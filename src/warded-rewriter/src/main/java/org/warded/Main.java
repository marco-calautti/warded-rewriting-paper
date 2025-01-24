package org.warded;

import org.apache.commons.io.FilenameUtils;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPosition;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IQuery;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.factory.IBasicFactory;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.basics.BasicFactory;
import org.deri.iris.queryrewriting.QueryRewriter;
import org.deri.iris.queryrewriting.RewritingUtils;
import org.deri.iris.queryrewriting.caching.CacheManager;
import org.deri.iris.utils.UniqueList;

import com.google.common.collect.Sets;

public class Main {

    public static void main(String[] args) throws IOException {

        if ((args.length != 1 && args.length != 2) || (args.length==2 && !args[1].equals("--bulk") && !args[1].equals("--check"))) {
            System.out.println("Usage: <programfile> [--bulk, --check]");
            System.exit(0);
        }

        String program = null;

        PrintWriter myWriter = new PrintWriter(System.out);

        // Setup caching
        CacheManager.setupCaching();
        try {

            long startTime = System.currentTimeMillis();

            String baseName = FilenameUtils.getBaseName(args[0]);
            String basePath = FilenameUtils.getFullPath(args[0]);

            program = loadFileFast(args[0]);

            // final Parser parser = new Parser();
            final BasicRuleParser parser = new BasicRuleParser();

            // Parse the program
            parser.parse(program);

            final List<IRule> rules = parser.getRules();

            // Get the queries in the program: A query has the form ?- body.
            final List<IQuery> queries = parser.getQueries();
            // the queries are the queries that are asked to the program ([?- Q1(?A)) form

            List<IRule> mTGDs = RewritingUtils.getTGDs(rules, queries);
            // mTGDs are the (rules - queries(head:-body))

            Set<IPosition> affectedPositions = computeAffectedPositions(mTGDs);
            Map<IPredicate,Set<IRule>> rulesByHeadPred = computeRulesByHeadPredicate(mTGDs);
            Set<String> edbPredicates = parser.getEDBPredicates();

            // Convert the query bodies in rules
            // the AllQueries represent the queries (head:-body)form
            final List<IRule> AllQueries = new LinkedList<IRule>(rules);
            AllQueries.removeAll(mTGDs);

            long preprocessingElapsed = System.currentTimeMillis() - startTime;

            System.out.println("Preprocessing time (ms): "+ preprocessingElapsed);
            if(args.length == 1){
                for (IQuery query : queries) {

                    // Get the rule corresponding to the query
                    final IRule ruleQuery = getRuleQuery(query, AllQueries);

                    QueryRewriter rewriter = new DecompositionFORewriter(ruleQuery,mTGDs,rulesByHeadPred,affectedPositions,edbPredicates);

                    rewriteAndSaveStats(rewriter,preprocessingElapsed,baseName,basePath,ruleQuery);
                }
            // bulk rewrite
            }else if(args[1].equals("--bulk")){
                List<IRule> queryBatch = queries.stream().map(q -> getRuleQuery(q, AllQueries)).toList();
                
                QueryRewriter rewriter = new DecompositionFORewriter(queryBatch,mTGDs,rulesByHeadPred,affectedPositions,edbPredicates);

                rewriteAndSaveStats(rewriter, preprocessingElapsed, baseName, basePath, null);
            // only check if the ontology is warded
            }else if(args[1].equals("--check")){
                IRule rule = isWarded(mTGDs, affectedPositions);
                System.out.println("Warded: " + (rule == null ? "yes" : "no, because of "+rule));
            }
            
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            myWriter.close();
        }

    }

    private static final void rewriteAndSaveStats(
        QueryRewriter rewriter, 
        long preprocessingElapsed,
        String baseName,
        String basePath,
        IRule ruleQuery) throws IOException{

        long startTime = System.currentTimeMillis();

        Set<IRule> rewritten = rewriter.rewrite();

        long elapsed = System.currentTimeMillis() - startTime;

        int rewSize = rewritten.size();
        
        int min =   rewritten.stream().
                    min((a,b) -> a.getBody().size() - b.getBody().size()).
                    map((a) ->  a.getBody().size()).orElse(0);

        int max =   rewritten.stream().
                    max((a,b) -> a.getBody().size() - b.getBody().size()).
                    map((a) -> a.getBody().size()).orElse(0);

        String queryPred = "bulk";
        if(ruleQuery != null){
            queryPred = ruleQuery.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol();
        }

        System.out.println("Query name: "+queryPred);
        System.out.println("Rewriting size: " + rewSize);
        System.out.println("Minimum rule size: " + min);
        System.out.println("Maximum rule size: " + max);
        System.out.println("Rewriting time (ms): " + elapsed);        

        try(PrintWriter pw = 
            new PrintWriter(
                new BufferedWriter(
                    new FileWriter(
                        Path.of(basePath, baseName+"_"+queryPred+".dtg").toFile())))){

            for(IRule rule : rewritten){
                pw.println(rule);
            }
        }

        try(PrintWriter pw = 
            new PrintWriter(
                new BufferedWriter(
                    new FileWriter(
                        Path.of(basePath, baseName+"_"+queryPred+".vada").toFile())))){

            for(IRule rule : rewritten){
                pw.println(rule.toString().replaceAll("\\?", ""));
            }
        }
    }
    
    private static final String loadFileFast(final String filename) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(filename));

        final StringBuilder builder = new StringBuilder();

        String line = br.readLine();
        while (line != null) {
            builder.append(line);
            builder.append('\n');
            line = br.readLine();
        }
        br.close();
        return builder.toString();
    }

    private static IRule getRuleQuery(final IQuery query, List<IRule> queries) {

        final IBasicFactory bf = BasicFactory.getInstance();

        for (final IRule r : queries) {

            if (r.getHead().contains(query.getLiterals().get(0))) {
                return r;
                // return bf.createRule(new UniqueList<ILiteral>(), query.getLiterals());
            }

        }
        // Return a Boolean Conjunctive Query (BCQ)
        return bf.createRule(new UniqueList<ILiteral>(), query.getLiterals());
    }

    private static Set<IPosition> computeAffectedPositions(final List<IRule> tgds) {
    
        final Set<IPosition> exPosSet = new HashSet<IPosition>();

        // get all declared existential positions in the set of TGDs (initial marking)

        for (final IRule tgd : tgds) {
            final Set<IPosition> exPossInTGD = tgd.getExistentialPositions();
            exPosSet.addAll(exPossInTGD);
        }

        Set<IPosition> newAffectedPos = new HashSet<>();

        do {

            exPosSet.addAll(newAffectedPos);
            newAffectedPos.clear();

            for(IRule r : tgds){
                final Set<IVariable> fVars = r.getFrontierVariables();

                for (final IVariable v : fVars) {
                    final Set<IPosition> bodyPos = r.getTermBodyPositions(v);

                    // All positions in which v occurs are affected -> all positions in head where v occurs 
                    // are affected
                    if(exPosSet.containsAll(bodyPos)){
                        final Set<IPosition> headPos = r.getTermHeadPositions(v);
                        // add only the new affected positions
                        newAffectedPos.addAll(Sets.difference(headPos, exPosSet));
                    }
                }
            }

        }while(!newAffectedPos.isEmpty());
        

        return exPosSet;
    }

    // returns null if it is warded, otherwise, it returns the rule that violates wardedness
    private static IRule isWarded(List<IRule> rules, Set<IPosition> affectedPos) {

        for(IRule rule: rules) {
            Set<IVariable> harmful = new HashSet<>();
            Set<IVariable> harmless = new HashSet<>();
            Set<IVariable> dangerous = new HashSet<>();

            for(IVariable variable: rule.getBodyVariables()) {
                boolean isHarmful = false;
                if(affectedPos.containsAll(rule.getBodyPositions(Collections.singleton(variable)))) {
                    harmful.add(variable);
                    isHarmful = true;
                }else{
                    harmless.add(variable);
                }

                if(isHarmful && rule.getHeadVariables().contains(variable)) {
                    dangerous.add(variable);
                }
            }

            // find the ward
            ILiteral[] bodyLiterals = rule.getBody().toArray(new ILiteral[0]);

            boolean ruleHasWard = false;
            for(int i = 0; i < bodyLiterals.length; i++){

                IAtom bodyAtom = bodyLiterals[i].getAtom();
                ITuple bodyTuple = bodyAtom.getTuple();

                if(bodyTuple.containsAll(dangerous)){     

                    boolean isWard = true;
                    not_ward:
                    for(ITerm t: bodyTuple){
                        IVariable v = (IVariable)t;

                        if(harmful.contains(v)){
                            for(int j = 0; j < bodyLiterals.length; j++){
                                if(i == j) continue;
    
                                IAtom otherBodyAtom = bodyLiterals[j].getAtom();
                                ITuple otherBodyTuple = otherBodyAtom.getTuple();
                                
                                if(otherBodyTuple.contains(v)){
                                    isWard = false;
                                    break not_ward;
                                }
                            }

                        }
                    }

                    if(isWard) {
                        ruleHasWard = true;
                        break;
                    }
                }
            }

            if(!ruleHasWard) {
                return rule;
            }
        }

        return null;
    }
    private static Map<IPredicate, Set<IRule>> computeRulesByHeadPredicate(List<IRule> rules){
        Map<IPredicate, Set<IRule>> result = new HashMap<>();

        for(IRule r : rules){
            IPredicate headPred = r.getHeadPredicates().iterator().next();
            Set<IRule> predRules = result.get(headPred);
            if(predRules == null) {
                predRules = new HashSet<>();
                result.put(headPred,predRules);
            }
            predRules.add(r);
        }

        return result;
    }
}
