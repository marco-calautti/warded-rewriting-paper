package org.unimi;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.lang.ProcessBuilder.Redirect;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.security.AlgorithmParameterGenerator;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.queryrewriting.caching.CacheManager;
import org.semanticweb.rulewerk.core.model.api.PositiveLiteral; 
import org.semanticweb.rulewerk.core.reasoner.KnowledgeBase;
import org.semanticweb.rulewerk.parser.ParsingException;
import org.semanticweb.rulewerk.parser.RuleParser;
import org.semanticweb.rulewerk.reasoner.vlog.VLogReasoner;

import fr.boreal.forward_chaining.chase.Chase;
import fr.boreal.forward_chaining.chase.ChaseBuilder;
import fr.boreal.forward_chaining.chase.halting_condition.HaltingCondition;
import fr.boreal.forward_chaining.chase.halting_condition.Timeout;
import fr.boreal.io.csv.CSVLoader;
import fr.boreal.io.csv.CSVParser;
import fr.boreal.io.csv.RLSCSVParser;
import fr.boreal.io.csv.RLSCSVsParser;
import fr.boreal.io.dlgp.DlgpParser;
import fr.boreal.model.kb.api.FactBase;
import fr.boreal.model.kb.impl.RuleBaseImpl;
import fr.boreal.storage.builder.StorageBuilder;
import fr.boreal.model.logicalElements.api.Atom;
import fr.boreal.model.logicalElements.api.Substitution;
import fr.boreal.model.query.api.FOQuery;
import fr.boreal.model.query.factory.FOQueryFactory;
import fr.boreal.model.queryEvaluation.api.FOQueryEvaluator;
import fr.boreal.model.rule.api.FORule;
import fr.boreal.query_evaluation.generic.GenericFOQueryEvaluator;
import fr.boreal.model.kb.api.RuleBase;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.lang3.time.StopWatch;
import org.apache.commons.lang3.tuple.Pair;
import org.apache.logging.log4j.core.util.SystemClock;

public class App 
{
    public static void main( String[] args )
    {
        if(args.length != 4){
            System.out.println("Usage: <reasoner (vlog/dlv/dlvExists/integraal)> <dtg file> <annotations file> <timeout in seconds>");
            return;
        }

        try{

            String reasonerType = args[0];

            if( !reasonerType.equals("dlv") && 
                !reasonerType.equals("vlog") &&
                !reasonerType.equals("dlvExists") &&
                !reasonerType.equals("integraal")){
                System.err.println("Unknown reasoner "+reasonerType);
                System.exit(-1);
            }

            Integer timeout = Integer.parseInt(args[3]);
            if(timeout == 0){
                timeout = null;
            } 

            // Setup caching. Needed by the rule parser and rule syntax system in general.
            CacheManager.setupCaching();

            String program = loadFile(args[1]);
            String annotationsString = loadFile(args[2]);

            BasicRuleParser ruleParser = new BasicRuleParser();
            AnnotationsParser annotationsParser = new AnnotationsParser();

            ruleParser.parse(program);
            annotationsParser.parse(annotationsString);

            // get only the rules
            List<IRule> rules = ruleParser.getRules();

            List<Annotation> inputAnnotations = annotationsParser.getInputAnnotations();
            List<Annotation> tempOut = annotationsParser.getOutputAnnotations();

            List<Annotation> outputAnnotations = new ArrayList<>();

            for(Annotation outAn : tempOut){
                for(IRule r :rules){
                    IPredicate p = r.getHeadPredicates().iterator().next();
                    if(p.getPredicateSymbol().equals(outAn.getPredicate().getPredicateSymbol())){
                        if(!outputAnnotations.contains(outAn))
                            outputAnnotations.add(new Annotation(p, outAn.getCsvPath(), outAn.getType()));
                    }
                }
            }

            switch(reasonerType){
                case "vlog":
                    reasonVLog(rules, inputAnnotations, outputAnnotations, timeout);
                break;
                case "dlv":
                    reasonDLV(rules, inputAnnotations, outputAnnotations, timeout);
                break;
                case "dlvExists":
                    reasonDLVEx(rules, inputAnnotations, outputAnnotations, timeout);
                break;
                case "integraal":
                    reasonInteGraal(rules, inputAnnotations, outputAnnotations, timeout);
                break;
                default:
                    throw new Exception("Unknown reasoner "+reasonerType);
            }

        }catch(Exception e){
            writeResult("EXCEPTION", 0);
        }
    }

    private static void reasonDLV(List<IRule> rules, List<Annotation> inputAnnotations,
            List<Annotation> outputAnnotations, Integer timeout) throws IOException{
        
        reasonDLVInternal(rules, inputAnnotations, outputAnnotations, timeout, false);
    }

    private static void reasonDLVEx(List<IRule> rules, List<Annotation> inputAnnotations,
            List<Annotation> outputAnnotations, Integer timeout) throws IOException{

        reasonDLVInternal(rules, inputAnnotations, outputAnnotations, timeout, true);
    }

    private static void reasonDLVInternal(List<IRule> rules, List<Annotation> inputAnnotations,
            List<Annotation> outputAnnotations, Integer timeout, boolean isEx) throws IOException{

        String dlvBinaryPath = "";
        try{
            Path dlvBinaryBasePath = Paths.get(App.class.getProtectionDomain().getCodeSource().getLocation()
            .toURI());
            String dlvBin = isEx? "dlvExists" : "dlv";
            dlvBinaryPath = Paths.get(dlvBinaryBasePath.getParent().toString(),dlvBin).toString();

        }catch(Exception e ){}

        String dlvRules = createDLVRules(rules, isEx);
        String dlvRulesPath = Files.createTempFile("dlv_rules",".asp").toString();
        try(BufferedWriter bw = new BufferedWriter(new FileWriter(dlvRulesPath))){
            bw.write(dlvRules);
        }

        
        List<String> factsFiles = createFactsFiles(inputAnnotations);

        List<Pair<List<String>,String>> commands = createDLVCommands(dlvBinaryPath,dlvRulesPath,factsFiles,outputAnnotations, isEx);
        
        long start = System.currentTimeMillis();

        for(Pair<List<String>,String> entry : commands){

            List<String> command = entry.getLeft();
            String outputPath = entry.getRight();

            ProcessBuilder dlvProcessBuilder = new ProcessBuilder(command);
            if(outputPath != null){
                dlvProcessBuilder.redirectOutput(new File(outputPath));
            }else{
                dlvProcessBuilder.redirectOutput(Redirect.DISCARD);
            }
                
            Process process = dlvProcessBuilder.start();

            try{
                if(!process.waitFor(timeout, TimeUnit.SECONDS)){
                    long elapsed = System.currentTimeMillis() - start;
                    process.destroy();
                    writeResult("TIMEOUT", elapsed);
                    return;
                }
            }catch(InterruptedException e){
                long elapsed = System.currentTimeMillis() - start;
                writeResult("INTERRUPTED", elapsed);
                return;
            }

            long elapsed = System.currentTimeMillis() - start;
            if(elapsed > timeout*1000){
                writeResult("TIMEOUT", elapsed);
                return;
            }
        }

        long elapsed = System.currentTimeMillis() - start;
        writeResult("SUCCESS", elapsed);
    }

    private static List<Pair<List<String>,String>> createDLVCommands(String dlvBinaryPath, String dlvRulesPath, List<String> factsFiles,
            List<Annotation> outputAnnotations, boolean isEx) throws IOException{
        

        List<Pair<List<String>,String>> allCommands = new ArrayList<>();

        if(!isEx){
            List<String> command = new ArrayList<>();
        
            String outputPath = 
                outputAnnotations.isEmpty()? null : Paths.get(new File(outputAnnotations.get(0).getCsvPath()).getParent(),"dlv_out.facts").toString();

            String outputPreds = outputAnnotations.stream().map(
                a -> a.getPredicate().getPredicateSymbol()
            ).collect(Collectors.joining(","));
            
            
            command.add(dlvBinaryPath);
            if(!outputPreds.isEmpty()){
                command.add("-pfilter="+outputPreds);
            }
            command.add(dlvRulesPath);
            command.addAll(factsFiles);

            allCommands.add(Pair.of(command,outputPath)); 
        }else{
            for(Annotation ann : outputAnnotations){
                List<String> command = new ArrayList<>();

                String predName = ann.getPredicate().getPredicateSymbol();
                int predArity = ann.getPredicate().getArity();

                Path outputPath = 
                    Paths.get(new File(ann.getCsvPath()).getParent(),"dlv_"+predName+".facts");
                
                String dlvQueryPath = Files.createTempFile("dlv_query_"+predName,".asp").toString();
                try(BufferedWriter bw = new BufferedWriter(new FileWriter(dlvQueryPath))){

                    bw.append(predName);
                    bw.append('(');

                    String varTuple = 
                        IntStream.range(0, predArity).mapToObj(i -> "V"+i).collect(Collectors.joining(","));

                    bw.append(varTuple);
                    bw.append(")?\n");
                }
                command.add(dlvBinaryPath);
                command.add(dlvRulesPath);
                command.addAll(factsFiles);
                command.add(dlvQueryPath);
                command.add("-cautious");

                allCommands.add(Pair.of(command,outputPath.toString())); 
            }
        }

        return allCommands;
    }

    private static void reasonVLog(List<IRule> rules, List<Annotation> inputAnnotations,
            List<Annotation> outputAnnotations, Integer timeout) throws ParsingException, IOException {
        
        String vlogAnnotations = createVLogAnnotations(inputAnnotations);

        String vlogRules = createVLogRules(rules);

        String kbString = vlogAnnotations+vlogRules;
        KnowledgeBase kb = RuleParser.parse(kbString);
        
        try (VLogReasoner reasoner = new VLogReasoner(kb)) {
            if(!reasoner.isMFA()){
                writeResult("NONTERMINATING",0);
            }

            long start = System.currentTimeMillis();
            reasoner.setAlgorithm(org.semanticweb.rulewerk.core.reasoner.Algorithm.RESTRICTED_CHASE);
            reasoner.setReasoningTimeout(timeout);

            boolean allFinished = reasoner.reason();
            if(allFinished){
                for(Annotation outAnnotation : outputAnnotations){
                    String outPred = outAnnotation.getPredicate().getPredicateSymbol();
                    int predArity = outAnnotation.getPredicate().getArity();
                    String csvPath = outAnnotation.getCsvPath();

                    PositiveLiteral query = buildQuery(outPred, predArity);
                    
                    reasoner.exportQueryAnswersToCsv(query,csvPath,false);
                }
            }

            long elapsed = System.currentTimeMillis() - start;

            if(allFinished){
                writeResult("SUCCESS", elapsed);
            }else{
                writeResult("TIMEOUT", elapsed);
            }
        }
    }

    private static String createVLogRules(List<IRule> rules) {
        StringBuilder sb = new StringBuilder();

        for(IRule rule : rules){
            Set<IVariable> exVars = rule.getExistentialVariables();

            IAtom headAtom = rule.getHead().iterator().next().getAtom();
            sb  .append(headAtom.getPredicate().getPredicateSymbol())
                .append('(');

            String headAtomVariables = 
                headAtom.getTuple().stream().map(
                    variable -> {
                        if(exVars.contains(variable))
                            return "!"+variable.getValue();
                        else
                            return "?"+variable.getValue();
                    }).collect(Collectors.joining(","));
                
            sb.append(headAtomVariables);
            sb.append(") :- ");

            String body =
                rule.getBody().stream().map(
                    lit -> lit.getAtom().toString()
                ).collect(Collectors.joining(","));

            sb.append(body);
            sb.append(".\n");
        }

        return sb.toString();
    }

    private static PositiveLiteral buildQuery(String outPred, int predArity) throws ParsingException{
        StringBuilder sb = new StringBuilder();

        sb.append(outPred).append('(');

        String varTuple = 
            IntStream.range(0, predArity).mapToObj(i -> "?V"+i).collect(Collectors.joining(","));

        sb.append(varTuple);
        sb.append(')');

        return RuleParser.parsePositiveLiteral(sb.toString());
    }

    private static String createVLogAnnotations(List<Annotation> annotations){
        StringBuilder sb = new StringBuilder();

        for(Annotation a : annotations){
            sb  .append("@source ")
                .append(a.getPredicate().getPredicateSymbol())
                .append('[')
                .append(a.getPredicate().getArity())
                .append("] : load-csv('")
                .append(a.getCsvPath())
                .append("').\n");
        }
        return sb.toString();
    }

    private static String createDLVRules(List<IRule> rules, boolean isEx){
        StringBuilder sb = new StringBuilder();

        int skolemId = 0;
        for(IRule rule : rules){
            Set<IVariable> exVars = rule.getExistentialVariables();

            if(isEx){
                if(!exVars.isEmpty()){
                    sb.append("#exists{");
                    sb.append(
                        exVars.stream().map(v -> v.getValue().toString()).collect(Collectors.joining(",")));
                    sb.append('}');
                }

                IAtom headAtom = rule.getHead().iterator().next().getAtom();

                sb  .append(headAtom.getPredicate().getPredicateSymbol())
                    .append('(');

                String headTuple = headAtom.getTuple().stream().map(
                    v -> v.getValue().toString()
                ).collect(Collectors.joining(","));

                sb.append(headTuple);
                sb.append(") :- ");
            }else{
                String skolemTerms = rule.getFrontierVariables().stream().map(
                    fVar -> fVar.getValue()
                ).collect(Collectors.joining(","));

                Map<IVariable,String> skolems = new HashMap<>();
                
                for(IVariable ex : exVars){
                    StringBuilder sbEx = new StringBuilder();
                    sbEx    .append('f').append(skolemId).append('(')
                            .append(skolemTerms)
                            .append(')');
                    
                    skolems.put(ex,sbEx.toString());
                    skolemId++;
                }

                IAtom headAtom = rule.getHead().iterator().next().getAtom();

                sb  .append(headAtom.getPredicate().getPredicateSymbol())
                    .append('(');

                String headTuple = headAtom.getTuple().stream().map(
                    variable -> {
                        if(exVars.contains(variable))
                            return skolems.get((IVariable)variable);
                        else
                            return variable.getValue().toString();
                    }
                ).collect(Collectors.joining(","));

                sb.append(headTuple);
                sb.append(") :- ");
            }

            String ruleBody = rule.getBody().stream().map(
                lit -> {
                    IAtom bodyAtom = lit.getAtom();

                    String bodyTuple = bodyAtom.getTuple().stream().map(
                        v-> v.getValue().toString()
                    ).collect(Collectors.joining(","));
                    
                    return bodyAtom.getPredicate().getPredicateSymbol() + "(" + bodyTuple + ")";
                }
            ).collect(Collectors.joining(","));

            sb.append(ruleBody);
            sb.append(".\n");
        }

        return sb.toString();
    }

    private static List<String> createFactsFiles(List<Annotation> inputAnnotations) throws IOException{
        List<String> result = new ArrayList<>();

        for(Annotation a : inputAnnotations){
            String csvPath = a.getCsvPath();
            String pred = a.getPredicate().getPredicateSymbol();

            String factsFile = FilenameUtils.removeExtension(csvPath)+".facts";
            result.add(factsFile);

            try(BufferedReader br = new BufferedReader(new FileReader(csvPath))){
                try(PrintWriter pw = new PrintWriter(new BufferedWriter(new FileWriter(factsFile)))){
                    String line = br.readLine();
                    while(line != null){
                        line = line.strip();
                        if(!line.isEmpty()){
                            pw.print(pred);
                            pw.print("(");
                            pw.print(line);
                            pw.println(").");
                        }
                        line = br.readLine();
                    }
                }
            }
        }

        return result;
    }

    private static void writeResult(String status, long elapsed) {
        System.out.println(status+" "+elapsed);
    }
    
    private static final String loadFile(final String filename) throws IOException {
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

    private static void reasonInteGraal(List<IRule> rules, List<Annotation> inputAnnotations,
    List<Annotation> outputAnnotations, Integer timeout) throws Exception{

        timeout = timeout * 1000;
        
        RuleBase ruleBase = null;

        try(DlgpParser rulesParser = new DlgpParser(createInteGraalRules(rules))){
            ruleBase = new RuleBaseImpl(rulesParser.parse().rules());        
        }

        FactBase fb = StorageBuilder.getSimpleInMemoryGraphStore();

        for(Annotation an : inputAnnotations){
            String csvPath = an.getCsvPath();
            String predName = an.getPredicate().getPredicateSymbol();
            int arity = an.getPredicate().getArity();

            try(CSVParser parser = new CSVParser(predName,arity,new File(csvPath))){
                fb.addAll(parser.parse().atoms());
            }
        }
        
        String queriesString = outputAnnotations.stream().map(
            an -> { 
                String predName = an.getPredicate().getPredicateSymbol();
                int arity = an.getPredicate().getArity();
                String varTuple = "(" +
                    IntStream.range(0, arity).mapToObj(i -> "V"+i).collect(Collectors.joining(","))
                    + ")";
                return "?"+varTuple+" :- "+predName+varTuple+".";

        }).collect(Collectors.joining("\n"));
            
        Collection<FOQuery> queries = null;
        try(DlgpParser parser = new DlgpParser(queriesString)){
            queries = parser.parse().queries();  
        }

        List<String> outputPaths = outputAnnotations.stream().map(
            an -> {
                return Paths.get(new File(an.getCsvPath()).getParent(),
                        "integraal_"+an.getPredicate().getPredicateSymbol()+".ans").toString();
            }
        ).collect(Collectors.toList());

        var timeoutChecker = new ChaseTimeoutCondition(timeout);
        
        var chase = ChaseBuilder.defaultBuilder(fb, ruleBase)
            .useRestrictedChecker()
            .useGRDRuleScheduler()
            .useSemiNaiveComputer()
            .useDirectApplication()
            .addStandardHaltingConditions()
            .addHaltingConditions(timeoutChecker)
            .build().get();

        chase.execute();


        if(timeoutChecker.timeExpired()){
            writeResult("TIMEOUT", timeout);
            return;
        }

        FOQueryEvaluator<FOQuery> evaluator = GenericFOQueryEvaluator.defaultInstance();
        Iterator<String> anIt = outputPaths.iterator();
        for(FOQuery query : queries){
            String outPath = anIt.next();
                
            Iterator<Substitution> res = evaluator.evaluate(query, fb);
            if(timeoutChecker.timeExpired()){
                writeResult("TIMEOUT", timeout);
                return;
            }

            try(PrintWriter pw = new PrintWriter(new BufferedWriter(new FileWriter(outPath)))){
                while(res.hasNext()){
                    pw.println(res.next());
                }
            }

            if(timeoutChecker.timeExpired()){
                writeResult("TIMEOUT", timeout);
                return;
            }
        } 

        writeResult("SUCCESS", timeoutChecker.timeElapsed());
    }

    private static String createInteGraalRules(List<IRule> rules){
        StringBuilder sb = new StringBuilder();

        for(IRule rule : rules){

            IAtom headAtom = rule.getHead().iterator().next().getAtom();

            sb  .append(headAtom.getPredicate().getPredicateSymbol())
                .append('(');

            String headTuple = headAtom.getTuple().stream().map(
                variable -> {
                        return variable.getValue().toString();
                }
            ).collect(Collectors.joining(","));

            sb.append(headTuple);
            sb.append(") :- ");
            

            String ruleBody = rule.getBody().stream().map(
                lit -> {
                    IAtom bodyAtom = lit.getAtom();

                    String bodyTuple = bodyAtom.getTuple().stream().map(
                        v-> v.getValue().toString()
                    ).collect(Collectors.joining(","));
                    
                    return bodyAtom.getPredicate().getPredicateSymbol() + "(" + bodyTuple + ")";
                }
            ).collect(Collectors.joining(","));

            sb.append(ruleBody);
            sb.append(".\n");
        }

        return sb.toString();
    }
}

class ChaseTimeoutCondition implements HaltingCondition{

    private long timeout;
    private long start;

    public ChaseTimeoutCondition(long timeout){
        this.timeout = timeout;
    }

    @Override
    public void init(Chase c) {
        start = System.currentTimeMillis();
    }

    @Override
    public boolean check() {
        return timeout > (System.currentTimeMillis()-start);
    }

    public boolean timeExpired(){
        return timeout < (System.currentTimeMillis()-start);
    }

    public long timeElapsed(){
        return System.currentTimeMillis()-start;
    }
}
