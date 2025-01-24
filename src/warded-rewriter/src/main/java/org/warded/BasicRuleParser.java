package org.warded;

import java.io.IOException;
import java.io.StreamTokenizer;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.deri.iris.factory.Factory.BASIC;
import static org.deri.iris.factory.Factory.TERM;

import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IQuery;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.queryrewriting.NormalizationUtils;

import com.google.common.collect.ImmutableList;

public class BasicRuleParser {
    
    private final static char POPEN = '(', PCLOSE = ')', QMARK = '?', COMMA = ',', COLON = ':', DASH = '-', DOT = '.', BSLASH = '/', DIRECTIVE = '@'; 
    
    private final static String EDB_DIRECTIVE = "edb";

    private Set<IRule> curProgram;
    private List<IQuery> curQueries;
    private Set<String> edbPredicates;

    private int auxCounter = 0;

    private static enum RuleState {
        HEAD,
        BODY
    }

    private static enum State {
        DIRECTIVE_BEGIN,
        DIRECTIVE_END,
        EDB_DIRECTIVE_BEGIN,
        RULE_BEGIN,
        COMMA_RULE_END,
        ATOM_PRED,
        COMMA_RULE_SEP,
        RULE_SEP,
        RULE_SEP_END,
        OPEN_PAR,
        VAR_BEGIN,
        VAR_NAME,
        NEXT_VAR_ATOM_END,
        QUERY_SEP_END
    }

    public void parse(String program) throws IOException{
        auxCounter = 0;

        StreamTokenizer tok = new StreamTokenizer(new StringReader(program));

        tok.wordChars('a', 'z');
        tok.wordChars('A', 'Z');
        tok.wordChars('0', '9');
        tok.wordChars('_','_');
        
        tok.ordinaryChar(POPEN);
        tok.ordinaryChar(PCLOSE);
        tok.ordinaryChar(QMARK);
        tok.ordinaryChar(COMMA);
        tok.ordinaryChar(COLON);
        tok.ordinaryChar(DASH);
        tok.ordinaryChar(DOT);
        tok.ordinaryChar(BSLASH);
        tok.ordinaryChar(DIRECTIVE);
        tok.eolIsSignificant(false);
        tok.slashSlashComments(true);

        State state = State.RULE_BEGIN;
        RuleState rState = RuleState.HEAD;
        
        int token = tok.nextToken();
        
        String curPredStr = null;
        List<ITerm> curAtomTerms = null;
        List<ILiteral> curHead = new ArrayList<>();
        List<ILiteral> curBody = new ArrayList<>();
        curProgram = new HashSet<>();
        curQueries = new ArrayList<>();
        edbPredicates = new HashSet<>();

        while(token != StreamTokenizer.TT_EOF){
            switch(state){                    
                case RULE_BEGIN:
                    if(tok.ttype == DIRECTIVE){
                        state = State.DIRECTIVE_BEGIN;
                    } else if(tok.ttype == QMARK){
                        state = State.QUERY_SEP_END;
                    } else if(tok.ttype == StreamTokenizer.TT_WORD){
                        curPredStr = tok.sval;
                        state = State.OPEN_PAR;
                    } else {
                        throw new IOException("Syntax error in line "+tok.lineno());
                    } 
                break;

                case DIRECTIVE_BEGIN:
                    if(tok.ttype == StreamTokenizer.TT_WORD){
                        if(tok.sval.equals(EDB_DIRECTIVE)){
                            state = State.EDB_DIRECTIVE_BEGIN;
                        }else{
                            throw new IOException("Syntax error in line "+tok.lineno());
                        }
                    }else{
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }
                break;

                case EDB_DIRECTIVE_BEGIN:
                    if(tok.ttype == StreamTokenizer.TT_WORD){
                        edbPredicates.add(tok.sval);
                        state = State.DIRECTIVE_END;
                    }else{
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }
                break;

                case DIRECTIVE_END:
                    if(tok.ttype == DOT){
                        state = State.RULE_BEGIN;
                    }else{
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }
                break;

                case ATOM_PRED:
                    if(tok.ttype == StreamTokenizer.TT_WORD){
                        curPredStr = tok.sval;
                        state = State.OPEN_PAR;
                    } else {
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    
                break;

                case COMMA_RULE_SEP:
                    if(tok.ttype == COMMA){
                        state = State.ATOM_PRED;
                    }else if (tok.ttype == COLON){
                        state = State.RULE_SEP_END;
                    }else {
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    
                break;

                case RULE_SEP:
                    if (tok.ttype == COLON){
                        state = State.RULE_SEP_END;
                    }else {
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    
                break;
                case COMMA_RULE_END:
                    if(tok.ttype == COMMA){
                        state = State.ATOM_PRED;
                    }else if (tok.ttype == DOT && rState == RuleState.BODY){
                        if(curHead.size() == 0){
                            IQuery query = BASIC.createQuery(new ArrayList<>(NormalizationUtils.canonicalRenaming(curBody,"U")));
                            curQueries.add(query);
                            curBody = new ArrayList<>();

                        }else{
                            IRule rule = NormalizationUtils.canonicalRenaming(BASIC.createRule(curHead, curBody),"U");
                            if(rule.getHead().size() == 1){
                                curProgram.add(rule);
                            }else{
                                curProgram.addAll(normalizeRule(rule));
                            }
                            
                            curHead = new ArrayList<>();
                            curBody = new ArrayList<>();
                        }
                        
                        rState = RuleState.HEAD;
                        state = State.RULE_BEGIN;
                        
                    }else {
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    
                break;

                case RULE_SEP_END:
                    if(tok.ttype == DASH){
                        rState = RuleState.BODY;
                        state = State.ATOM_PRED;
                    }else {
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    
                break;

                case OPEN_PAR:
                    if(tok.ttype != POPEN){
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    state = State.VAR_BEGIN;
                    curAtomTerms = new ArrayList<>();
                break;

                case VAR_BEGIN:
                    if(tok.ttype != QMARK){
                        throw new IOException("Syntax error in line "+tok.lineno()+". Expected ?");
                    }

                    state = State.VAR_NAME;
                break;

                case VAR_NAME:
                    if(tok.ttype != StreamTokenizer.TT_WORD){
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                    
                    curAtomTerms.add(TERM.createVariable(tok.sval));
                    state = State.NEXT_VAR_ATOM_END;
                break;

                case NEXT_VAR_ATOM_END:
                    if(tok.ttype == COMMA ){
                        state = State.VAR_BEGIN;
                    }else if(tok.ttype == PCLOSE){
                        IPredicate predicate = BASIC.createPredicate(curPredStr, curAtomTerms.size());
                        ITuple tuple = BASIC.createTuple(curAtomTerms);
                        ILiteral atom = BASIC.createLiteral(true, predicate, tuple);

                        if(rState == RuleState.HEAD){
                            curHead.add(atom);
                            state = State.COMMA_RULE_SEP;
                        }else{
                            curBody.add(atom);
                            state = State.COMMA_RULE_END;

                        }
                    }else{
                        throw new IOException("Syntax error in line "+tok.lineno());
                    }

                break;

                case QUERY_SEP_END:
                    if(tok.ttype == DASH){
                        state = State.ATOM_PRED;
                        rState = RuleState.BODY;
                    }
                break;
            }

            token = tok.nextToken();
        }
            
    }

    public List<IRule> getRules() {
        return new ArrayList<>(curProgram);
    }

    public List<IQuery> getQueries() {
        return curQueries;
    }

    public Set<String> getEDBPredicates(){
        return edbPredicates;
    }
    
    private List<IRule> normalizeRule(IRule rule){
        assert(rule.getHead().size() > 1);

        List<IRule> normalized = new ArrayList<>();

        // Multiple head atoms
        final Set<IVariable> exVars = rule.getExistentialVariables();
        if (exVars.isEmpty()) {
            // No existential variables --> safe to split
            final Set<ILiteral> head = rule.getHead();
            for (final ILiteral headLit : head) {
                normalized.add(BASIC.createRule(ImmutableList.of(headLit), rule.getBody()));
            }
        } else {
            // Need to use auxiliary predicate
            Set<IVariable> allRuleVars = rule.getHeadVariables();
            List<ITerm> allRuleTerms = allRuleVars.stream().map(a -> (ITerm)a).toList();

            IPredicate auxPred = BASIC.createPredicate("Aux"+auxCounter, allRuleVars.size());
            ITuple auxTuple = BASIC.createTuple(allRuleTerms);
            ILiteral auxAtom = BASIC.createLiteral(true,auxPred, auxTuple);

            // Now create the auxiliary rule, and one rule for each head atom
            IRule auxRule = BASIC.createRule(ImmutableList.of(auxAtom), rule.getBody());
            normalized.add(auxRule);

            for(ILiteral headLit : rule.getHead()){
                normalized.add(BASIC.createRule(ImmutableList.of(headLit),ImmutableList.of(auxAtom)));
            }

            auxCounter++;
        }

        return normalized;
    }
}
