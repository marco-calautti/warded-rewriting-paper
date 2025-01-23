package org.unimi;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPosition;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.basics.Position;
import org.deri.iris.factory.Factory;
import org.deri.iris.queryrewriting.NormalizationUtils;
import org.deri.iris.queryrewriting.QueryGraph;
import org.deri.iris.queryrewriting.QueryRewriter;
import org.deri.iris.queryrewriting.RewritingUtils;
import org.deri.iris.queryrewriting.SetSizeComparator;
import org.deri.iris.utils.TermMatchingAndSubstitution;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

public class DecompositionFORewriter implements QueryRewriter {

    protected final Set<IRule> queries;
    protected final List<IRule> rules;
    protected final Set<String> edbPredicates;
    protected final Map<IPredicate,Set<IRule>> rulesByHeadPredicate;
    protected final Set<IPosition> affectedPos;

    @Override
    public Set<IRule> call() throws Exception {
        return rewrite();
    }

    public DecompositionFORewriter(final Collection<? extends IRule> queries, final List<IRule> rules, Map<IPredicate,Set<IRule>> rulesByHeadPred, Set<IPosition> affectedPositions, Set<String> edbPredicates) {
        this.queries = new HashSet<>(queries);
        this.rules = rules;
        this.edbPredicates = edbPredicates;
        this.affectedPos = affectedPositions;
        this.rulesByHeadPredicate = rulesByHeadPred;
    }

    public DecompositionFORewriter(final IRule query, final List<IRule> rules, Map<IPredicate,Set<IRule>> rulesByHeadPred, Set<IPosition> affectedPositions, Set<String> edbPredicates) {
        this(Sets.newHashSet(query),rules,rulesByHeadPred,affectedPositions,edbPredicates);
    }

    @Override
    public Set<IRule> rewrite() {

        final Map<IPredicate, QueryGraph> partialRewritings = new HashMap<>();

        final Set<IRule> exploredQueries = new HashSet<>();

        final Set<IRule> newQueries = Sets.newHashSet(
            queries.stream().map(q -> 
            NormalizationUtils.canonicalRenaming(q, "U")).collect(Collectors.toSet()));

        final Set<IRule> datalogRules = new HashSet<>();

        final Map<Component,IRule> builtComponents = new HashMap<>();

        final Set<IRule> excludedRulesFromFinalRewriting = new HashSet<>();

        for(IRule query : newQueries){
            addRuleToQueryGraph(query, partialRewritings);
        }

        // The temporary rewritings
        List<IRule> tempRew;

        do {
            tempRew = ImmutableList.copyOf(newQueries);
            newQueries.clear();

            for (final IRule qn : tempRew) {

                IPredicate qnPredicate = qn.getHead().iterator().next().getAtom().getPredicate();

                // avoid double exploration
                if (!exploredQueries.contains(qn)) {

                    Set<IRule> queryComponents = RewritingUtils.decomposeQuery(qn, affectedPos, rules);

                    // More than one component, which means we can add the reconciliation rule to the set of Datalog rules
                    // and add the components to the queue of queries to be rewritten

                    if (queryComponents.size() > 1) {

                        List<Component> baseComponents = queryComponents.stream().map( c ->  new Component(c)).toList();

                        // we do not need to use the current query in the final result, since we now build
                        // an equivalent Datalog version
                        excludedRulesFromFinalRewriting.add(qn);

                        // We must find whether some of the components in the body of the reconciliation rule
                        // can be replaced with a component we already built previously.
                        // This, for Warded rules guarantees termination, as in this case each component has a bound
                        // on the size of its body, so we will eventually start repeating components.

                        Set<IRule> adaptedComponents = new HashSet<>();
                        Set<IRule> reusedComponents = new HashSet<>();
                        Set<Component> newComponents = new HashSet<>();

                        for (Component comp : baseComponents) {
                            // Check whether we have already built a component which is
                            // is identical, but with a different predicate name in the head
                            Component alternativeComponent = findReusableComponent(comp, builtComponents);

                            // if this component is new, then keep it, and mark it as new component to be added
                            // later to the set of all built components
                            if (alternativeComponent == null){
                                adaptedComponents.add(comp.getQuery());
                                newComponents.add(comp);
                            // if this component is not new, use the alternative, equivalent one, and
                            // mark it as being reused for later.
                            } else {
                                adaptedComponents.add(alternativeComponent.getQuery());
                                reusedComponents.add(alternativeComponent.getQuery());
                            }
                        }

                        // update the set of all built components.
                        for(Component c : newComponents){
                            builtComponents.put(c,c.getCanonicalQuery());
                        }
                        

                        // Create reconciliation rule
                        IRule reconciliationRule = RewritingUtils.createReconciliationRule(qn, adaptedComponents);

                        // Do not add reconciliation rule and related components, if the reconciliation rule is trivial
                        if (!reconciliationRule.getBody()
                                .contains(reconciliationRule.getHead().iterator().next())) {

                            // add reconciliation rule to the set of Datalog rules
                            datalogRules.add(NormalizationUtils.canonicalRenaming(reconciliationRule, "U"));

                            // Add only the new components to the set of queries that need a rewriting.
                            // In particular, it a component is one which is reused, this has already been
                            // added to the queries to be processed in a previous iteration. Note that
                            // even if it has already been processed, it does not mean it is marked as explored,
                            // due to the subsumption check, that might remove it, in case it was subsumed.
                            // Nonetheless, it has been processed, in one way or another.
                            for (IRule comp : adaptedComponents) {
                                final IRule qRed = NormalizationUtils.canonicalRenaming(comp, "U");
                                if (!exploredQueries.contains(qRed) && !reusedComponents.contains(comp)) {
                                    addRuleToQueryGraph(qRed, partialRewritings);
                                    newQueries.add(qRed);
                                }
                            }
                        }

                        // We have processed qn, there is no need to do it again
                        exploredQueries.add(qn);

                    } else { // If we have only one component, we then exhaustively rewrite it with a one-step unification

                        for(IPredicate queryBodyPred : qn.getBodyPredicates()){
                            Set<IRule> headRules = rulesByHeadPredicate.get(queryBodyPred);
                            if(headRules == null){
                                continue;
                            }

                            for (IRule r : headRules) {

                                r = NormalizationUtils.canonicalRenaming(r, "V");
                                final IPredicate headPred = r.getHead().iterator().next().getAtom().getPredicate();

                                /*
                                * Check if the new query factorizes w.r.t the TGD r
                                */
                                final Set<IRule> factorizedQueries = new LinkedHashSet<IRule>();
                                factorizedQueries.add(qn);
                                if (r.getExistentialVariables().size() > 0 && qn.getBody().size() > 1 &&
                                        qn.getBodyPredicates().contains(headPred)) {

                                    factorizedQueries.addAll(factorisable(qn, r, exploredQueries));

                                }

                                /*
                                * Apply the TGDs until it is possible
                                */
                                for (final IRule qFact : factorizedQueries) {

                                    for (final ILiteral l : qFact.getBody()) {
                                        // get the atom a
                                        final IAtom a = l.getAtom();

                                        final Map<IVariable, ITerm> gamma = new HashMap<IVariable, ITerm>();

                                        // Check if the rule is applicable to the atom a
                                        if (RewritingUtils.isApplicable(r, qFact, a, gamma)) {

                                            // rewrite the atom a with the body of the rule sigma
                                            final IRule qrew = NormalizationUtils.canonicalRenaming(
                                                    RewritingUtils.rewrite(qFact, a, r.getBody(), gamma), "U");

                                            final IRule qRed = NormalizationUtils.canonicalRenaming(qrew, "U");

                                            // if this query has not be explored already. Try adding it
                                            if (!exploredQueries.contains(qRed)) {

                                                // Temporarily add this rewritten version of qn, and then check
                                                // if it is subsumed, in which case we remove it again, or
                                                // if eventually it subsumes others, we remove the others.
                                                addRuleToQueryGraph(qn, qRed, partialRewritings);

                                                // Checking subsumption
                                                if (!RewritingUtils.isSubsumed(
                                                        partialRewritings.get(qnPredicate),
                                                        qRed, exploredQueries, newQueries)) {
                                                    
                                                    // this rewritten version of qa is not subsumed, so it deserves to be
                                                    // processed at the next iteration.
                                                    newQueries.add(qRed);
                                                }

                                            }
                                            // If our current query qn has been removed, because it was subsumed by one of
                                            // its rewritten versions. There is no point in continuing with rewriting the current
                                            // factorized query.
                                            if (!partialRewritings.get(qnPredicate).contains(qn)) {
                                                break;
                                            }
                                        }
                                    }
                                }

                                // Moreover, if qn was subsumed, no need to keep rewriting it with other rules. 
                                if (!partialRewritings.get(qnPredicate).contains(qn)) {
                                    break;
                                }
                            }
                        }
                        // If we managed to exhaustively rewrite qn without it being subsumed by other queries
                        // then we mark it as explored. Otherwise, it means we need to rewrite the query that was
                        // subsuming it.
                        if (partialRewritings.get(qnPredicate).contains(qn)) {
                            exploredQueries.add(qn);
                        }
                    }            
                }
            }
        } while (!newQueries.isEmpty());

        // The final Datalog query is the one containing all the reconciliation rules
        // together with all undecomposable rewritings of the components we built.

        Set<String> supportPredicates = new HashSet<>();
        Set<String> bodyPreds = new HashSet<>();

        Set<IRule> result = new HashSet<>();
        for(IRule r: datalogRules){
            result.add(r);
            supportPredicates.add(r.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol());
            for(ILiteral a : r.getBody()){
                bodyPreds.add(a.getAtom().getPredicate().getPredicateSymbol());
            }
        }

        for (QueryGraph graph : partialRewritings.values()) {
            for(IRule r : graph.getRules()){
                if (!excludedRulesFromFinalRewriting.contains(r)){
                    result.add(r);
                    supportPredicates.add(r.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol());
                    for(ILiteral a : r.getBody()){
                        bodyPreds.add(a.getAtom().getPredicate().getPredicateSymbol());
                    }
                }
            }
            
        }
        
        // Prune rules not mentioning edb predicates in the body, and inductively 
        // all rules with a body predicate not occurring in the head of any other rule
        // Moreover, we also do the opposite: if a rule produces a predicate that does not
        // appear in the body of any other rule, and this predicate is not a query predicate
        // we can safely remove it, and inductively all other rules becoming like this.

        // if edbPredicates is empty, assume everything is edb: no pruning
        if(edbPredicates.isEmpty()){
            return result;
        }
        
        // Collect all the original queries predicates
        Set<String> originalQueryPreds =
            new HashSet<>(queries.stream().map(
                q -> q.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol()).
                collect(Collectors.toSet()));
        
        Set<IRule> removed = new HashSet<>();
 
        do {

            removed.clear();

            for(IRule rule : result){
                String headPred = rule.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol();
                if(!originalQueryPreds.contains(headPred) && !bodyPreds.contains(headPred)){
                    removed.add(rule);
                }else{
                    for(IPredicate p : rule.getBodyPredicates()){
                        String predSymb = p.getPredicateSymbol();
                        if(!edbPredicates.contains(predSymb) && !supportPredicates.contains(predSymb)){
                            removed.add(rule);
                            break;
                        }
                    }
                }
            }

            result.removeAll(removed);

            supportPredicates.clear();
            bodyPreds.clear();
            for(IRule rule : result){
                supportPredicates.add(rule.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol());
                for(ILiteral a : rule.getBody()){
                    bodyPreds.add(a.getAtom().getPredicate().getPredicateSymbol());
                }
            }
        }while(!removed.isEmpty());

        return result;
    }

    /**
     * Checks if the n atoms are sharing the same variables in all the existential
     * positions
     * 
     * @param q
     *           a conjunctive query
     * @param r
     *           a TGD
     * @param a1
     *           the first atom
     * @param a2
     *           the second atom
     * @return true if they share the same variables in all the existential
     *         positions
     */
    protected Set<IRule> factorisable(final IRule q, final IRule r, final Set<IRule> explored) {

        // worst case, return the original query
        final Set<IRule> factorizedQueries = new LinkedHashSet<IRule>();

        if (q.getBody().size() > 1) {
            // Get the atoms in body(q) that unify with head(r).

            final IAtom rheadAtom = r.getHead().iterator().next().getAtom();
            final Set<IPosition> headExPos = r.getExistentialPositions();

            final Set<IAtom> potentiallyUnifiableAtoms = new LinkedHashSet<IAtom>();
            for (final ILiteral l : q.getBody()) {
                final IAtom qbodyAtom = l.getAtom();

                if (qbodyAtom.getPredicate().equals(rheadAtom.getPredicate())) {
                    potentiallyUnifiableAtoms.add(qbodyAtom);
                }
            }

            if (potentiallyUnifiableAtoms.size() < 2)
                // No potentially unifiable atoms.
                return factorizedQueries;
            else {

                // compute the powerset of atoms that are potentially unifiable in the body in
                // the query.
                final Set<Set<IAtom>> atomsPowSet = Sets.powerSet(potentiallyUnifiableAtoms);
                // sort the set by size
                final List<Set<IAtom>> sortedPowSet = Lists.newArrayList(atomsPowSet);
                Collections.sort(sortedPowSet, new SetSizeComparator());

                final Set<Set<IAtom>> usedSets = new LinkedHashSet<Set<IAtom>>();
                for (final Set<IAtom> candidateSet : sortedPowSet) {
                    // check that we have at least two atoms in the candidate set.
                    if (candidateSet.size() > 1 && !subsumed(candidateSet, usedSets)) {
                        final Map<IVariable, ITerm> unifier = new HashMap<IVariable, ITerm>();
                        if (TermMatchingAndSubstitution.unify(candidateSet, unifier)) {
                            // the atoms have a unifier, check that there is a well-behaved existential
                            // variable

                            // get variables in existential positions
                            final Set<IVariable> variables = getVariablesInPositions(candidateSet, headExPos);
                            for (final IVariable var : variables) {
                                // check that the variable does not occur in non-existential positions
                                if (headExPos.containsAll(q.getPositions(var))
                                        && containedInAllAtoms(var, candidateSet)) {
                                    usedSets.add(candidateSet);

                                    final IRule factQuery = NormalizationUtils.canonicalRenaming(
                                            RewritingUtils.factoriseQuery(q, unifier), "U");
                                    if (!explored.contains(factQuery)) {
                                        factorizedQueries.add(factQuery);
                                    }
                                }
                            }

                        }
                    }
                }
                return factorizedQueries;
            }
        } else
            // No potentially unifiable atoms, return the original query.
            return factorizedQueries;
    }

    private boolean subsumed(final Set<IAtom> sub, final Set<Set<IAtom>> usedSet) {
        for (final Set<IAtom> used : usedSet) {
            if (used.size() < sub.size())
                return false;
            if (used.containsAll(sub))
                return true;
        }
        return false;
    }

    protected boolean containedInAllAtoms(final IVariable var, final Set<IAtom> candidateSet) {

        for (final IAtom atom : candidateSet) {
            if (!atom.getTuple().contains(var))
                return false;
        }
        return true;
    }

    protected Set<IVariable> getVariablesInPositions(final Set<IAtom> candidateSet, final Set<IPosition> positions) {
        final Set<IVariable> exPosVariables = new LinkedHashSet<IVariable>();
        for (final IAtom atom : candidateSet) {
            int pos = 0;
            for (final ITerm t : atom.getTuple()) {
                pos++;
                final IPosition curPos = new Position(atom.getPredicate().getPredicateSymbol(), pos);
                if (t instanceof IVariable && positions.contains(curPos)) {
                    exPosVariables.add((IVariable) t);
                }
            }
        }
        return exPosVariables;
    }

    private Component findReusableComponent(Component comp, Map<Component, IRule> builtComponents) {
        IRule q = builtComponents.get(comp);
        if(q != null){
            IRule queryComp = comp.getQuery();

            IPredicate qHeadPred = q.getHead().iterator().next().getAtom().getPredicate();
            ITuple altTupleHead = queryComp.getHead().iterator().next().getAtom().getTuple();
            ILiteral altCompHead = Factory.BASIC.createLiteral(true, qHeadPred, altTupleHead);
            return new Component(
                Factory.BASIC.createRule(Collections.singleton(altCompHead), queryComp.getBody()));
        }
        return null;
    }

    private void addRuleToQueryGraph(IRule rule, Map<IPredicate, QueryGraph> graphMap) {
        IPredicate headPred = rule.getHead().iterator().next().getAtom().getPredicate();
        QueryGraph graph = graphMap.get(headPred);

        if (graph == null) {
            graph = new QueryGraph();
            graphMap.put(headPred, graph);
        }

        graph.addRule(rule);
    }

    private void addRuleToQueryGraph(IRule parent, IRule child, Map<IPredicate, QueryGraph> graphMap) {
        IPredicate headPred = parent.getHead().iterator().next().getAtom().getPredicate();
        QueryGraph graph = graphMap.get(headPred);

        if (graph == null) {
            graph = new QueryGraph();
        }

        graph.addRule(parent, child);
    }
}