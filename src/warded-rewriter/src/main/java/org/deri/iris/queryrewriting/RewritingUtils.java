/*
 * Integrated Rule Inference System (IRIS+-):
 * An extensible rule inference system for datalog with extensions.
 *
 * Copyright (C) 2009 ICT Institute - Dipartimento di Elettronica e Informazione (DEI),
 * Politecnico di Milano, Via Ponzio 34/5, 20133 Milan, Italy.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA  02110-1301, USA.
 */
package org.deri.iris.queryrewriting;

import java.lang.String;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.Configuration;
import org.deri.iris.EvaluationException;
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
import org.deri.iris.basics.Position;
import org.deri.iris.factory.Factory;
import org.deri.iris.facts.Facts;
import org.deri.iris.facts.IFacts;
import org.deri.iris.queryrewriting.caching.CartesianCache;
import org.deri.iris.queryrewriting.caching.CoveringCache;
import org.deri.iris.queryrewriting.caching.CoveringCache.CacheType;
import org.deri.iris.queryrewriting.caching.MGUCache;
import org.deri.iris.queryrewriting.caching.MapsToCache;
import org.deri.iris.rules.compiler.ICompiledRule;
import org.deri.iris.rules.compiler.RuleCompiler;
import org.deri.iris.storage.IRelation;
import org.deri.iris.storage.IRelationFactory;
import org.deri.iris.storage.RelationFactory;
import org.deri.iris.storage.simple.SimpleRelation;
import org.deri.iris.utils.TermMatchingAndSubstitution;
import org.deri.iris.utils.UniqueList;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;


/**
 * @author Giorgio Orsi <orsi@elet.polimi.it> - Politecnico di Milano
 * @version 1.0
 */

public class RewritingUtils {

  public static Configuration defaultConfiguration = new Configuration();
  private static int lastQueryId = 1;

  public static List<IPredicate> getPredicates(final List<IRule> tgds) {
    final List<IPredicate> result = new UniqueList<IPredicate>();

    for (final IRule r : tgds) {
      for (final ILiteral l : r.getHead()) {
        result.add(l.getAtom().getPredicate());
      }
      for (final ILiteral l : r.getBody()) {
        result.add(l.getAtom().getPredicate());
      }
    }
    return result;
  }

  public static Set<ILiteral> applyMGU(final Set<ILiteral> lits, final Map<IVariable, ITerm> map) {
    final Set<ILiteral> result = new LinkedHashSet<ILiteral>();

    for (final ILiteral l : lits) {
      result.add(applyMGU(l.getAtom(), map));
    }
    return result;
  }

  /**
   * Applies the MGU to the atoms to be unified
   *
   * @param a
   *          the atom
   * @param map
   *          the substitution
   * @return the unified atom
   */
  public static ILiteral applyMGU(final IAtom a, final Map<IVariable, ITerm> map) {

    if (MGUCache.inCache(a, map)) {
      return MGUCache.getLiteral(a, map);
    }

    final IBasicFactory bf = BasicFactory.getInstance();
    final List<ITerm> freshTerms = new LinkedList<ITerm>();

    boolean applied;
    ITuple t = a.getTuple();
    final Set<ITuple> generated = new LinkedHashSet<ITuple>();

    do {
      generated.add(t);
      applied = false;
      final Iterator<IVariable> kIt = map.keySet().iterator();
      while (kIt.hasNext()) {
        freshTerms.clear();
        final IVariable k = kIt.next();
        final Iterator<ITerm> tIt = t.iterator();
        while (tIt.hasNext()) {
          final ITerm v = tIt.next();
          if (v.equals(k)) {
            freshTerms.add(map.get(k));
            applied = true;
          } else {
            freshTerms.add(v);
          }
        }
        t = bf.createTuple(freshTerms);
      }

    } while (applied && !generated.contains(t));

    final ILiteral literal = bf.createLiteral(true, bf.createAtom(a.getPredicate(), t));
    MGUCache.cache(a, map, literal);
    return literal;
  }

  public static long atomsCount(final Set<IRule> rewriting) {
    long length = 0;
    for (final IRule q : rewriting) {
      length += q.getBody().size();
    }
    return length;
  }

  public static long joinCount(final Set<IRule> rewriting) {

    long totJoins = 0;
    for (final IRule r : rewriting) {
      final Set<PositionJoin> jt = DepGraphUtils.computePositionJoins(r);
      for (final PositionJoin j : jt) {
        totJoins += j.getCount();
      }
    }
    return totJoins;
  }

  /**
   * Checks whether there exists a homomorphism from {@link IRule} r1 to
   * {@link IRule} r2 and returns that inside {@link Map<IVariable,ITerm>}
   * substitution.
   *
   * @pre r1 and r2 have disjoint sets of variables. Since the substitution
   *      operates on these variable, the caller has to take care that the
   *      variables are properly renamed before calling this method.
   * @param r1
   *          the first rule.
   * @param r2
   *          the second rule.
   * @param substitution
   *          the homomorphism (if any).
   * @return is the homomorphism exists.
   */
  public static boolean mapsTo(final IRule r1, final IRule r2) {
    if (!r2.getPredicates().containsAll(r1.getPredicates()))
      return false;

    final Set<ILiteral> s1 = r1.getAllLiterals();
    final Set<ILiteral> s2 = r2.getAllLiterals();

    if (s2.containsAll(s1)) {
      MapsToCache.cache(s1, s2, MapsToCache.CacheType.MAPSTO);
      return true;
    }

    if (MapsToCache.inCache(s1, s2, MapsToCache.CacheType.NOT_MAPSTO)) {
      return false;
    }

    if (MapsToCache.inCache(s1, s2, MapsToCache.CacheType.MAPSTO)) {
      return true;
    }

    if (mapsOnFrozen(r1, r2)) {
      MapsToCache.cache(s1, s2, MapsToCache.CacheType.MAPSTO);
      return true;
    } else {
      MapsToCache.cache(s1, s2, MapsToCache.CacheType.NOT_MAPSTO);
      return false;
    }
  }

  private static boolean mapsOnFrozen(final IRule r1, final IRule r2) {
    // Freeze r2 and checks whether r1 fires in the presence of such an
    // instance.

    final IFacts frozen = freezeRule(r2);
    final RuleCompiler ruleCompiler = new RuleCompiler(frozen, defaultConfiguration);

    final ICompiledRule compiledRule = ruleCompiler.compile(r1);

    final IRelation evaluation = compiledRule.evaluate();

    for (final IPredicate headPred : r2.getHeadPredicates()) {
      final IRelation headRel = frozen.get(headPred);
      for (int i = 0; i < headRel.size(); i++) {
        if (!evaluation.contains(headRel.get(i)))
          return false;
      }
    }
    return true;
  }

  private static IFacts freezeRule(final IRule rule) {

    final IRelationFactory relFactory = new RelationFactory();

    final Map<IPredicate, IRelation> predRelMap = new HashMap<IPredicate, IRelation>();

    for (final ILiteral l : rule.getAllLiterals()) {
      if (l.isPositive()) {
        final IAtom a = l.getAtom();
        final IPredicate p = a.getPredicate();
        // Check whether the map has already an entry for the predicate
        if (predRelMap.containsKey(p)) {
          predRelMap.get(p).add(freezeTuple(a.getTuple()));
        } else {
          // create a new entry by creating a new relation
          final IRelation rel = new SimpleRelation();
          rel.add(freezeTuple(a.getTuple()));
          predRelMap.put(p, rel);
        }
      }
    }

    return new Facts(predRelMap, relFactory);
  }

  private static ITuple freezeTuple(final ITuple tuple) {

    final List<ITerm> frozenTerms = Lists.newArrayList();

    for (final ITerm t : tuple) {
      frozenTerms.add(freezeTerm(t));
    }

    return Factory.BASIC.createTuple(frozenTerms);
  }

  private static ITerm freezeTerm(final ITerm term) {

    if (term.isGround())
      // already frozen
      return term;
    else if (term instanceof IVariable)
      return Factory.TERM.createString("f_" + term.getValue());
    else
      throw new EvaluationException("Unable to freeze a constructed term!");
  }

  public static boolean mapsTo(final Collection<ILiteral> s1, final Collection<ILiteral> s2) {

    final Collection<ILiteral> renamedS1 = NormalizationUtils.canonicalRenaming(s1, "V");

    final Set<ITerm> tSet1 = new LinkedHashSet<ITerm>();
    final Set<ITerm> tSet2 = new LinkedHashSet<ITerm>();

    for (final ILiteral l : renamedS1) {
      tSet1.addAll(l.getAtom().getTuple());
    }

    for (final ILiteral l : s2) {
      tSet2.addAll(l.getAtom().getTuple());
    }

    Set<Map<IVariable, ITerm>> cartesian = new LinkedHashSet<Map<IVariable, ITerm>>();

    if (CartesianCache.inCache(tSet1, tSet2)) {
      cartesian = CartesianCache.getCartesian(tSet1, tSet2);
    } else {
      @SuppressWarnings("unchecked") final Set<List<ITerm>> possibleSubstitutions = Sets.cartesianProduct(tSet1, tSet2);
      final Map<ITerm, Set<List<ITerm>>> substitutionSets = new LinkedHashMap<ITerm, Set<List<ITerm>>>();

      // Create one set for each term in the domain of the substitution.
      for (final List<ITerm> possibleSubstitution : possibleSubstitutions) {
        final ITerm keyTerm = possibleSubstitution.get(0);
        if (substitutionSets.containsKey(keyTerm)) {
          substitutionSets.get(keyTerm).add(possibleSubstitution);
        } else {
          final Set<List<ITerm>> substitutions = new LinkedHashSet<List<ITerm>>();
          substitutions.add(possibleSubstitution);
          substitutionSets.put(keyTerm, substitutions);
        }
      }

      // compute the valid substitutions
      final List<Set<List<ITerm>>> list = Lists.newArrayList();
      for (final Set<List<ITerm>> substitutionSet : substitutionSets.values()) {
        list.add(substitutionSet);
      }
      final Set<List<List<ITerm>>> validSubstitutions = Sets.cartesianProduct(list);

      // create the maps
      for (final List<List<ITerm>> validSubstitution : validSubstitutions) {
        final Map<IVariable, ITerm> map = new HashMap<IVariable, ITerm>();
        for (final List<ITerm> termMap : validSubstitution) {
          map.put((IVariable) termMap.get(0), termMap.get(1));
        }
        cartesian.add(map);
      }

      // Cache the cartesian product
      CartesianCache.cache(tSet1, tSet2, cartesian);
    }

    for (final Map<IVariable, ITerm> m : cartesian) {

      // Apply the substitution

      // LOGGER.trace("Applying substitution " + m.toString() + " to literals "
      // + s1);
      boolean allMap = true;
      for (final ILiteral l1 : renamedS1) {
        if (!s2.contains(applyMGU(l1.getAtom(), m))) {
          allMap = false;
          break;
        }
      }

      if (allMap)
        return true;

    }
    return false;
  }

  public static IRule reduceQuery(final IRule q,
      final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> deps) {

    final long qElimTime = System.currentTimeMillis();
    IRule qRed = Factory.BASIC.createRule(q.getHead(), q.getBody());
    ILiteral coveredAtom = null;

    if (qRed.getBody().size() > 1) {
      boolean covered = true;
      do {
        covered = false;
        for (int i = 0; (i < (qRed.getBody().size() - 1)) && !covered; i++) {
          for (int j = i + 1; (j < qRed.getBody().size()) && !covered; j++) {

            final ILiteral la = Iterators.get(qRed.getBody().iterator(), i);
            final ILiteral lb = Iterators.get(qRed.getBody().iterator(), j);

            if (covers(la, lb, deps, qRed)) {
              coveredAtom = lb;
              covered = true;
            }
            if (covers(lb, la, deps, qRed)) {
              coveredAtom = la;
              covered = true;
            }
          }
        }
        if (covered) {
          final Set<ILiteral> reducedBody = new LinkedHashSet<ILiteral>();
          for (final ILiteral l : qRed.getBody())
            if (!l.equals(coveredAtom)) {
              reducedBody.add(l);
            }
          qRed = Factory.BASIC.createRule(qRed.getHead(), reducedBody);
        }
      } while (covered);
    }

    return qRed;
  }

  public static boolean covers(final ILiteral a, final ILiteral b,
      final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> deps, final IRule q) {

    // Check whether is in cache.

    if (CoveringCache.inCache(a, b, CacheType.NOT_COVERING)) {
      return false;
    }

    if (CoveringCache.inCache(a, b, CacheType.COVERING)) {
      return true;
    }

    final Set<ITerm> coveredTerms = new LinkedHashSet<ITerm>();

    int i = 0;
    for (final ITerm tb : b.getAtom().getTuple()) {
      i++;
      final IPosition tbPosInB = new Position(b.getAtom().getPredicate().getPredicateSymbol(), i);

      final Set<IPosition> tbPossInA = getTermPositionsInLiteral(tb, a);
      for (final IPosition tbPosInA : tbPossInA) {
        final Pair<IPosition, IPosition> dep = Pair.of(tbPosInA, tbPosInB);
        // check that a cover dependency exists.
        if (deps.containsKey(dep)) {
          coveredTerms.add(tb);
        }
      }
    }

    if (coveredTerms.containsAll(b.getAtom().getTuple())) {
      // add the pair of literals to the covering cache.
      CoveringCache.cache(a, b, CacheType.COVERING);
      return true;
    } else {
      CoveringCache.cache(a, b, CacheType.NOT_COVERING);
      return false;
    }

  }

  private static Set<IPosition> getTermPositionsInLiteral(final ITerm tb, final ILiteral a) {
    final Set<IPosition> pos = new HashSet<IPosition>();

    final List<ITerm> terms = a.getAtom().getTuple();
    for (int i = 0; i < terms.size(); i++) {
      if (terms.get(i).equals(tb)) {
        pos.add(new Position(a.getAtom().getPredicate().getPredicateSymbol(), i + 1));
      }
    }
    return pos;
  }

  public static IRule factoriseQuery(final IRule q, final Map<IVariable, ITerm> map) {

    // The list containing the literals for q'
    final Set<ILiteral> qPrimeBodyLiterals = new HashSet<ILiteral>();
    final Set<ILiteral> qPrimeHeadLiterals = new HashSet<ILiteral>();

    // For each literal in the body of q
    for (final ILiteral curLit : q.getBody()) {
      // add the non unified atoms of q to q'
      qPrimeBodyLiterals.add(Factory.BASIC.createLiteral(RewritingUtils.applyMGU(curLit.getAtom(), map)));
    }

    // for each literal (should be one) in the head of q
    for (final ILiteral curLit : q.getHead()) {
      // Apply the unification also to the head
      qPrimeHeadLiterals.add(Factory.BASIC.createLiteral(RewritingUtils.applyMGU(curLit.getAtom(), map)));
    }

    final IRule factor = Factory.BASIC.createRule(qPrimeHeadLiterals, qPrimeBodyLiterals);

    return factor;
  }

  public static List<IRule> getTGDs(final List<IRule> rules, final List<IQuery> queryHeads) {

    final List<IRule> output = new UniqueList<IRule>();

    for (final IRule r : rules) {
      boolean tgd = true;

      // Check for storage predicate in the body
      for (final ILiteral l : r.getBody()) {
        if (l.getAtom().getPredicate().getPredicateSymbol().startsWith("@")) {
          tgd = false;
        }
      }

      // Check for builtin predicates, EGDs and negative Constraints.
      for (final ILiteral l : r.getHead())
        if (!l.isPositive() || l.getAtom().isBuiltin()) {
          tgd = false;
        } else {
          // Check whether this rule is a query definition
          for (final IQuery q : queryHeads)
            if (q.getLiterals().contains(l)) {
              tgd = false;
            }
        }

      // Return the tgd
      if (tgd) {
        output.addAll(RewritingUtils.normalizeTGD(r));
      }
    }
    return output;
  }

  public static Set<IRule> normalizeTGD(final IRule r) {

    // Check if the rule head is already normalized.
    final Set<ILiteral> head = r.getHead();

    if (head.size() == 1)
      return Sets.newHashSet(r);

    // Construct an equivalent set of single-head rules.
    final Set<IVariable> exVars = r.getExistentialVariables();
    final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> posDeps = DepGraphUtils
        .computePropagationGraph(Lists.newArrayList(r));
    final Map<IPosition, Set<IRule>> exPos = DepGraphUtils.computeAffectedPositions(Lists.newArrayList(r), posDeps);
    final Set<PositionJoin> exJoins = DepGraphUtils.computeExistentialJoins(head, exPos);

    final Set<IRule> rules = new HashSet<IRule>();
    if (exVars.isEmpty() || exJoins.isEmpty()) {
      // just split the head atoms
      for (final ILiteral l : head) {
        rules.add(Factory.BASIC.createRule(Sets.newHashSet(l), r.getBody()));
      }
      return rules;
    }

    // Partition the set of atoms
    final Set<Set<Set<ILiteral>>> currentLevelDecompositions = new LinkedHashSet<Set<Set<ILiteral>>>();

    // create a level 0 decomposition (i.e., only singletons)
    final Set<Set<ILiteral>> decomposition = new LinkedHashSet<Set<ILiteral>>();
    for (final ILiteral l : head) {
      decomposition.add(ImmutableSet.of(l));
    }
    currentLevelDecompositions.add(decomposition);

    int level = 1;
    do {
      Set<Set<Set<ILiteral>>> nextLevelDecompositions = new LinkedHashSet<Set<Set<ILiteral>>>();

      for (final Set<Set<ILiteral>> currentDecomposition : currentLevelDecompositions) {
        // check validity of the decomposition
        if (validDecomposition(currentDecomposition, exPos, exJoins)) {
          // Build the rules
          int auxCount = 0;
          for (final Set<ILiteral> component : currentDecomposition) {

            // collect the variables
            final Set<IVariable> vars = RewritingUtils.getVariables(component);

            if (component.size() > 0) {
              // Create an auxiliary predicate
              final IPredicate auxPred = Factory.BASIC.createPredicate("aux_" + auxCount, vars.size());
              auxCount++;

              // Create an auxiliary tuple
              final ITuple auxTuple = Factory.BASIC.createTuple(vars.toArray(new ITerm[1]));

              // Create the auxiliary atom
              final ILiteral auxLiteral = Factory.BASIC.createLiteral(true, auxPred, auxTuple);

              /*
               * Create auxiliary rules:
               */

              // body
              rules.add(Factory.BASIC.createRule(Sets.newHashSet(auxLiteral), r.getBody()));

              // all literals in the partition
              for (final ILiteral l : component) {
                rules.add(Factory.BASIC.createRule(Sets.newHashSet(l), Sets.newHashSet(auxLiteral)));
              }
            }
          }
          return rules;
        }
      }
      // compute next-level decompositions
      nextLevelDecompositions = mergeDecompositions(currentLevelDecompositions);
      currentLevelDecompositions.clear();
      currentLevelDecompositions.addAll(nextLevelDecompositions);
      // LOGGER.trace(currentLevelDecompositions);
      level++;
    } while (level <= head.size());

    return Sets.newHashSet();
  }

  private static Set<IVariable> getVariables(final Set<ILiteral> component) {
    final Set<IVariable> vars = new HashSet<IVariable>();
    for (final ILiteral l : component) {
      vars.addAll(l.getVariables());
    }
    return vars;
  }

  public static List<IRule> getSBoxRules(final List<IRule> rules, final List<IQuery> queryHeads) {

    final List<IRule> output = new UniqueList<IRule>();

    for (final IRule r : rules) {
      // Check for storage predicate in the body
      for (final ILiteral l : r.getBody()) {
        if (l.getAtom().getPredicate().getPredicateSymbol().startsWith("@")) {
          output.add(r);
        }
      }
    }
    return output;
  }

  public static List<IRule> getQueries(final List<IRule> bodies, final List<IQuery> queryHeads) {
    final List<IRule> output = new UniqueList<IRule>();
    for (final IRule r : bodies) {
      for (final IQuery q : queryHeads)
        if (r.getHead().iterator().next().equals(q.getLiterals().get(0))) {
          output.add(r);
        }
    }

    return output;
  }

  public static Set<IRule> getConstraints(final List<IRule> rules, final List<IQuery> queryHeads) {

    final Set<IRule> output = Sets.newHashSet();
    for (final IRule r : rules) {
      for (final ILiteral l : r.getHead())
        if (!l.isPositive() || l.getAtom().isBuiltin()) {
          for (final IQuery q : queryHeads)
            if (!q.getLiterals().contains(l)) {
              final Set<ILiteral> head = Sets.newHashSet(Factory.BASIC.createLiteral(true,
                  Factory.BASIC.createPredicate("Q_CNS", 0), Factory.BASIC.createTuple()));
              final Set<ILiteral> body = Sets.newHashSet();
              body.add(Factory.BASIC.createLiteral(true, l.getAtom()));
              body.addAll(r.getBody());
              output.add(Factory.BASIC.createRule(head, body));
            }
        }
    }
    return output;
  }

  public static Map<IVariable, ITerm> invertSubstitution(final Map<IVariable, ITerm> m) {

    final Map<IVariable, ITerm> map = new LinkedHashMap<IVariable, ITerm>();

    for (final IVariable v : m.keySet()) {
      final ITerm t = m.get(v);
      if (t instanceof IVariable) {
        map.put((IVariable) m.get(v), v);
      }
    }
    return map;
  }

  public static IRule createReconciliationRule(final IRule query, final Set<IRule> queryComponents) {
    final IBasicFactory factory = BasicFactory.getInstance();

    final List<ILiteral> body = new LinkedList<ILiteral>();
    for (final IRule comp : queryComponents) {
      body.add(comp.getHead().iterator().next());
    }

    return factory.createRule(query.getHead(), body);
  }

  public static Set<IRule> decomposeQuery(final IRule query, final Set<IPosition> exPos,
  final List<IRule> tgds) {
    
    if(query.getBody().size() < 2) {
      return Sets.newHashSet(query);
    }

    Set<Set<ILiteral>> candidateComponents = new HashSet<>();

    //Assume at the beginning that each atom in the body of the query is its own component
    for(ILiteral atom : query.getBody()){
      candidateComponents.add(Collections.singleton(atom));
    }

    Set<IVariable> queryVariables = query.getAllVariables();
    Set<IVariable> dangerousVariables = new HashSet<>(queryVariables);

    //After this first pass, the set dangerousVariables contains only the variables that appear exclusively
    //in affected positions of the query,
    for(IVariable v : queryVariables){

      outer_loop: for(ILiteral queryAtom : query.getBody()){

        for(int position = 0; position < queryAtom.getAtom().getPredicate().getArity(); position++ ){

          IVariable curVar = (IVariable)queryAtom.getAtom().getTuple().get(position);
          if(curVar.equals(v)){

            Position p = new Position(queryAtom.getAtom().getPredicate().getPredicateSymbol(), position + 1);

            // the current variable v appears in a non-affected position
            if(!exPos.contains(p) || query.getHeadVariables().contains(v)){
              dangerousVariables.remove(v);
              break outer_loop;
            }
          }
          
        }
      }
    }

    //In this second pass, for each dangerous variable, we modify the current components, by mering the ones containing
    //the dangerous variable

    for(IVariable v : dangerousVariables){
      Set<Set<ILiteral>> newCandidateComponents = new HashSet<>();
      Set<ILiteral> tempComponent = new HashSet<>();

      for(Set<ILiteral> component : candidateComponents){

        boolean appeared = false;
        for(ILiteral atomInComponent : component){
          if(atomInComponent.getVariables().contains(v)){
            tempComponent.addAll(component);
            appeared = true;
            break;
          }
        }
        if(!appeared){
          newCandidateComponents.add(component);
        }
      }

      newCandidateComponents.add(tempComponent);
      candidateComponents = newCandidateComponents;
    }
    
    return constructQueryComponents(query, exPos, candidateComponents);
  }

public static Set<Set<ILiteral>> mergeSets(Set<Set<ILiteral>> sets) {
  Set<Set<ILiteral>> result =  new HashSet<>();

  for (Set<ILiteral> currentSet : sets) {
      boolean merged = false;

      for (Set<ILiteral> mergedSet : result) {
          if (hasCommonElement(currentSet, mergedSet)) {
              mergedSet.addAll(currentSet);
              merged = true;
              break;
          }
      }

      if (!merged) {
          result.add(new HashSet<>(currentSet));
      }
  }

  return result;
}

private static boolean hasCommonElement(Set<ILiteral> set1, Set<ILiteral> set2) {
  for (ILiteral element : set1) {
      if (set2.contains(element)) {
          return true;
      }
  }
  return false;
}


  private static Set<Set<Set<ILiteral>>> mergeDecompositions(final Set<Set<Set<ILiteral>>> currentLevelDecompositions) {

    final Set<Set<Set<ILiteral>>> next = new LinkedHashSet<Set<Set<ILiteral>>>();

    for (final Set<Set<ILiteral>> decomposition : currentLevelDecompositions) {
      // merge the components of the decomposition to create one set of literal
      // less than the current
      // decomposition
      for (final Set<ILiteral> comp1 : decomposition) {
        for (final Set<ILiteral> comp2 : decomposition) {
          if (!comp1.equals(comp2)) {
            final Set<Set<ILiteral>> mergedDecomposition = new LinkedHashSet<Set<ILiteral>>();
            mergedDecomposition.addAll(decomposition);
            final Set<ILiteral> mergedComponent = Sets.newLinkedHashSet(comp1);
            mergedComponent.addAll(comp2);
            mergedDecomposition.add(mergedComponent);
            mergedDecomposition.remove(comp1);
            mergedDecomposition.remove(comp2);
            next.add(mergedDecomposition);
          }
        }
      }
    }
    return next;
  }

  static Set<IRule> constructQueryComponents(final IRule query, final Set<IPosition> exPos,
      final Set<Set<ILiteral>> set) {

    final IBasicFactory factory = BasicFactory.getInstance();
    final Set<IRule> out = new LinkedHashSet<IRule>();

    int count = 1;
    for (final Set<ILiteral> s : set) {

      final Set<IVariable> sVars = variablesFrom(s);
      final Set<IVariable> headVars = query.getHeadVariables();

      final List<ITerm> propVars = Lists.newLinkedList();
      for (final IVariable v : sVars) {

        if (headVars.contains(v) || (query.isShared(v)
            && !Sets.difference(query.getBodyPositions(ImmutableSet.of(v)), exPos).isEmpty())) {
          propVars.add(v);
        }
      }

      final String headPredSym = query.getHead().iterator().next().getAtom().getPredicate().getPredicateSymbol();
      final IPredicate headPred = factory.createPredicate(headPredSym.concat("_" + lastQueryId+"_"+count), propVars.size());

      final ILiteral head = factory.createLiteral(true, headPred, factory.createTuple(propVars));

      final IRule comp = factory.createRule(ImmutableList.of(head), s);

      out.add(comp);
      count++;
    }

    lastQueryId++;
    return out;
  }

  private static Set<IVariable> variablesFrom(final Set<ILiteral> literals) {
    final Set<IVariable> vars = new LinkedHashSet<IVariable>();

    for (final ILiteral l : literals) {
      vars.addAll(variablesFrom(l));
    }
    return vars;
  }

  private static Set<IVariable> variablesFrom(final ILiteral l) {

    final Set<IVariable> vars = new LinkedHashSet<IVariable>();
    for (final ITerm t : l.getAtom().getTuple()) {
      if (t instanceof IVariable) {
        vars.add((IVariable) t);
      }
    }
    return vars;
  }

  private static boolean validDecomposition(final Set<Set<ILiteral>> components, final Map<IPosition, Set<IRule>> exPos,
      final Set<PositionJoin> exJoins) {

    final Set<PositionJoin> compExJoins = new LinkedHashSet<PositionJoin>();
    for (final Set<ILiteral> c : components) {
      compExJoins.addAll(DepGraphUtils.computeExistentialJoins(c, exPos));
    }
    // Check that the existential joins are preserved
    return compExJoins.equals(exJoins);
  }

  public static Collection<IRule> unfold(final IRule reconciliationQuery, final Map<String, Set<IRule>> rewritingMap,
      final Set<IRule> cns) {

    final Collection<IRule> unfolded = new ArrayList<IRule>();
    unfolded.add(NormalizationUtils.canonicalRenaming(reconciliationQuery, "U"));

    List<IRule> temp;
    for (final String key : rewritingMap.keySet()) {

      temp = ImmutableList.copyOf(unfolded);
      unfolded.clear();
      // get the corresponding expansions
      final Set<IRule> rewritings = rewritingMap.get(key);
      for (final IRule r : temp) {
        for (final ILiteral t : r.getBody()) {
          if (t.getAtom().getPredicate().getPredicateSymbol().equals(key)) {
            // possible expansion
            final Map<IVariable, ITerm> gamma = new LinkedHashMap<IVariable, ITerm>();
            for (IRule exp : rewritings) {
              exp = NormalizationUtils.canonicalRenaming(exp, "V");
              if (TermMatchingAndSubstitution.unify(t.getAtom(), exp.getHead().iterator().next().getAtom(), gamma)) {
                final IRule qPrime = NormalizationUtils
                    .canonicalRenaming(RewritingUtils.rewrite(r, t.getAtom(), exp.getBody(), gamma), "U");
                unfolded.add(qPrime);
              }
            }
          }
        }
      }

    }
    return unfolded;
  }

  public static boolean resolves(final IRule r1, final IRule r2, final Map<IVariable, ITerm> gamma) {

    for (final ILiteral l1 : r1.getHead()) {
      for (final ILiteral l2 : r2.getBody())
        if (TermMatchingAndSubstitution.unify(l1.getAtom(), l2.getAtom(), gamma))
          return true;
    }
    return false;
  }

  public static boolean resolves(final IRule r, final IRule q, final IAtom a, final Map<IVariable, ITerm> gamma) {

    // check if the head of the rule unifies with the atom a
    return TermMatchingAndSubstitution.unify(a, r.getHead().iterator().next().getAtom(), gamma);
  }

  public static boolean isApplicable(final IRule r, final IRule q, final IAtom a, final Map<IVariable, ITerm> gamma) {

    // check if the head of the rule unifies with the atom a
    if (!TermMatchingAndSubstitution.unify(a, r.getHead().iterator().next().getAtom(), gamma))
      return false;
    else {
      if (r.getExistentialPositions().size() > 0) {
        // test if the shared variables in q will be preserved by the rewriting
        // For each term in a
        for (int i = 0; i < a.getTuple().size(); i++) {
          if ((a.getTuple().get(i).isGround() || q.isShared(a.getTuple().get(i)))
              && !r.getBodyVariables().contains(r.getHead().iterator().next().getAtom().getTuple().get(i)))
            return false;
        }
      }
    }
    return true;
  }

  public static IRule rewrite(final IRule resolvent, final IAtom resolvedAtom, final Set<ILiteral> resolver,
      final Map<IVariable, ITerm> gamma) {

    // The list containing the literals for q'
    final Set<ILiteral> qPrimeHeadLiterals = new LinkedHashSet<ILiteral>();
    final Set<ILiteral> qPrimeBodyLiterals = new LinkedHashSet<ILiteral>();

    // Apply the MGU also to the head of the query
    for (final ILiteral l : resolvent.getHead()) {
      qPrimeHeadLiterals.add(Factory.BASIC.createLiteral(RewritingUtils.applyMGU(l.getAtom(), gamma)));
    }

    // Rewrite the atom a in the query q with the atoms in body producing a
    // query q'
    // For each literal in the body of q
    for (final ILiteral l : resolvent.getBody()) {
      if (!l.getAtom().equals(resolvedAtom)) {
        qPrimeBodyLiterals.add(Factory.BASIC.createLiteral(RewritingUtils.applyMGU(l.getAtom(), gamma)));
      }
    }
    for (final ILiteral l : resolver) {
      qPrimeBodyLiterals.add(Factory.BASIC.createLiteral(RewritingUtils.applyMGU(l.getAtom(), gamma)));
    }

    return Factory.BASIC.createRule(qPrimeHeadLiterals, qPrimeBodyLiterals);
  }

// Marco: fix subsumption check
  public static boolean isSubsumed(final QueryGraph queryGraph, final IRule q, final Set<IRule> explored,
  final Set<IRule> newQueries) {


  boolean subsumed = false;
  
  Set<IRule> copyOfQueryGraph = ImmutableSet.copyOf(queryGraph.getRules());
    

  for (final IRule qPrime : copyOfQueryGraph) {
  // Compare two different queries!
    if (queryGraph.contains(q) && queryGraph.contains(qPrime) && !q.equals(qPrime)) {
      IRule qPrimeCan = NormalizationUtils.canonicalRenaming(qPrime, "VV");
      IRule qCan = NormalizationUtils.canonicalRenaming(q, "UU");

      if (RewritingUtils.mapsTo(qPrimeCan, qCan)) {
        queryGraph.removeAndBypassSuccessors(q, qPrime, explored, newQueries);
        subsumed = true;
        break;
      }
    }
  }

  if(!subsumed){
    for (final IRule qPrime : copyOfQueryGraph){
      if (queryGraph.contains(q) && queryGraph.contains(qPrime) && !q.equals(qPrime)) {
        IRule qPrimeCan = NormalizationUtils.canonicalRenaming(qPrime, "VV");
        IRule qCan = NormalizationUtils.canonicalRenaming(q, "UU");
        if (RewritingUtils.mapsTo(qCan, qPrimeCan)) {
          queryGraph.removeAndBypassSuccessors(qPrime, q, explored, newQueries);
        }  
      }
    }
  }

  return subsumed;
  }

  public static void purgeSubsumed(final Set<IRule> queries) {

    final long pre = queries.size();

    final List<IRule> copy = Lists.newArrayList(queries);

    for (int i = 0; i < (copy.size() - 1); i++) {
      final IRule q1 = copy.get(i);
      if (queries.contains(q1)) {
        for (int j = i + 1; j < copy.size(); j++) {
          final IRule q2 = copy.get(j);
          if (queries.contains(q2))
            if (RewritingUtils.mapsTo(q1, q2)) {
              queries.remove(q2);
            } else if (RewritingUtils.mapsTo(q2, q1)) {
              queries.remove(q1);
            }
        }
      }
      if (((i % 500) == 0) && (copy.size() > 2000)) {
       // LOGGER.trace((copy.size() - i) + " queries left.");
      }
    }

    final long post = queries.size();

  }

  public Set<IPredicate> getPredicates(final Set<IRule> rules) {
    final Set<IPredicate> preds = Sets.newHashSet();
    for (final IRule r : rules) {
      preds.addAll(r.getPredicates());
    }
    return preds;
  }

  public static int getMaxQueryLength(final List<IRule> queryRules) {
    int bound = 1;
    for (final IRule q : queryRules) {
      if (q.getBody().size() > bound) {
        bound = q.getBody().size();
      }
    }
    return bound;
  }


  //Marco: adapted rule implication to arbitrary Datalog rules

  public static boolean implies(IRule r1, IRule r2){

    //Check if r2 is trivial, in which case it is trivially implied by r1.
    if(r2.getBody().contains(r2.getHead().iterator().next())){
      return true;
    }

    //If r2 is not trivial, we check if r1's head has the same predicate as r2's head.
    //If this is not the case, then there is not way for r1 to imply r2.
    if(!r1.getHead().iterator().next().getAtom().getPredicate().equals(
      r2.getHead().iterator().next().getAtom().getPredicate()
    )){
      return false;
    }

    final IFacts[] frozen = freezeRuleDatalog(r2);

    final RuleCompiler ruleCompiler = new RuleCompiler(frozen[1], defaultConfiguration);

    final ICompiledRule compiledRule = ruleCompiler.compile(r1);

    final IRelation evaluation = compiledRule.evaluate();

    for (final IPredicate headPred : r2.getHeadPredicates()) {
    final IRelation headRel = frozen[0].get(headPred);
    for (int i = 0; i < headRel.size(); i++) {
        if (!evaluation.contains(headRel.get(i)))
        return false;
    }
    }
    return true;
}

private static IFacts[] freezeRuleDatalog(final IRule rule) {

    final IRelationFactory relFactory = new RelationFactory();

    final Map<IPredicate, IRelation> predRelMapBody = new HashMap<IPredicate, IRelation>();
    final Map<IPredicate, IRelation> predRelMapHead = new HashMap<IPredicate, IRelation>();

    for (final ILiteral l : rule.getBody()) {
      if (l.isPositive()) {
        final IAtom a = l.getAtom();
        final IPredicate p = a.getPredicate();
        // Check whether the map has already an entry for the predicate
        if (predRelMapBody.containsKey(p)) {
          predRelMapBody.get(p).add(freezeTuple(a.getTuple()));
        } else {
          // create a new entry by creating a new relation
          final IRelation rel = new SimpleRelation();
          rel.add(freezeTuple(a.getTuple()));
          predRelMapBody.put(p, rel);
        }
      }
    }

    for (final ILiteral l : rule.getHead()) {
        if (l.isPositive()) {
          final IAtom a = l.getAtom();
          final IPredicate p = a.getPredicate();
          // Check whether the map has already an entry for the predicate
          if (predRelMapHead.containsKey(p)) {
            predRelMapHead.get(p).add(freezeTuple(a.getTuple()));
          } else {
            // create a new entry by creating a new relation
            final IRelation rel = new SimpleRelation();
            rel.add(freezeTuple(a.getTuple()));
            predRelMapHead.put(p, rel);
          }
        }
      }

      return new IFacts[] { new Facts(predRelMapHead, relFactory), new Facts(predRelMapBody, relFactory)};
    }


}
