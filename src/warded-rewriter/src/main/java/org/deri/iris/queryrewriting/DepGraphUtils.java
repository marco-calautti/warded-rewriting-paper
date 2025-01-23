/**
 * 
 */
package org.deri.iris.queryrewriting;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPosition;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.basics.Position;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;

/**
 * @author jd
 */
public class DepGraphUtils {

  private static PositionJoin getPositionJoin(final Set<PositionJoin> list, final IPosition left, final IPosition right) {
    for (final PositionJoin pj : list)
      if (pj.getLeftPosition().equals(left) && pj.getRightPosition().equals(right)
          || pj.getLeftPosition().equals(right) && pj.getRightPosition().equals(left))
        return pj;
    return null;
  }

  public static Set<PositionJoin> computePositionJoins(final Collection<ILiteral> literals) {
    final Set<PositionJoin> result = new LinkedHashSet<PositionJoin>();

    if (literals.size() > 1) {
      for (int k = 0; k < literals.size() - 1; k++) {
        final IAtom a1 = Iterators.get(literals.iterator(), k).getAtom();
        for (int l = k + 1; l < literals.size(); l++) {
          final IAtom a2 = Iterators.get(literals.iterator(), l).getAtom();
          int i = 0;
          for (final ITerm t1 : a1.getTuple()) {
            i++;
            int j = 0;
            for (final ITerm t2 : a2.getTuple()) {
              j++;
              if (t1 instanceof IVariable && t2 instanceof IVariable && t1.equals(t2)) {
                final IPosition p1 = new Position(a1.getPredicate().getPredicateSymbol(), i);
                final IPosition p2 = new Position(a2.getPredicate().getPredicateSymbol(), j);

                final PositionJoin pj = DepGraphUtils.getPositionJoin(result, p1, p2);
                if (pj == null) {
                  result.add(new PositionJoin(p1, p2, 1));
                } else {
                  pj.setCount(pj.getCount() + 1);
                }

              }
            }
          }
        }
      }
    }
    return result;
  }

  public static Set<PositionJoin> computePositionJoins(final IRule rule) {
    return computePositionJoins(rule.getBody());
  }

  public static Set<PositionJoin> computeExistentialJoins(final Collection<ILiteral> literals,
      final Map<IPosition, Set<IRule>> exPos) {

    final Set<PositionJoin> exJoins = new LinkedHashSet<PositionJoin>();
    if (literals.size() > 1) {

      final Set<PositionJoin> posJoin = computePositionJoins(literals);

      //System.out.println("heba--> posJoin" + posJoin);
      //System.out.println("exPos.keySet()-->" + exPos.keySet());

      for (final PositionJoin p : posJoin) {

         //     System.out.println("p-->" + p);
        if (exPos.keySet().contains(p.getLeftPosition()) && exPos.keySet().contains(p.getRightPosition())
            && !Sets.intersection(exPos.get(p.getLeftPosition()), exPos.get(p.getRightPosition())).isEmpty()) {
          exJoins.add(p);
            //  System.out.println("exJoins-->" + exJoins);

        }
      }
    }
    return exJoins;
  }

  public static Set<PositionJoin> computeExistentialJoins(final IRule query, final Map<IPosition, Set<IRule>> exPos) {

    return computeExistentialJoins(query.getBody(), exPos);
  }

  public static Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> computePropagationGraph(
      final List<IRule> tgds) {
    final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> posDeps = new LinkedHashMap<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>>();

    for (final IRule r : tgds) {

      // self loops
      for (final IPosition p : r.getRulePositions()) {
        final Pair<IPosition, IPosition> pair = ImmutablePair.of(p, p);
        if (!posDeps.containsKey(pair)) {
          final Set<Pair<List<IPosition>, List<IRule>>> ways = new LinkedHashSet<Pair<List<IPosition>, List<IRule>>>();
          final List<IPosition> path = Lists.newLinkedList();
          final List<IRule> label = Lists.newLinkedList();
          final Pair<List<IPosition>, List<IRule>> emptyPath = Pair.of(path, label);
          ways.add(emptyPath);
          posDeps.put(pair, ways);
        }
      }

      // direct dependencies
      final Set<IVariable> fVars = r.getFrontierVariables();
      for (final IVariable v : fVars) {
        final Set<IPosition> bodyPos = r.getTermBodyPositions(v);
        final Set<IPosition> headPos = r.getTermHeadPositions(v);
        for (final IPosition bp : bodyPos) {
          for (final IPosition hp : headPos) {
            final Pair<IPosition, IPosition> dep = ImmutablePair.of(bp, hp);
            Set<Pair<List<IPosition>, List<IRule>>> ways = posDeps.get(dep);
            if (ways == null) {
              ways = new LinkedHashSet<Pair<List<IPosition>, List<IRule>>>();
            }
            final List<IPosition> path = ImmutableList.of(bp, hp);
            final List<IRule> label = ImmutableList.of(r);
            final Pair<List<IPosition>, List<IRule>> way = Pair.of(path, label);
            ways.add(way);
            posDeps.put(dep, ways);
          }
        }
      }
    }

    return posDeps;
  }

  public static Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> computeCoverGraph(
      final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> deps) {

    final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> closure = Maps.newHashMap(deps);

    Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> tempDeps;
    do {
      tempDeps = ImmutableMap.copyOf(closure);
      // Cycle through the known position dependencies
      for (final Pair<IPosition, IPosition> depj : tempDeps.keySet()) {
        for (final Pair<IPosition, IPosition> depk : tempDeps.keySet()) {

          // Check that the position on the RHS is the same as the position on the LHS
          if (depj.getRight().equals(depk.getLeft())) {

            // Get the labels so far
            for (final Pair<List<IPosition>, List<IRule>> premise : tempDeps.get(depj)) {
              for (final Pair<List<IPosition>, List<IRule>> consequent : tempDeps.get(depk)) {
                /*
                 * Check that the sequence is tight
                 */

                // Avoid empty labels
                if (!(premise.getRight().isEmpty() || consequent.getRight().isEmpty())) {
                  final ILiteral preLit = premise.getRight().get(premise.getRight().size() - 1).getHead().iterator()
                      .next();
                  final ILiteral postLit = consequent.getRight().get(0).getBody().iterator().next();
                  if (RewritingUtils.mapsTo(ImmutableSet.of(postLit), ImmutableSet.of(preLit))) {
                    // if (RewritingUtils.resolves(premise.getRight().get(premise.getRight().size() - 1), consequent
                    // .getRight().get(0), new HashMap<IVariable, ITerm>())) {

                    /*
                     * Update the labels
                     */

                    // Construct the position dependency with corresponding label
                    final Pair<IPosition, IPosition> dep = ImmutablePair.of(depj.getLeft(), depk.getRight());

                    final List<IPosition> path = Lists.newLinkedList();
                    final List<IRule> label = Lists.newArrayList();
                    final Pair<List<IPosition>, List<IRule>> way = Pair.of(path, label);
                    path.addAll(premise.getLeft());
                    path.addAll(consequent.getLeft().subList(1, consequent.getLeft().size()));
                    label.addAll(premise.getRight());
                    label.addAll(consequent.getRight());

                    final Set<Pair<List<IPosition>, List<IRule>>> existingLabels = tempDeps.get(dep);
                    if (existingLabels == null) {
                      // the dependency was not present before, create a new set of labels.
                      final Set<Pair<List<IPosition>, List<IRule>>> labels = Sets.newLinkedHashSet();
                      labels.add(way);
                      closure.put(dep, labels);

                    } else {
                      /*
                       * The dependency already exists, check for loops and update the labels
                       */
                      // Check for loops
                      if (!containsLoop(way)) {
                        // The label is a new label
                        final Set<Pair<List<IPosition>, List<IRule>>> labels = Sets.newLinkedHashSet();
                        // Add all existing labels
                        labels.addAll(existingLabels);
                        // Add the new label
                        labels.add(way);

                        // Update the cover graph
                        closure.put(dep, labels);

                      }

                    }
                  }
                }
              }
            }
          }
        }
      }
      // LOGGER.trace(IOUtils.LINE_SEPARATOR + "CoverGraph: " + IOUtils.LINE_SEPARATOR
      // + DepGraphUtils.prettyPrintPositionGraph(closure));
    } while (!tempDeps.equals(closure));

    return closure;

  }

  private static boolean containsLoop(final Pair<List<IPosition>, List<IRule>> way) {

    final List<IRule> label = way.getRight();
    boolean loopingLabel = false;
    for (int i = 0; i < label.size() - 1; i++) {
      for (int j = 1; j <= i && i + j <= label.size(); j++) {
        if (label.subList(i - j, i).equals(label.subList(i, i + j))) {
          loopingLabel = true;
        }
      }
    }

    final List<IPosition> path = way.getLeft();
    boolean loopingPath = false;
    for (int i = 0; i < path.size() - 1; i++) {
      for (int j = 1; j <= i && i + j <= path.size(); j++) {
        if (path.subList(i - j, i).equals(path.subList(i, i + j))) {
          loopingPath = true;
        }
      }
    }

    return loopingLabel && loopingPath;
  }

  public static Map<IPosition, Set<IRule>> computeAffectedPositions(final List<IRule> tgds,
      final Map<Pair<IPosition, IPosition>, Set<Pair<List<IPosition>, List<IRule>>>> posDeps) {

    // get all declared existential positions in the set of TGDs (initial marking)
    final Map<IPosition, Set<IRule>> exPosSet = new HashMap<IPosition, Set<IRule>>();
    for (final IRule tgd : tgds) {
      final Set<IPosition> exPossInTGD = tgd.getExistentialPositions();
      for (final IPosition exPosInTGD : exPossInTGD) {
        if (exPosSet.containsKey(exPosInTGD)) {
          exPosSet.get(exPosInTGD).add(tgd);
        } else {
          exPosSet.put(exPosInTGD, Sets.newHashSet(tgd));
        }
      }
    }

    // compute inferred existential positions (marking propagation)
    for (final IPosition p : Sets.newHashSet(exPosSet.keySet())) {
      for (final Pair<IPosition, IPosition> posDep : posDeps.keySet()) {
        if (p.equals(posDep.getLeft())) {
          // add the new position to the set
          if (exPosSet.containsKey(posDep.getRight())) {
            exPosSet.get(posDep.getRight()).addAll(exPosSet.get(posDep.getLeft()));
          } else {
            exPosSet.put(posDep.getRight(), Sets.newHashSet(exPosSet.get(posDep.getLeft())));
          }
        }
      }
    }

    return exPosSet;
  }

}
