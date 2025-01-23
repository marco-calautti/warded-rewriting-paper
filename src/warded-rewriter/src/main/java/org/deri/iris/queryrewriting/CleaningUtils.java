package org.deri.iris.queryrewriting;

import java.util.HashSet;
import java.util.Set;

import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.factory.IBasicFactory;
import org.deri.iris.factory.Factory;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Iterators;

public class CleaningUtils {

  public static IRule cleanPrefix(final IRule r, final String prefix) {
    final IBasicFactory bf = Factory.BASIC;

    final Set<ILiteral> body = new HashSet<ILiteral>();
    for (final ILiteral l : r.getBody()) {
      final IPredicate p = l.getAtom().getPredicate();
      if (p.getPredicateSymbol().startsWith(prefix)) {
        body.add(bf.createLiteral(l.isPositive(),
            bf.createPredicate(p.getPredicateSymbol().replace(prefix, ""), p.getArity()), l.getAtom().getTuple()));
      } else {
        body.add(l);
      }
    }

    return NormalizationUtils.canonicalRenaming(bf.createRule(r.getHead(), body), "X");
  }

  public static void cleanRewriting(final QueryGraph queryGraph, final String[] auxPreds) {

    for (final IRule q : ImmutableSet.copyOf(queryGraph.getRules())) {
      boolean done = false;
      for (int i = 0; i < q.getBody().size() && !done; i++) {
        for (int j = 0; j < auxPreds.length && !done; j++)
          if (Iterators.get(q.getBody().iterator(), i).getAtom().getPredicate().getPredicateSymbol()
              .startsWith(auxPreds[j])) {
            queryGraph.removeRule(q);
            done = true;
          }
      }
    }

  }
}
