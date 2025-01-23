/**
 * 
 */
package org.deri.iris.queryrewriting;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.factory.Factory;
import org.deri.iris.queryrewriting.caching.RenamingCache;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;

/**
 * @author jd
 */
public class NormalizationUtils {

  public static Set<IRule> canonicalRenaming(final String var, final Set<IRule> s) {
    final Set<IRule> out = Sets.newHashSet();
    for (final IRule r : s) {
      out.add(canonicalRenaming(r, var));
    }
    return s;
  }

  public static IRule canonicalRenaming(final IRule r, final String var) {

    // Reporting and cache check.
    if (RenamingCache.inCache(r, var)) {
      return RenamingCache.getRenamed(r, var);
    }

    final long renamingTime = System.currentTimeMillis();

    final Map<IVariable, IVariable> map = new HashMap<IVariable, IVariable>();
    final Collection<ILiteral> freshHeadLiterals = canonicalRenaming(r.getHead(), var, map);
    final Collection<ILiteral> freshBodyLiterals = canonicalRenaming(r.getBody(), var, map);

    final IRule renamed = Factory.BASIC.createRule(freshHeadLiterals, freshBodyLiterals);

    // Reporting and caching.
    RenamingCache.cache(r, var, renamed);

    return renamed;
  }

  public static Collection<ILiteral> canonicalRenaming(final Collection<ILiteral> literals, final String var) {
    return canonicalRenaming(literals, var, new HashMap<IVariable, IVariable>());
  }

  public static Collection<ILiteral> canonicalRenaming(final Collection<ILiteral> literals, final String var,
      final Map<IVariable, IVariable> map) {

    final List<ILiteral> lits = Lists.newArrayList(literals);
    Collections.sort(lits);
    final List<ILiteral> renamedLiterals = Lists.newArrayList();

    for (final ILiteral l : lits) {
      final List<ITerm> freshTerms = new ArrayList<ITerm>();
      for (final ITerm t : l.getAtom().getTuple()) {
        if (t instanceof IVariable)
          if (map.containsKey(t)) {
            // ordinately substitute the variable with the corresponding fresh variable.
            freshTerms.add(map.get(t));
          } else {
            // substitute the current variable with a fresh variable
            final IVariable v = Factory.TERM.createVariable(var + map.size());
            freshTerms.add(v);
            map.put((IVariable) t, v);
          }
        else {
          freshTerms.add(t);
        }
      }
      renamedLiterals.add(Factory.BASIC.createLiteral(l.isPositive(), l.getAtom().getPredicate(),
          Factory.BASIC.createTuple(freshTerms)));
    }
    Collections.sort(renamedLiterals);
    return renamedLiterals;
  }

  public static Set<IRule> normalizeHead(final IRule rule) {
    final Set<IRule> normalized = Sets.newHashSet();

    if (rule.getHead().size() == 1) {
      normalized.add(rule);
    } else {
      // Multiple head atoms
      final Set<IVariable> exVars = rule.getExistentialVariables();
      if (exVars.isEmpty()) {
        // No existential variables --> safe to split
        final Collection<ILiteral> head = rule.getHead();
        for (final ILiteral headLit : head) {
          normalized.add(Factory.BASIC.createRule(ImmutableList.of(headLit), rule.getBody()));
        }
      } else {
        /*
         * Need for auxiliary predicates
         */
        for (final IVariable exVar : exVars) {
          final Set<ILiteral> litsWithVar = Sets.newHashSet();
          for (final ILiteral headLit : rule.getHead()) {
            if (headLit.getAtom().getTuple().contains(exVar)) {
              litsWithVar.add(headLit);
            }
          }
        }
      }
    }
    return normalized;
  }

}
