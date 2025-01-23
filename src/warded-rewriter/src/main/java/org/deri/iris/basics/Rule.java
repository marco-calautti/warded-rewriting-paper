/*
 * Integrated Rule Inference System (IRIS):
 * An extensible rule inference system for datalog with extensions.
 * 
 * Copyright (C) 2008 Semantic Technology Institute (STI) Innsbruck, 
 * University of Innsbruck, Technikerstrasse 21a, 6020 Innsbruck, Austria.
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
package org.deri.iris.basics;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;

import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPosition;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.terms.StringTerm;
import org.deri.iris.utils.UniqueList;

import com.google.common.collect.Sets;

/**
 * <p>
 * Represents a datalog rule.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler (richard dot poettler at deri dot at)
 * @author Giorgio Orsi (orsi at elet dot polimi dot it)
 * @version $Revision$
 */
public class Rule implements IRule {

  private final Set<ILiteral> head;

  private final Set<ILiteral> body;

  Rule(final Collection<ILiteral> head, final Collection<ILiteral> body) {
    if (head == null)
      throw new IllegalArgumentException("The head must not be null");
    if (head.contains(null))
      throw new IllegalArgumentException("The head must not contain null");
    if (body == null)
      throw new IllegalArgumentException("The body must not be null");
    if (body.contains(null))
      throw new IllegalArgumentException("The body must not contain null");
    this.head = Sets.newHashSet(head);
    this.body = Sets.newHashSet(body);
  }

  @Override public Set<ILiteral> getHead() {
    return head;
  }

  @Override public Set<ILiteral> getBody() {
    return body;
  }

  @Override public boolean isRectified() {
    return false;
  }

  @Override public int hashCode() {
    final HashCodeBuilder builder = new HashCodeBuilder(17, 37);
    for (final ILiteral l : getAllLiterals()) {
      builder.append(l);
    }
    return builder.toHashCode();
  }

  @Override public boolean equals(final Object o) {
    if (o == this)
      return true;

    if (!(o instanceof IRule))
      return false;

    final IRule r = (IRule) o;

    if (r.getHead().size() != head.size() || r.getBody().size() != body.size())
      return false;

    return head.equals(r.getHead()) && body.equals(r.getBody());
  }

  @Override public Set<IPredicate> getPredicates() {
    final Set<IPredicate> predicates = new HashSet<IPredicate>();

    predicates.addAll(getBodyPredicates());
    predicates.addAll(getHeadPredicates());

    return predicates;
  }

  @Override public Set<IPredicate> getBodyPredicates() {
    final Set<IPredicate> predicates = new HashSet<IPredicate>();

    for (final ILiteral l : getBody()) {
      predicates.add(l.getAtom().getPredicate());
    }

    return predicates;
  }

  @Override public Set<IPredicate> getHeadPredicates() {
    final Set<IPredicate> predicates = new HashSet<IPredicate>();

    for (final ILiteral l : getHead()) {
      predicates.add(l.getAtom().getPredicate());
    }

    return predicates;
  }

  @Override public String toString() {
    final StringBuilder buffer = new StringBuilder();
    boolean first = true;
    for (final ILiteral l : head) {
      if (first) {
        first = false;
      } else {
        buffer.append(", ");
      }
      buffer.append(l);
    }

    buffer.append(" :- ");

    first = true;
    for (final ILiteral l : body) {
      if (first) {
        first = false;
      } else {
        buffer.append(", ");
      }
      buffer.append(l);
    }
    buffer.append('.');
    return buffer.toString();
  }

  /*
   * (non-Javadoc)
   * 
   * @see org.deri.iris.api.basics.IRule#getBodyVariables()
   */
  @Override public Set<IVariable> getBodyVariables() {
    final Set<IVariable> res = new HashSet<IVariable>();

    for (final ILiteral l : getBody()) {
      for (final ITerm t : l.getAtom().getTuple()) {
        if (t instanceof IVariable && !res.contains(t)) {
          res.add((IVariable) t);
        }
      }
    }
    return res;
  }

  @Override public Set<IVariable> getHeadVariables() {
    final Set<IVariable> res = new HashSet<IVariable>();

    for (final ILiteral l : getHead()) {
      for (final ITerm t : l.getAtom().getTuple()) {
        if (t instanceof IVariable && !res.contains(t)) {
          res.add((IVariable) t);
        }
      }
    }
    return res;
  }

  @Override public Set<IVariable> getExistentialVariables() {
    final Set<IVariable> res = new HashSet<IVariable>();

    for (final IVariable v : getHeadVariables()) {
      if (!getBodyVariables().contains(v)) {
        res.add(v);
      }
    }
    return res;
  }

  @Override public Set<IVariable> getFrontierVariables() {
    final Set<IVariable> res = new HashSet<IVariable>();

    for (final IVariable v : getHeadVariables()) {
      if (getBodyVariables().contains(v)) {
        res.add(v);
      }
    }
    return res;
  }

  /*
   * (non-Javadoc)
   * 
   * @see org.deri.iris.api.basics.IRule#getTermBodyPositions(org.deri.iris.api.terms.ITerm)
   */
  @Override public Set<IPosition> getTermBodyPositions(final ITerm term) {
    final Set<IPosition> res = new LinkedHashSet<IPosition>();

    for (final ILiteral l : getBody()) {
      final IAtom a = l.getAtom();

      int i = 0;
      for (final ITerm t : a.getTuple()) {
        i++;
        if (t.compareTo(term) == 0) {
          res.add(new Position(a.getPredicate().getPredicateSymbol(), i));
        }
      }
    }
    return res;
  }

  /*
   * (non-Javadoc)
   * 
   * @see org.deri.iris.api.basics.IRule#getTermHeadPositions(org.deri.iris.api.terms.ITerm)
   */
  @Override public Set<IPosition> getTermHeadPositions(final ITerm term) {
    final Set<IPosition> res = new LinkedHashSet<IPosition>();

    for (final ILiteral l : getHead()) {
      final IAtom a = l.getAtom();

      int i = 0;
      for (final ITerm t : a.getTuple()) {
        i++;
        if (t.compareTo(term) == 0) {
          res.add(new Position(a.getPredicate().getPredicateSymbol(), i));
        }
      }
    }
    return res;
  }

  /**
   * Retrieves all the terms that appear in a position p in the query
   * 
   * @param p
   *          the position in the query
   * @return the set of terms in position p
   */
  @Override public Set<ITerm> getBodyTerms(final Set<IPosition> positions) {
    final Set<ITerm> terms = new HashSet<ITerm>();

    for (final IPosition p : positions) {
      terms.addAll(getBodyTerms(p));
    }

    return terms;
  }

  /**
   * Retrieves all variables appear in given positions in the rule.
   * 
   * @param positions
   *          the position in the rule.
   * @return the set of terms in given positions.
   */
  @Override public Set<IVariable> getBodyVariables(final Set<IPosition> positions) {
    final Set<IVariable> vars = new HashSet<IVariable>();

    for (final IPosition p : positions) {
      vars.addAll(getBodyVariables(p));
    }

    return vars;
  }

  /**
   * Retrieves all variables appear in given positions in the rule.
   * 
   * @param positions
   *          the position in the rule.
   * @return the set of terms in given positions.
   */
  @Override public Set<IVariable> getHeadVariables(final Set<IPosition> positions) {
    final Set<IVariable> vars = new HashSet<IVariable>();

    for (final IPosition p : positions) {
      vars.addAll(getHeadVariables(p));
    }

    return vars;
  }

  /**
   * Retrieves all the terms that appear in a position p in the body of the rule
   * 
   * @param p
   *          the position in the query
   * @return the set of terms in position p
   */
  @Override public Set<ITerm> getBodyTerms(final IPosition p) {
    final Set<ITerm> terms = new HashSet<ITerm>();

    for (final ILiteral l : getBody()) {
      int i = 0;
      for (final ITerm t : l.getAtom().getTuple()) {
        i++;
        if (l.getAtom().getPredicate().getPredicateSymbol().compareTo(p.getPredicate()) == 0 && i == p.getPosition()) {
          terms.add(t);
        }
      }
    }

    return terms;
  }

  /**
   * Retrieves all variables appearing in a position p in the body of the rule
   * 
   * @param p
   *          the position in the rule
   * @return the set of variables in position p
   */
  @Override public Set<IVariable> getBodyVariables(final IPosition p) {
    final Set<IVariable> vars = new HashSet<IVariable>();

    for (final ILiteral l : getBody()) {
      int i = 0;
      for (final ITerm t : l.getAtom().getTuple()) {
        i++;
        final IPosition cmp = new Position(l.getAtom().getPredicate().getPredicateSymbol(), i);
        if (cmp.equals(p) && t instanceof IVariable) {
          vars.add((IVariable) t);
        }
      }
    }

    return vars;
  }

  /**
   * Retrieves all variables appearing in a position p in the body of the rule
   * 
   * @param p
   *          the position in the rule
   * @return the set of variables in position p
   */
  @Override public Set<IVariable> getHeadVariables(final IPosition p) {
    final Set<IVariable> vars = new HashSet<IVariable>();

    for (final ILiteral l : getHead()) {
      int i = 0;
      for (final ITerm t : l.getAtom().getTuple()) {
        i++;
        final IPosition cmp = new Position(l.getAtom().getPredicate().getPredicateSymbol(), i);
        if (cmp.equals(p) && t instanceof IVariable) {
          vars.add((IVariable) t);
        }
      }
    }

    return vars;
  }

  public Set<IPosition> getPositions() {
    final Set<IPosition> p = new HashSet<IPosition>();

    for (final ILiteral l : getBody()) {
      for (int i = 0; i < l.getAtom().getTuple().size(); i++) {
        p.add(new Position(l.getAtom().getPredicate().getPredicateSymbol(), i));
      }
    }

    return p;
  }

  @Override public Set<IPosition> getBodyPositions(final Collection<? extends ITerm> terms) {
    return getPositions(terms, getBody());
  }

  @Override public Set<IPosition> getHeadPositions(final Collection<? extends ITerm> terms) {
    return getPositions(terms, getHead());
  }

  private Set<IPosition> getPositions(final Collection<? extends ITerm> terms, final Collection<ILiteral> literals) {
    final Set<IPosition> positions = Sets.newHashSet();

    for (final ITerm t : terms) {
      positions.addAll(getPositions(t, literals));
    }

    return positions;
  }

  private Set<IPosition> getPositions(final ITerm t, final Collection<ILiteral> literals) {
    final Set<IPosition> positions = Sets.newHashSet();

    for (final ILiteral l : literals) {
      positions.addAll(getPositions(t, l));
    }

    return positions;
  }

  private Set<IPosition> getPositions(final ITerm t, final ILiteral l) {
    final Set<IPosition> positions = Sets.newHashSet();

    final List<ITerm> terms = l.getAtom().getTuple();
    final String pred = l.getAtom().getPredicate().getPredicateSymbol();
    for (int i = 1; i <= terms.size(); i++) {
      if (terms.get(i - 1).equals(t)) {
        positions.add(new Position(pred, i));
      }
    }
    return positions;
  }

  /**
   * Returns all the positions in the query atoms that correspond to the positions of existential variables in the set
   * of rules given as parameter. Each list of positions corresponds to one TGD with existential Variables.
   * 
   * @param rules
   *          The set of rules to be considered
   * @return the set of existential positions in this query considering each rule separately.
   */
  @Override public List<IPosition> getExistentialPositions(final IRule r) {

    final List<IPosition> exPos = new UniqueList<IPosition>();

    final Iterator<IVariable> vIt = r.getExistentialVariables().iterator();
    while (vIt.hasNext()) {
      final IVariable v = vIt.next();

      final Iterator<IPosition> pIt = r.getTermHeadPositions(v).iterator();
      while (pIt.hasNext()) {
        final IPosition p = pIt.next();

        final Iterator<ILiteral> lIt = getBody().iterator();
        while (lIt.hasNext()) {
          final IAtom a = lIt.next().getAtom();
          if (a.getPredicate().equals(p.getPredicate())) {
            exPos.add(p);
          }
        }
      }
    }

    return exPos;
  }

  /**
   * Returns all the existential positions in this rule.
   */
  @Override public Set<IPosition> getExistentialPositions() {

    final Set<IPosition> exPos = new LinkedHashSet<IPosition>();

    for (final IVariable v : getExistentialVariables()) {
      exPos.addAll(this.getPositions(v));
    }

    return exPos;
  }

  @Override public Set<IPosition> getPositions(final ITerm v) {

    final Set<IPosition> res = new HashSet<IPosition>();

    for (final ILiteral l : getBody()) {
      int pos = 0;
      for (final ITerm t : l.getAtom().getTuple()) {
        pos++;
        if (t.equals(v)) {
          res.add(new Position(l.getAtom().getPredicate().getPredicateSymbol(), pos));
        }
      }
    }
    for (final ILiteral l : getHead()) {
      int pos = 0;
      for (final ITerm t : l.getAtom().getTuple()) {
        pos++;
        if (t.equals(v)) {
          res.add(new Position(l.getAtom().getPredicate().getPredicateSymbol(), pos));
        }
      }
    }
    return res;
  }

  @Override public boolean isShared(final ITerm t) {

    if (t instanceof StringTerm)
      return true;
    int i = 0;
    for (final ILiteral l : getBody()) {
      for (final ITerm term : l.getAtom().getTuple()) {
        if (term.equals(t)) {
          i++;
        }
        if (i > 1)
          return true;
      }
    }
    for (final ILiteral l : getHead()) {
      for (final ITerm term : l.getAtom().getTuple()) {
        if (term.equals(t))
          return true;
      }
    }
    return false;
  }

  @Override public Set<IVariable> getAllVariables() {

    final Set<IVariable> vars = Sets.newHashSet();
    vars.addAll(getHeadVariables());
    vars.addAll(getBodyVariables());

    return vars;
  }

  @Override public Set<IPosition> getRulePositions() {

    // Get the head positions
    final Set<IPosition> positions = getHeadPositions();

    // Get the body positions
    positions.addAll(getBodyPositions());

    return positions;
  }

  @Override public Set<IPosition> getHeadPositions() {
    return getPositions(getHead());
  }

  @Override public Set<IPosition> getBodyPositions() {
    return getPositions(getBody());
  }

  private Set<IPosition> getPositions(final Collection<ILiteral> literals) {
    final Set<IPosition> positions = Sets.newLinkedHashSet();

    // Get positions in literal.
    for (final ILiteral l : literals) {
      final IAtom a = l.getAtom();

      for (int i = 1; i <= a.getTuple().size(); i++) {
        positions.add(new Position(a.getPredicate().getPredicateSymbol(), i));
      }
    }
    return positions;
  }

  @Override public Set<ILiteral> getAllLiterals() {
    final Set<ILiteral> lits = new HashSet<ILiteral>();
    lits.addAll(body);
    lits.addAll(head);

    return lits;
  }
}