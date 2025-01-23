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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.IPosition;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.ITerm;

/**
 * <p>
 * A simple Atom implementation.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler (richard dot poettler at deri dot at)
 * @author Darko Anicic, DERI Innsbruck
 * @version $Revision$
 */
public class Atom implements IAtom {

  private final IPredicate predicate;
  private final Set<EqualityTypeItem> eqType;
  private final ITuple tuple;

  Atom(final IPredicate predicate, final ITuple tuple) {
    if (predicate == null || tuple == null)
      throw new IllegalArgumentException("The parameters must not be null");
    if (predicate.getArity() != tuple.size())
      throw new IllegalArgumentException("Cannot create an atom when"
          + " a tuple's arity does not match the predicate's arity.");
    this.predicate = predicate;
    this.tuple = tuple;
    eqType = computeEqualityType(tuple);
  }

  /**
   * @param tuple
   *          the tuple of this atom
   * @return constructs the equality type of this atom
   */
  private Set<EqualityTypeItem> computeEqualityType(final ITuple tuple) {
    final Set<EqualityTypeItem> out = new HashSet<EqualityTypeItem>();

    for (int i = 0; i < tuple.size() - 1; i++)
      if (tuple.get(i).isGround()) {
        out.add(new EqualityTypeItem(new Position(predicate.getPredicateSymbol(), i + 1), tuple.get(i)));
      } else {
        for (int j = i + 1; j < tuple.size(); j++)
          if (tuple.get(i).compareTo(tuple.get(j)) == 0) {
            out.add(new EqualityTypeItem(new Position(predicate.getPredicateSymbol(), i + 1), new Position(predicate
                .getPredicateSymbol(), j + 1)));
          }
      }
    return out;
  }

  @Override public IPredicate getPredicate() {
    return predicate;
  }

  public List<IPosition> getPositions(final ITerm t) {
    final List<IPosition> pos = new ArrayList<IPosition>();

    final Iterator<ITerm> tIt = getTuple().iterator();
    int i = 0;
    while (tIt.hasNext()) {
      final ITerm curTerm = tIt.next();
      if (curTerm.compareTo(t) == 0) {
        pos.add(new Position(getPredicate().getPredicateSymbol(), ++i));
      }
    }
    return pos;
  }

  @Override public ITuple getTuple() {
    return tuple;
  }

  @Override public Set<EqualityTypeItem> getEqualityType() {
    return eqType;
  }

  @Override public boolean isGround() {
    return tuple.isGround();
  }

  @Override public int compareTo(final IAtom o) {
    int res = 0;
    if ((res = predicate.compareTo(o.getPredicate())) != 0)
      return res;
    if ((res = tuple.compareTo(o.getTuple())) != 0)
      return res;
    return 0;
  }

  @Override public int hashCode() {
    return new HashCodeBuilder(29, 103).append(predicate).append(tuple).toHashCode();
  }

  @Override public boolean equals(final Object o) {
    if (this == o)
      return true;
    if (!(o instanceof Atom))
      return false;
    final Atom a = (Atom) o;

    return predicate.equals(a.predicate) && tuple.equals(a.getTuple());
  }

  @Override public String toString() {
    final StringBuilder buffer = new StringBuilder();
    buffer.append(predicate);
    buffer.append(tuple);

    return buffer.toString();
  }

  @Override public boolean isBuiltin() {
    return false;
  }
}
