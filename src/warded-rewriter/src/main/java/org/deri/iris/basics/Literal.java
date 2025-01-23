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
import java.util.List;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * <p>
 * Simple literal implementation.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler, richard dot poettler at deri dot org
 * @author Darko Anicic, DERI Innsbruck
 * @version $Revision$
 */
public class Literal implements ILiteral {

  private final boolean positive;

  private final IAtom atom;

  Literal(final IAtom atom) {
    this(true, atom);
  }

  Literal(final boolean positive, final IAtom atom) {
    this.atom = atom;
    this.positive = positive;
  }

  @Override public boolean isPositive() {
    return positive;
  }

  @Override public IAtom getAtom() {
    return atom;
  }

  @Override public int compareTo(final ILiteral oo) {
    final ILiteral o = oo;
    if (positive != o.isPositive() && positive)
      return 1;
    else if (positive != o.isPositive() && !positive)
      return -1;
    return atom.compareTo(o.getAtom());
  }

  @Override public int hashCode() {
    return new HashCodeBuilder(19, 83).append(atom).append(positive).toHashCode();
  }

  @Override public boolean equals(final Object o) {
    if (o == this)
      return true;
    if (!(o instanceof Literal))
      return false;
    final Literal l = (Literal) o;
    return atom.equals(l.atom) && positive == l.positive;
  }

  @Override public String toString() {
    return (positive ? "" : "!") + atom;
  }

  @Override public Set<IVariable> getVariables() {
    final Set<IVariable> vars = new HashSet<IVariable>();

    for (final ITerm t : getAtom().getTuple()) {
      if (t instanceof IVariable) {
        vars.add((IVariable) t);
      }
    }
    return vars;
  }


@Override public List<IVariable> hebaVariables() {
    final List<IVariable> vars = new ArrayList();

    for (final ITerm t : getAtom().getTuple()) {
      if (t instanceof IVariable) {
        vars.add((IVariable) t);
      }
    }
    return vars;
  }
}
