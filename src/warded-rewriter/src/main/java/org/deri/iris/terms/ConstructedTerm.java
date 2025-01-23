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
package org.deri.iris.terms;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.deri.iris.api.terms.IConstructedTerm;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * <p>
 * Simple implementation of the IConstructedTerm.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler (richard dot poettler at deri dot at)
 * @author Darko Anicic, DERI Innsbruck
 * @version $Revision$
 */
public class ConstructedTerm implements IConstructedTerm {

  /**
   * A constructed term consist of a list of terms, where these terms can be constructed or non-constructed ones in a
   * general case.
   */
  private final List<ITerm> terms = new ArrayList<ITerm>();

  /** The function symbol itself. */
  private final String symbol;

  /**
   * Indicates if this object represents a ground term: 0 = not calculated, 1 = yes, 2 = no
   */
  private int mIsGround;

  /**
   * Constructor (for factory method).
   * 
   * @param symbol
   *          The function symbol
   * @param terms
   *          The terms for this function symbols expression.
   */
  ConstructedTerm(final String symbol, final Collection<ITerm> terms) {
    assert symbol != null : "The symbol must not be null";
    assert terms != null : "The terms must not be null";

    this.symbol = symbol;
    this.terms.addAll(terms);
  }

  @Override public String getFunctionSymbol() {
    return symbol;
  }

  @Override public List<ITerm> getParameters() {
    return terms;
  }

  @Override public List<ITerm> getValue() {
    return terms;
  }

  @Override public boolean isGround() {
    if (mIsGround == 0) {
      mIsGround = 1;
      for (final ITerm term : terms) {
        if (!term.isGround()) {
          mIsGround = 2;
          break;
        }
      }
    }

    return mIsGround == 1;
  }

  @Override public int hashCode() {
    return new HashCodeBuilder(257, 317).append(mIsGround).append(symbol).append(terms).toHashCode();
  }

  @Override public String toString() {
    final StringBuilder result = new StringBuilder();

    result.append(symbol).append('(');

    for (int i = 0; i < terms.size(); ++i) {
      if (i > 0) {
        result.append(',');
      }
      result.append(terms.get(i));
    }

    result.append(')');

    return result.toString();
  }

  @Override public boolean equals(final Object o) {
    if (this == o)
      return true;

    if (!(o instanceof ConstructedTerm))
      return false;

    final ConstructedTerm t = (ConstructedTerm) o;

    if (!symbol.equals(t.symbol))
      return false;

    return terms.equals(t.terms);
  }

  @Override public int compareTo(final ITerm o) {

    assert o instanceof IConstructedTerm : "Invalid argument type for ConstructedTerm.compare()";

    final IConstructedTerm t = (IConstructedTerm) o;

    int result = symbol.compareTo(t.getFunctionSymbol());
    if (result != 0)
      return result;

    final List<ITerm> tTerms = t.getValue();

    final int min = Math.min(terms.size(), tTerms.size());

    for (int iCounter = 0; iCounter < min; iCounter++) {
      result = terms.get(iCounter).compareTo(tTerms.get(iCounter));
      if (result != 0)
        return result;
    }
    return terms.size() - t.getValue().size();
  }

  @Override public Set<IVariable> getVariables() {
    final Set<IVariable> variables = new HashSet<IVariable>();
    for (final ITerm term : terms) {
      if (term instanceof IVariable) {
        variables.add((IVariable) term);
      } else if (term instanceof IConstructedTerm) {
        final IConstructedTerm childTerm = (IConstructedTerm) term;
        variables.addAll(childTerm.getVariables());
      }
    }
    return variables;
  }
}
