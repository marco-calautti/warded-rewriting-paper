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

import org.apache.commons.lang3.builder.HashCodeBuilder;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * <p>
 * Simple implementation of the IVariable.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler (richard dot poettler at deri dot at)
 * @version $Revision$
 */
public class Variable implements IVariable {

  private String name = "";

  Variable(final String name) {
    this.name = name;
  }

  @Override public boolean isGround() {
    return false;
  }

  @Override public int compareTo(final ITerm o) {
    if (o == null)
      return 1;

    if (!(o instanceof IVariable))
      return 1;

    final Variable v = (Variable) o;

    return name.compareTo(v.getValue());
  }

  @Override public int hashCode() {
    return new HashCodeBuilder(199, 241).append(name).toHashCode();
  }

  @Override public boolean equals(final Object o) {
    if (!(o instanceof Variable))
      return false;
    final Variable v = (Variable) o;
    return name.equals(v.name);
  }

  /**
   * Returns a String representation of this object. The subject of the string format is to change. An example return
   * value might be &quot;?date&quot;
   * 
   * @return the String representation
   */
  @Override public String toString() {
    return "?" + name;
  }

  @Override public String getValue() {
    return name;
  }
}
