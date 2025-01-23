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
package org.deri.iris.terms.concrete;

import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.concrete.IIntegerTerm;

/**
 * <p>
 * Simple implementation of the IIntegerTerm.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler (richard dot poettler at deri dot at)
 * @author Holger Lausen
 * @version $Revision$
 */
public class IntegerTerm implements IIntegerTerm {
    /** integer to represent this datatype */
    private final Integer i;

    IntegerTerm(int z) {
	this.i = z;
    }

    public Integer getValue() {
	return i;
    }

    public boolean isGround() {
	return true;
    }

    public int compareTo(ITerm o) {
	if (o == null) {
	    return 1;
	}
	IntegerTerm it = (IntegerTerm) o;
	return i.compareTo(it.getValue());
    }

    public int hashCode() {
	return i;
    }

    public boolean equals(final Object o) {
	if (!(o instanceof IntegerTerm)) {
	    return false;
	}
	IntegerTerm it = (IntegerTerm) o;
	return i.equals(it.i);
    }

    /**
     * Simply returns the String representation of the holded int.
     * 
     * @return the String representation of the holded int
     */
    public String toString() {
	return i.toString();
    }
}
