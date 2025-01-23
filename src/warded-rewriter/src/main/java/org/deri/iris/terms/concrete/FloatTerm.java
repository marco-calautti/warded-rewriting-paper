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
import org.deri.iris.api.terms.concrete.IFloatTerm;
import org.deri.iris.utils.StandardFloatingPointComparator;

/**
 * <p>
 * Simple implementation of the IFloatTerm.
 * </p>
 * <p>
 * $Id$
 * </p>
 * 
 * @author Richard Pöttler (richard dot poettler at deri dot at)
 * @version $Revision$
 */
public class FloatTerm implements IFloatTerm {

    /** The float represented by this object */
    private final Float f;

    /**
     * Constructs a new float with the given value.
     * 
     * @param f
     *            the float value for this object
     * @throws NullPointerException
     *             if the float is null
     */
    FloatTerm(final float f) {
	this.f = f;
    }

    public Float getValue() {
	return f;
    }

    public boolean isGround() {
	return true;
    }

    public int compareTo(ITerm o) {
	if (o == null) {
	    return 1;
	}

	FloatTerm ft = (FloatTerm) o;
	return StandardFloatingPointComparator.getFloat().compare(f, ft.f);
    }

    public int hashCode() {
	return f.hashCode();
    }

    public boolean equals(Object o) {
	if (!(o instanceof FloatTerm)) {
	    return false;
	}
	FloatTerm ft = (FloatTerm) o;
	// Use the floating point comparer to allow for round-off errors.
	return StandardFloatingPointComparator.getFloat().equals(f, ft.f);
    }

    public String toString() {
	return f.toString();
    }
}
