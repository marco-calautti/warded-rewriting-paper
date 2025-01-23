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
package org.deri.iris.builtins;

import static org.deri.iris.factory.Factory.BASIC;

import java.util.Set;

import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.basics.EqualityTypeItem;

/**
 * <p>
 * Represents an add operation. At evaluation time there must be only one
 * variable left for computation, otherwise an exception will be thrown.
 * </p>
 * 
 * @author Richard Pöttler, richard dot poettler at deri dot org
 * @version $Revision: 1.15 $
 */
public class AddBuiltin extends ArithmeticBuiltin {
    /**
     * Constructor. Three terms must be passed to the constructor, otherwise an
     * exception will be thrown.
     * 
     * @param t
     *            the terms
     * @throws IllegalArgumentException
     *             if one of the terms is {@code null}
     * @throws IllegalArgumentException
     *             if the number of terms submitted is not 3
     * @throws IllegalArgumentException
     *             if t is <code>null</code>
     */
    public AddBuiltin(final ITerm... t) {
	super(PREDICATE, t);
    }

    protected ITerm computeMissingTerm(int missingTermIndex, ITerm[] terms) {
	switch (missingTermIndex) {
	case 0:
	    return BuiltinHelper.subtract(terms[2], terms[1]);

	case 1:
	    return BuiltinHelper.subtract(terms[2], terms[0]);

	default:
	    return BuiltinHelper.add(terms[0], terms[1]);
	}
    }

    public Set<EqualityTypeItem> getEqualityType() {
	return this.getEqualityType();
    }
    
    /** The predicate defining this built-in. */
    private static final IPredicate PREDICATE = BASIC.createPredicate("ADD", 3);
}
