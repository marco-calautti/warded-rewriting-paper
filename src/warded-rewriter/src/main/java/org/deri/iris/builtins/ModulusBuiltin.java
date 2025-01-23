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

import org.deri.iris.EvaluationException;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.basics.EqualityTypeItem;

/**
 * Represents a modulus operation. At evaluation time there must be either: a) 1
 * unknown variable for computation, OR b) no unknown variables, in which case
 * the evaluation is just a check that term0 % term1 = term2
 */
public class ModulusBuiltin extends ArithmeticBuiltin {
    /**
     * Constructor.
     * 
     * @param terms
     *            the terms. There must always be 3 terms.
     */
    public ModulusBuiltin(final ITerm... terms) {
	super(PREDICATE, terms);
    }

    protected ITerm computeMissingTerm(int missingTermIndex, ITerm[] terms)
	    throws EvaluationException {
	switch (missingTermIndex) {
	case 0:
	    return terms[2]; // +n x terms[ 1 ], where n >= 0

	case 1:
	    if (BuiltinHelper.less(terms[2], terms[0]))
		return BuiltinHelper.subtract(terms[0], terms[2]);

	    if (BuiltinHelper.equal(terms[2], terms[0]))
		return BuiltinHelper.increment(terms[2]);

	    // x % y = z, does not make sense when when x < z
	    return null;

	default:
	    return BuiltinHelper.modulus(terms[0], terms[1]);
	}
    }

    /** The predicate defining this built-in. */
    private static final IPredicate PREDICATE = BASIC.createPredicate(
	    "MODULUS", 3);
    
    public Set<EqualityTypeItem> getEqualityType() {
	return this.getEqualityType();
    }
}
