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

import java.util.Set;

import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.basics.EqualityTypeItem;
import org.deri.iris.factory.Factory;

/**
 * Builtin to compare two terms.
 */
public class LessEqualBuiltin extends BooleanBuiltin {
    /**
     * Constructor.
     * 
     * @param terms
     *            The terms, must be of length 2
     */
    public LessEqualBuiltin(ITerm... terms) {
	super(PREDICATE, terms);
    }

    protected boolean computeResult(ITerm[] terms) {
	return BuiltinHelper.lessEquals(terms[0], terms[1]);
    }

    /** The predicate defining this built-in. */
    private static final IPredicate PREDICATE = Factory.BASIC.createPredicate(
	    "LESS_EQUAL", 2);
    
    public Set<EqualityTypeItem> getEqualityType() {
	return this.getEqualityType();
    }
}
