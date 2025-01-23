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

import java.util.Arrays;
import java.util.Collection;

import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.factory.ITermFactory;
import org.deri.iris.api.terms.IConstructedTerm;
import org.deri.iris.api.terms.IFreshTerm;
import org.deri.iris.api.terms.IStringTerm;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * @author richi
 * @author Giorgio Orsi, Politecnico di Milano (orsi at elet dot polimi dot it)
 * 
 */
public class TermFactory implements ITermFactory {

    private static final ITermFactory FACTORY = new TermFactory();

    private static int freshTerms;
    private static int dontCareVariables;

    private TermFactory() {
	freshTerms = 0;
	dontCareVariables = 0;
    }

    public IConstructedTerm createConstruct(String name, Collection<ITerm> terms) {
	return new ConstructedTerm(name, terms);
    }

    public IConstructedTerm createConstruct(String name, ITerm... terms) {
	return createConstruct(name, Arrays.asList(terms));
    }

    public IStringTerm createString(String arg) {
	if (arg != null)
	    return new StringTerm(arg);
	else
	    return new StringTerm("nil");
    }

    
    public IVariable createVariable(String name) {
	if ( name.compareTo("_") == 0 ) {
	    dontCareVariables++;
	    return ( new AnyTerm( dontCareVariables ) );
	} else
	    return ( new Variable( name ) );
    }

    public static ITermFactory getInstance() {
	return FACTORY;
    }

    public IFreshTerm createFreshTerm(IPredicate pred, int posIndex, Collection<ITerm> terms) {

	// create the "fresh" term
	freshTerms++;
	IFreshTerm fresh = new Null(pred, posIndex, freshTerms, terms);

	return (fresh);
    }

}
