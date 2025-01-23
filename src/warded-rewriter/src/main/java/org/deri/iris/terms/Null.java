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

import java.util.Collection;

import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.terms.IFreshTerm;
import org.deri.iris.api.terms.ITerm;

/**
 * <p>
 * The Concrete implementation of a "fresh" term.
 * </p>
 * @author Giorgio Orsi, Politecnico di Milano (orsi at elet dot polimi dot it)
 * @date 01.04.2009 10:57:00
 */
public class Null extends ConstructedTerm implements IFreshTerm {

	private final int freshTermIndex;

	Null(final IPredicate pred, final int posIndex, final int freshTermIndex, final Collection<ITerm> terms) {

		super("skf_" + pred.getPredicateSymbol() + "[" + posIndex + "]", terms);
		this.freshTermIndex = freshTermIndex;

	}

	@Override
	public int hashCode() {
		return super.hashCode();
	}

	@Override
	public String toString() {

		return ("u_" + freshTermIndex);

	}

}
