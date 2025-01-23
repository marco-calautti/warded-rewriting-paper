/*
 * <IRIS+->
 * <Project Description>
 * 
 * Copyright (C) 2010 ICT Institute - Politecnico di Milano, Via Ponzio 34/5, 20133 Milan, Italy.
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

import org.deri.iris.api.basics.IPosition;
import org.deri.iris.terms.StringTerm;

/**
 * @author Giorgio Orsi <orsi AT elet DOT polimi DOT it> 
 *	   ICT Institute - Politecnico di Milano.
 * @version 0.1b
 *
 */
public class EqualityTypeItem {
    private IPosition lhs;
    private Object rhs;
    
    public EqualityTypeItem (IPosition lhs, Object rhs) {
	if (! ((rhs instanceof StringTerm) || (rhs instanceof IPosition)) )
	    throw new IllegalArgumentException("Invalid Equality Type Item: the right-hand-side "+ rhs + " is neither a constant nor a position.");
	this.lhs = lhs;
	this.rhs = rhs;
    }

    /**
     * @return the LHS
     */
    public IPosition getLHS() {
        return (lhs);
    }

    /**
     * @return the RHS
     */
    public Object getRHS() {
        return (rhs);
    }
    
    public String toString() {
	return ( lhs.toString() + " = " + rhs.toString() );
    }
}