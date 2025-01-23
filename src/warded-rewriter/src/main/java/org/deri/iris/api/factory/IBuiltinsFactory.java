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
package org.deri.iris.api.factory;

import org.deri.iris.api.builtins.IBuiltinAtom;
import org.deri.iris.api.terms.ITerm;

/**
 * <p>
 * An interface that can be used to create set of built-ins supported by this
 * engine.
 * </p>
 * <p>
 * $Id: IBuiltInsFactory.java,v 1.7 2007-10-12 13:00:42 bazbishop237 Exp $
 * </p>
 * 
 * @author Darko Anicic, DERI Innsbruck
 * @author Richard Pöttler, richard dot poettler at deri dot org
 * @date 17.03.2006 11:55:35
 * @version $Revision: 1.7 $
 */
public interface IBuiltinsFactory {

    /**
     * Creates an add builtin.
     * 
     * @param t0
     *            the first summand
     * @param t1
     *            the second summand
     * @param t2
     *            the sum
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createAddBuiltin(final ITerm t0,
	    final ITerm t1, final ITerm t2);

    /**
     * Creates a subtract builtin.
     * 
     * @param t0
     *            the minuend
     * @param t1
     *            the subtrahend
     * @param t2
     *            the difference
     * @return the constructed builtin
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createSubtractBuiltin(final ITerm t0,
	    final ITerm t1, final ITerm t2);

    /**
     * Creates a multiply builtin.
     * 
     * @param t0
     *            the first factor
     * @param t1
     *            the second factor
     * @param t2
     *            the product
     * @return the constructed builtin
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createMultiplyBuiltin(final ITerm t0,
	    final ITerm t1, final ITerm t2);

    /**
     * Creates a divide builtin.
     * 
     * @param t0
     *            the dividend
     * @param t1
     *            the diviso
     * @param t2
     *            the quotient
     * @return the constructed builtin
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createDivideBuiltin(final ITerm t0,
	    final ITerm t1, final ITerm t2);

    /**
     * Creates a modulus builtin.
     * 
     * @param t0
     *            the numerator
     * @param t1
     *            the denominator
     * @param t2
     *            the result
     * @return the constructed builtin
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createModulusBuiltin(final ITerm t0,
	    final ITerm t1, final ITerm t2);

    /**
     * Creates an equal builtin.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createEqual(final ITerm t0, final ITerm t1);

    /**
     * Creates an unequal builtin.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createUnequal(final ITerm t0, final ITerm t1);

    /**
     * Create an EXACT_EQUAL built-in.
     * 
     * @param t0
     *            The first term.
     * @param t1
     *            The second term.
     * @return The built-in instance
     */
    IBuiltinAtom createExactEqual(final ITerm t0, final ITerm t1);

    /**
     * Create a NOT_EXACT_EQUAL built-in.
     * 
     * @param t0
     *            The first term.
     * @param t1
     *            The second term.
     * @return The built-in instance
     */

    IBuiltinAtom createNotExactEqual(final ITerm t0, final ITerm t1);

    /**
     * Creates a less builtin.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createLess(final ITerm t0, final ITerm t1);

    /**
     * Creates an less-equal builtin.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createLessEqual(final ITerm t0, final ITerm t1);

    /**
     * Creates a greater builtin.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createGreater(final ITerm t0, final ITerm t1);

    /**
     * Creates a greater-equal builtin.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return the builtin
     * @throws NullPointerException
     *             if any of the terms is <code>null</code>
     */
    public abstract IBuiltinAtom createGreaterEqual(final ITerm t0,
	    final ITerm t1);
}
