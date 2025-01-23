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

import org.deri.iris.api.builtins.IBuiltinAtom;
import org.deri.iris.api.factory.IBuiltinsFactory;
import org.deri.iris.api.terms.ITerm;

/**
 * <p>
 * Factory to create all sorts of builtins.
 * </p>
 * <p>
 * $Id: BuiltinsFactory.java,v 1.4 2007-10-12 12:40:58 bazbishop237 Exp $
 * </p>
 * 
 * @author Richard Pöttler, richard dot poettler at deri dot org
 * @version $Revision: 1.4 $
 */
public class BuiltinsFactory implements IBuiltinsFactory {

    private static final IBuiltinsFactory INSTANCE = new BuiltinsFactory();

    private BuiltinsFactory() {
	// this is a singelton
    }

    /**
     * Returns the singelton instance of this factory.
     * 
     * @return a instane of this factory
     */
    public static IBuiltinsFactory getInstance() {
	return INSTANCE;
    }

    public IBuiltinAtom createAddBuiltin(final ITerm t0, final ITerm t1,
	    final ITerm t2) {
	return new AddBuiltin(t0, t1, t2);
    }

    public IBuiltinAtom createSubtractBuiltin(final ITerm t0, final ITerm t1,
	    final ITerm t2) {
	return new SubtractBuiltin(t0, t1, t2);
    }

    public IBuiltinAtom createMultiplyBuiltin(final ITerm t0, final ITerm t1,
	    final ITerm t2) {
	return new MultiplyBuiltin(t0, t1, t2);
    }

    public IBuiltinAtom createDivideBuiltin(final ITerm t0, final ITerm t1,
	    final ITerm t2) {
	return new DivideBuiltin(t0, t1, t2);
    }

    public IBuiltinAtom createModulusBuiltin(final ITerm t0, final ITerm t1,
	    final ITerm t2) {
	return new ModulusBuiltin(t0, t1, t2);
    }

    public IBuiltinAtom createEqual(ITerm t0, ITerm t1) {
	return new EqualBuiltin(t0, t1);
    }

    public IBuiltinAtom createGreater(ITerm t0, ITerm t1) {
	return new GreaterBuiltin(t0, t1);
    }

    public IBuiltinAtom createGreaterEqual(ITerm t0, ITerm t1) {
	return new GreaterEqualBuiltin(t0, t1);
    }

    public IBuiltinAtom createLess(ITerm t0, ITerm t1) {
	return new LessBuiltin(t0, t1);
    }

    public IBuiltinAtom createLessEqual(ITerm t0, ITerm t1) {
	return new LessEqualBuiltin(t0, t1);
    }

    public IBuiltinAtom createUnequal(ITerm t0, ITerm t1) {
	return new NotEqualBuiltin(t0, t1);
    }

    public IBuiltinAtom createExactEqual(final ITerm t0, final ITerm t1) {
	return new ExactEqualBuiltin(t0, t1);
    }

    public IBuiltinAtom createNotExactEqual(final ITerm t0, final ITerm t1) {
	return new NotExactEqualBuiltin(t0, t1);
    }
}
