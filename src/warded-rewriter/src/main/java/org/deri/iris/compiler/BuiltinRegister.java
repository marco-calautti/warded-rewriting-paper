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
package org.deri.iris.compiler;

import java.util.HashMap;
import java.util.Map;

import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.builtins.IBuiltinAtom;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.factory.Factory;

/**
 * <p>
 * Holds the registry of built-in atoms that the parser can use to translate
 * predicates to built-ins as the logic program is parsed.
 * </p>
 * <p>
 * Before a built-in can be recognized by the parser it must first be registered
 * with the associated BuiltinRegister. The BuiltinRegister uses instances of
 * the built-ins to get their predicate names and their class instances. The
 * BuiltinRegister basically holds a map between predicate symbol and class
 * instance. This class initialises itself with all the standard IRIS built-ins.
 * </p>
 * <p>
 * To add more, simply call registerBuiltin() with an instance of the new
 * built-in type.
 * </p>
 * <p>
 * To unregister a built-in call unregisterBuiltin(). However, beware that
 * unregistering any of the standard built-ins can lead to undefined behaviour.
 * </p>
 */
public final class BuiltinRegister {

    /**
     * Holding all the information about the built-ins.
     * <ul>
     * <li>key: the name (predicate symbol of the built-in)</li>
     * <li>value: the RegisterEntry containing the information about the
     * built-in</li>
     * </ul>
     */
    private final Map<String, RegisterEntry> reg = new HashMap<String, RegisterEntry>();

    /**
     * Constructs a new built-in register and register all the standard IRIS
     * built-ins.
     */
    public BuiltinRegister() {
	ITerm t1 = Factory.TERM.createVariable("a");
	ITerm t2 = Factory.TERM.createVariable("b");
	ITerm t3 = Factory.TERM.createVariable("c");
	registerBuiltin(new org.deri.iris.builtins.AddBuiltin(t1, t2, t3));

	registerBuiltin(new org.deri.iris.builtins.SubtractBuiltin(t1, t2, t3));
	registerBuiltin(new org.deri.iris.builtins.MultiplyBuiltin(t1, t2, t3));
	registerBuiltin(new org.deri.iris.builtins.DivideBuiltin(t1, t2, t3));
	registerBuiltin(new org.deri.iris.builtins.ModulusBuiltin(t1, t2, t3));

	registerBuiltin(new org.deri.iris.builtins.EqualBuiltin(t1, t2));
	registerBuiltin(new org.deri.iris.builtins.NotEqualBuiltin(t1, t2));
	registerBuiltin(new org.deri.iris.builtins.ExactEqualBuiltin(t1, t2));
	registerBuiltin(new org.deri.iris.builtins.NotExactEqualBuiltin(t1, t2));

	registerBuiltin(new org.deri.iris.builtins.LessBuiltin(t1, t2));
	registerBuiltin(new org.deri.iris.builtins.LessEqualBuiltin(t1, t2));
	registerBuiltin(new org.deri.iris.builtins.GreaterBuiltin(t1, t2));
	registerBuiltin(new org.deri.iris.builtins.GreaterEqualBuiltin(t1, t2));

	registerBuiltin(new org.deri.iris.builtins.IsBase64BinaryBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsBooleanBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsDateBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsDateTimeBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsDecimalBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsDoubleBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsDurationBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsFloatBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsGDayBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsGMonthBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsGMonthDayBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsGYearBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsGYearMonthBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsHexBinaryBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsIntegerBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsIriBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsNumericBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsSqNameBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsStringBuiltin(t1));
	registerBuiltin(new org.deri.iris.builtins.IsTimeBuiltin(t1));

	registerBuiltin(new org.deri.iris.builtins.SameTypeBuiltin(t1, t2));

	registerBuiltin(new org.deri.iris.builtins.TrueBuiltin());
	registerBuiltin(new org.deri.iris.builtins.FalseBuiltin());

	registerBuiltin(new org.deri.iris.builtins.RegexBuiltin(t1,
		Factory.TERM.createString("")));
    }

    /**
     * Registers a single built-in. Already registered built-ins will be
     * overwritten.
     * 
     * @param builtin
     *            an instance of the built-in to register
     * @throws IllegalArgumentException
     *             if the class is <code>null</code>
     */
    public void registerBuiltin(IBuiltinAtom builtin) {
	if (builtin == null)
	    throw new IllegalArgumentException(
		    "The builtin atom must not be null");

	final Class<?> c = builtin.getClass();

	final RegisterEntry ent = new RegisterEntry(c, builtin.getPredicate());
	reg.put(ent.getName(), ent);
    }

    /**
     * De-registers a single built-in.
     * 
     * @param builtin
     *            an instance of the built-in to de-register
     * @throws IllegalArgumentException
     *             if the class is <code>null</code>
     */
    public void unregisterBuiltin(IBuiltinAtom builtin) {
	if (builtin == null)
	    throw new IllegalArgumentException(
		    "The builtin atom must not be null");

	reg.remove(builtin.getPredicate());
    }

    /**
     * Returns the arity of a registered built-in.
     * 
     * @param s
     *            the name (predicate symbol) of the built-in
     * @return the arity, or -1 if such a built-in hasn't been registered yet
     */
    public int getBuiltinArity(final String s) {
	final RegisterEntry re = reg.get(s);
	return (re == null) ? -1 : re.getArity();
    }

    /**
     * Returns the class of a registered built-in.
     * 
     * @param s
     *            the name (predicate symbol) of the built-in
     * @return the class, or <code>null</code> if such a built-in hasn't been
     *         registered yet
     */
    public Class<?> getBuiltinClass(final String s) {
	final RegisterEntry re = reg.get(s);
	return (re == null) ? null : re.getBuiltinClass();
    }

    /**
     * <p>
     * Returns a short description of this object. <b>The format of the returned
     * string is undocumented and subject to change.</b>
     * </p>
     * <p>
     * An example return string could be: <code>[ADD[3,
     * org.deri.iris.builtins.AddBuiltin],SUBTRACT[3,
     * org.deri.builtins.SubtractBuiltin]]</code>
     * </p>
     * 
     * @return the description
     */
    public String toString() {
	return reg.values().toString();
    }

    public boolean equals(final Object o) {
	if (!(o instanceof BuiltinRegister)) {
	    return false;
	}
	return reg.equals(((BuiltinRegister) o).reg);
    }

    public int hashCode() {
	return reg.hashCode();
    }

    /**
     * Holds various informations about a built-in.
     */
    private static class RegisterEntry {

	/** The class of the built-in. */
	private Class<?> builtinClass;

	/** The predicate defining the built-in. */
	private IPredicate pred;

	/**
	 * Constructs a registry entry.
	 * 
	 * @param c
	 *            the class of the built-in
	 * @param p
	 *            the predicate of the built-in
	 * @throws NullPointerException
	 *             if the class is <code>null</code>
	 * @throws NullPointerException
	 *             if the predicate is <code>null</code>
	 */
	public RegisterEntry(final Class<?> c, final IPredicate p) {
	    if (c == null) {
		throw new NullPointerException("The class must not be null");
	    }
	    if (p == null) {
		throw new NullPointerException("The predicate must not be null");
	    }
	    builtinClass = c;
	    pred = p;
	}

	/**
	 * Returns the class of the built-in.
	 * 
	 * @return the class
	 */
	public Class<?> getBuiltinClass() {
	    return builtinClass;
	}

	/**
	 * Returns the arity of the built-in.
	 * 
	 * @return the arity
	 */
	public int getArity() {
	    return pred.getArity();
	}

	/**
	 * Returns the name (predicate symbol) of the built-in.
	 * 
	 * @return the name
	 */
	public String getName() {
	    return pred.getPredicateSymbol();
	}

	/**
	 * <p>
	 * Returns a short description of this object. <b>The format of the
	 * returned string is undocumented and subject to change.</b>
	 * </p>
	 * <p>
	 * An example return string could be: <code>ADD[3,
	 * org.deri.iris.builtins.AddBuiltin)</code>
	 * </p>
	 * 
	 * @return the description
	 */
	public String toString() {
	    return getName() + "[" + getArity() + ", " + getBuiltinClass()
		    + "]";
	}

	public boolean equals(final Object o) {
	    if (!(o instanceof RegisterEntry)) {
		return false;
	    }
	    final RegisterEntry e = (RegisterEntry) o;
	    return builtinClass.equals(e.builtinClass) && pred.equals(e.pred);
	}

	public int hashCode() {
	    int res = 17;
	    res = res * 37 + pred.hashCode();
	    res = res * 37 + builtinClass.hashCode();
	    return res;
	}
    }
}
