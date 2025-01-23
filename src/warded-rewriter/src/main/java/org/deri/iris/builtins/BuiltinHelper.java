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

import static org.deri.iris.factory.Factory.CONCRETE;

import java.math.BigDecimal;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.GregorianCalendar;
import java.util.TimeZone;

import javax.xml.datatype.DatatypeConstants;
import javax.xml.datatype.Duration;
import javax.xml.datatype.XMLGregorianCalendar;

import org.deri.iris.EvaluationException;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.INumericTerm;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.concrete.IDateTerm;
import org.deri.iris.api.terms.concrete.IDateTime;
import org.deri.iris.api.terms.concrete.IDecimalTerm;
import org.deri.iris.api.terms.concrete.IDoubleTerm;
import org.deri.iris.api.terms.concrete.IDuration;
import org.deri.iris.api.terms.concrete.IFloatTerm;
import org.deri.iris.api.terms.concrete.IIntegerTerm;
import org.deri.iris.api.terms.concrete.ITime;
import org.deri.iris.terms.concrete.XmlDurationWorkAroundHelper;
import org.deri.iris.utils.StandardFloatingPointComparator;

/**
 * <p>
 * Some helper methods common to some Builtins.
 * </p>
 */
public class BuiltinHelper {

    /**
     * Empty tuple (with arity 0) to avoid some timeconsuming creation of
     * tuples.
     */
    public static final ITuple EMPTY_TUPLE = org.deri.iris.factory.Factory.BASIC
	    .createTuple(new ITerm[] {});

    /**
     * Calendar with all fields set to 0. Used to get the milliseconds out of a
     * {@link javax.xml.datatype.Duration} object.
     */
    private static final Calendar ZERO;

    static {
	ZERO = new GregorianCalendar(TimeZone.getTimeZone("GMT"));
	ZERO.clear();
    }

    private BuiltinHelper() {
	// prevent subclassing
    }

    /**
     * Compares two numerics by casting them to doubles and then comparing them
     * for equality. <b>This method assumes that only numbers are stored in
     * <code>INumericTerm</code>.</b>
     * 
     * @param n0
     *            the first number
     * @param n1
     *            the second number
     * @return whether the numbers are equal
     * @throws NullPointerException
     *             if one of the numbers is null
     * @see Number
     */
    public static boolean numbersEqual(final INumericTerm n0,
	    final INumericTerm n1) {
	if ((n0 == null) || (n1 == null)) {
	    throw new NullPointerException("The numbers must not be null");
	}
	return numbersCompare(n0, n1) == 0;
    }

    /**
     * Compares two numerics by casting them to doubles and then comparing them.
     * <b>This method assumes that only numbers are stored in
     * <code>INumericTerm</code>.</b>
     * 
     * @param n0
     *            the first number
     * @param n1
     *            the second number
     * @return <code>0</code> if they are equal, a value <code>&lt; 0</code> if
     *         n0 is smaller than n1 and a value <code>&gt; 0</code> if n0 is
     *         bigger than n1
     * @throws NullPointerException
     *             if one of the numbers is null
     * @see Number
     */
    public static int numbersCompare(final INumericTerm n0,
	    final INumericTerm n1) {
	if ((n0 == null) || (n1 == null)) {
	    throw new NullPointerException("The numbers must not be null");
	}

	// Special case. Any combination of different numeric types get casted
	// to double, except
	// a pair of integers...
	if (n0 instanceof IIntegerTerm && n1 instanceof IIntegerTerm) {
	    Integer i0 = ((IIntegerTerm) n0).getValue();
	    Integer i1 = ((IIntegerTerm) n1).getValue();

	    return i0.compareTo(i1);
	}

	// ...and a pair of floats.
	if (n0 instanceof IFloatTerm && n1 instanceof IFloatTerm) {
	    Float f0 = ((IFloatTerm) n0).getValue();
	    Float f1 = ((IFloatTerm) n1).getValue();

	    return StandardFloatingPointComparator.getFloat().compare(f0, f1);
	}

	double f0 = getDouble(n0);
	double f1 = getDouble(n1);

	return StandardFloatingPointComparator.getDouble().compare(f0, f1);
    }

    /**
     * Compares two terms to each other. A value <code>&lt;0</code>,
     * <code>0</code> or <code>&gt;0</code> will be returned, if the first term
     * is smaller, equal or greater than the second one.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return an Integer determining which one of the terms is bigger
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     * @throws IllegalArgumentException
     *             if the two terms couldn't be compared
     */
    public static int compare(final ITerm t0, final ITerm t1) {
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The terms must not be null");
	}
	if ((t0 instanceof INumericTerm) && (t1 instanceof INumericTerm)) {
	    return numbersCompare((INumericTerm) t0, (INumericTerm) t1);
	} else if (t0.getClass().isAssignableFrom(t1.getClass())) {
	    return t0.compareTo(t1);
	}
	throw new IllegalArgumentException("Couldn't compare "
		+ t0.getClass().getName() + " and " + t1.getClass().getName());
    }

    /**
     * Evaluate a < operation.
     * 
     * @param t0
     *            A term
     * @param t1
     *            A term
     * @return true if the two terms can be compared and t0 is less than t1
     */
    static boolean less(final ITerm t0, final ITerm t1) {
	assert t0 != null;
	assert t1 != null;

	if ((t0 instanceof INumericTerm) && (t1 instanceof INumericTerm))
	    return numbersCompare((INumericTerm) t0, (INumericTerm) t1) < 0;

	if (t0.getClass() == t1.getClass())
	    return t0.compareTo(t1) < 0;

	return false;
    }

    /**
     * Evaluate a <= operation.
     * 
     * @param t0
     *            A term
     * @param t1
     *            A term
     * @return true if the two terms can be compared and t0 is less than or
     *         equal to t1
     */
    static boolean lessEquals(final ITerm t0, final ITerm t1) {
	assert t0 != null;
	assert t1 != null;

	if ((t0 instanceof INumericTerm) && (t1 instanceof INumericTerm))
	    return numbersCompare((INumericTerm) t0, (INumericTerm) t1) <= 0;

	if (t0.getClass() == t1.getClass())
	    return t0.compareTo(t1) <= 0;

	return false;
    }

    /**
     * Checks whether the values of two terms are the same.
     * 
     * @param t0
     *            the first term
     * @param t1
     *            the second term
     * @return <code>true</code> if the terms are comparable and if their values
     *         are equal, otherwise <code>false</code>
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     */
    static boolean equal(final ITerm t0, final ITerm t1) {
	assert t0 != null;
	assert t1 != null;

	if ((t0 instanceof INumericTerm) && (t1 instanceof INumericTerm))
	    return numbersEqual((INumericTerm) t0, (INumericTerm) t1);

	return t0.equals(t1);
    }

    /**
     * Two terms are exactly equal if they:
     * 
     * a) have exactly the same type, AND b) have the same value
     * 
     * This comparison respects floating point round-off errors.
     * 
     * @param t0
     * @param t1
     * @return
     */
    static boolean exactlyEqual(ITerm t0, ITerm t1) {
	assert t0 != null;
	assert t1 != null;

	// For two floating point terms (implemented with Float or Double) the
	// normal
	// Object.equals() method can not be used, because it hides proper ieee
	// floating
	// point behaviour.
	// Specifically, -0.0 should equal to +0.0, Nan != NaN etc
	// In any case, the floating point comparison should allow for round-off
	// errors.
	if (t0.getClass() == t1.getClass()) {
	    Object ot0 = t0.getValue();
	    Object ot1 = t1.getValue();

	    if (ot0 instanceof Float && ot1 instanceof Float) {
		return StandardFloatingPointComparator.getFloat().equals(
			((Float) ot0).floatValue(), ((Float) ot1).floatValue());
	    } else if (ot0 instanceof Double && ot1 instanceof Double) {
		return StandardFloatingPointComparator.getDouble().equals(
			((Double) ot0).doubleValue(),
			((Double) ot1).doubleValue());
	    }
	}
	return t0.equals(t1);
    }

    /**
     * Returns the Double value from a <code>INumericTerm</code> <b>This method
     * assumes that only numbers are stored in <code>INumericTerm</code>.</b>
     * 
     * @param n
     *            the term
     * @return the double value
     * @throws NullPointerException
     *             if the term is null
     * @see Number
     */
    private static double getDouble(final INumericTerm n) {
	assert n != null;

	// TODO: maybe instance check for Number
	return ((Number) n.getValue()).doubleValue();
    }

    /**
     * Creates a duration out of a given amount of milliseconds.
     * 
     * @param millis
     *            the milliseconds for which to create the duration
     * @return the duration
     */
    private static IDuration createDuration(final long millis) {
	return CONCRETE.createDuration(millis);
    }

    /**
     * Creates a datetime object out of a <code>XMLGregorianCalendar</code>.
     * 
     * @param dt
     *            the <code>XMLGregorianCalendar</code>
     * @return the datetime
     */
    private static IDateTime createDateTime(final XMLGregorianCalendar dt) {
	assert dt != null : "The datetime must not be null";

	return CONCRETE.createDateTime(dt.getYear(), dt.getMonth(),
		dt.getDay(), dt.getHour(), dt.getMinute(),
		XmlDurationWorkAroundHelper.getSeconds(dt).doubleValue(),
		tzHours(dt), tzMinutes(dt));
    }

    /**
     * Creates a date object out of a <code>XMLGregorianCalendar</code>.
     * 
     * @param dt
     *            the <code>XMLGregorianCalendar</code>
     * @return the date
     */
    private static IDateTerm createDate(final XMLGregorianCalendar dt) {
	assert dt != null : "The date must not be null";

	return CONCRETE.createDate(dt.getYear(), dt.getMonth(), dt.getDay(),
		tzHours(dt), tzMinutes(dt));
    }

    private static int tzHours(XMLGregorianCalendar dt) {
	return dt.getTimezone() / 60;
    }

    private static int tzMinutes(XMLGregorianCalendar dt) {
	int tz = dt.getTimezone();
	if (tz < 0)
	    return -((-tz) % 60);
	else
	    return tz % 60;
    }

    /**
     * Creates a time object out of a <code>XMLGregorianCalendar</code>.
     * 
     * @param dt
     *            the <code>XMLGregorianCalendar</code>
     * @return the time
     */
    private static ITime createTime(final XMLGregorianCalendar dt) {
	assert dt != null : "The time must not be null";

	return CONCRETE
		.createTime(dt.getHour(), dt.getMinute(), dt.getSecond(), dt
			.getMillisecond(), tzHours(dt), tzMinutes(dt));
    }

    /**
     * Creates a duration object out of a <code>Duration</code>.
     * 
     * @param dt
     *            the <code>Duration</code>
     * @return the duration
     */
    private static IDuration createDuration(final Duration d) {
	assert d != null : "The duration must not be null";

	return CONCRETE.createDuration(d.getSign() >= 0, d.getYears(), d
		.getMonths(), d.getDays(), d.getHours(), d.getMinutes(),
		((BigDecimal) d.getField(DatatypeConstants.SECONDS))
			.doubleValue());
    }

    /**
     * <p>
     * Produces the sum of two terms. The resulting term will be of the most
     * accurate type of the submitted ones.
     * </p>
     * 
     * @param t0
     *            the first summand
     * @param t1
     *            the second summand
     * @return the sum
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     * @throws IllegalArgumentException
     *             if the operation couldn't be applied to the terms
     */
    public static ITerm add(final ITerm t0, final ITerm t1) {
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The terms must not be null");
	}
	if ((t0 instanceof IIntegerTerm) && (t1 instanceof IIntegerTerm)) { // int
									    // +
									    // int
									    // =
									    // int
	    return CONCRETE.createInteger(((IIntegerTerm) t0).getValue()
		    + ((IIntegerTerm) t1).getValue());
	} else if ((t0 instanceof INumericTerm) && (t1 instanceof INumericTerm)) { // number
										   // +
										   // number
										   // =
										   // number
	    return toAppropriateType(getDouble((INumericTerm) t0)
		    + getDouble((INumericTerm) t1), t0, t1);
	} else if ((t0 instanceof IDateTime) && (t1 instanceof IDuration)) { // datetime
									     // +
									     // duration
									     // =
									     // datetime
	    final XMLGregorianCalendar cal0 = (XMLGregorianCalendar) ((IDateTime) t0)
		    .getValue().clone();
	    cal0.add(((IDuration) t1).getValue());
	    return createDateTime(cal0);
	} else if ((t0 instanceof IDuration) && (t1 instanceof IDateTime)) { // duration
									     // +
									     // datetime
									     // =
									     // datetime
	    final XMLGregorianCalendar cal1 = (XMLGregorianCalendar) ((IDateTime) t1)
		    .getValue().clone();
	    cal1.add(((IDuration) t0).getValue());
	    return createDateTime(cal1);
	} else if ((t0 instanceof IDateTerm) && (t1 instanceof IDuration)) { // date
									     // +
									     // duration
									     // =
									     // date
	    final XMLGregorianCalendar cal0 = (XMLGregorianCalendar) ((IDateTerm) t0)
		    .getValue().clone();
	    cal0.add(((IDuration) t1).getValue());
	    return createDate(cal0);
	} else if ((t0 instanceof IDuration) && (t1 instanceof IDateTerm)) { // duration
									     // +
									     // date
									     // =
									     // date
	    final XMLGregorianCalendar cal1 = (XMLGregorianCalendar) ((IDateTerm) t1)
		    .getValue().clone();
	    cal1.add(((IDuration) t0).getValue());
	    return createDate(cal1);
	} else if ((t0 instanceof ITime) && (t1 instanceof IDuration)) { // time
									 // +
									 // duration
									 // =
									 // time
	    final XMLGregorianCalendar cal0 = (XMLGregorianCalendar) ((ITime) t0)
		    .getValue().clone();
	    cal0.add(((IDuration) t1).getValue());
	    return createTime(cal0);
	} else if ((t0 instanceof IDuration) && (t1 instanceof ITime)) { // duration
									 // +
									 // time
									 // =
									 // time
	    final XMLGregorianCalendar cal1 = (XMLGregorianCalendar) ((ITime) t1)
		    .getValue().clone();
	    cal1.add(((IDuration) t0).getValue());
	    return createTime(cal1);
	} else if ((t0 instanceof IDuration) && (t1 instanceof IDuration)) { // duration
									     // +
									     // duration
									     // =
									     // duration
	    final Duration d0 = ((IDuration) t0).getValue();
	    final Duration d1 = ((IDuration) t1).getValue();
	    return createDuration(XmlDurationWorkAroundHelper.add(d0, d1));
	}
	return null;
    }

    /**
     * <p>
     * Produces the difference of two terms. The resulting term will be of the
     * most accurate type of the submitted ones.
     * </p>
     * 
     * @param t0
     *            the minuend
     * @param t1
     *            the subtrahend
     * @return the differnece
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     * @throws IllegalArgumentException
     *             if the operation couldn't be applied to the terms
     */
    public static ITerm subtract(final ITerm t0, final ITerm t1) {
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The terms must not be null");
	}
	if ((t0 instanceof IIntegerTerm) && (t1 instanceof IIntegerTerm)) { // int
									    // -
									    // int
									    // =
									    // int
	    return CONCRETE.createInteger(((IIntegerTerm) t0).getValue()
		    - ((IIntegerTerm) t1).getValue());
	} else if ((t0 instanceof INumericTerm) && (t1 instanceof INumericTerm)) { // numer
										   // -
										   // number
										   // =
										   // number
	    return toAppropriateType(getDouble((INumericTerm) t0)
		    - getDouble((INumericTerm) t1), t0, t1);
	} else if ((t0 instanceof IDateTime) && (t1 instanceof IDateTime)) { // datetime
									     // -
									     // datetime
									     // =
									     // duration
	    final XMLGregorianCalendar cal0 = ((IDateTime) t0).getValue();
	    final XMLGregorianCalendar cal1 = ((IDateTime) t1).getValue();

	    return createDuration(XmlDurationWorkAroundHelper.subtract(cal0,
		    cal1));

	    // return
	    // createDuration(cal0.toGregorianCalendar().getTimeInMillis() -
	    // cal1.toGregorianCalendar().getTimeInMillis());

	} else if ((t0 instanceof IDateTime) && (t1 instanceof IDuration)) { // datetime
									     // -
									     // duration
									     // =
									     // datetime
	    final XMLGregorianCalendar cal0 = (XMLGregorianCalendar) ((IDateTime) t0)
		    .getValue().clone();
	    cal0.add(((IDuration) t1).getValue().negate());
	    return createDateTime(cal0);
	} else if ((t0 instanceof IDateTerm) && (t1 instanceof IDateTerm)) { // date
									     // -
									     // date
									     // =
									     // duration
	    final XMLGregorianCalendar cal0 = ((IDateTerm) t0).getValue();
	    final XMLGregorianCalendar cal1 = ((IDateTerm) t1).getValue();

	    return createDuration(XmlDurationWorkAroundHelper.subtract(cal0,
		    cal1));
	    // return
	    // createDuration(cal0.toGregorianCalendar().getTimeInMillis() -
	    // cal1.toGregorianCalendar().getTimeInMillis());

	} else if ((t0 instanceof IDateTerm) && (t1 instanceof IDuration)) { // date
									     // -
									     // duration
									     // =
									     // date
	    final XMLGregorianCalendar cal0 = (XMLGregorianCalendar) ((IDateTerm) t0)
		    .getValue().clone();
	    cal0.add(((IDuration) t1).getValue().negate());
	    return createDate(cal0);
	} else if ((t0 instanceof ITime) && (t1 instanceof ITime)) { // time -
								     // time =
								     // duration
	    final XMLGregorianCalendar cal0 = ((ITime) t0).getValue();
	    final XMLGregorianCalendar cal1 = ((ITime) t1).getValue();
	    return createDuration(cal0.toGregorianCalendar().getTimeInMillis()
		    - cal1.toGregorianCalendar().getTimeInMillis());
	} else if ((t0 instanceof ITime) && (t1 instanceof IDuration)) { // time
									 // -
									 // duration
									 // =
									 // time
	    final XMLGregorianCalendar cal0 = (XMLGregorianCalendar) ((ITime) t0)
		    .getValue().clone();
	    cal0.add(((IDuration) t1).getValue().negate());
	    return createTime(cal0);
	} else if ((t0 instanceof IDuration) && (t1 instanceof IDuration)) { // duration
									     // -
									     // duration
	    final Duration d0 = ((IDuration) t0).getValue();
	    final Duration d1 = ((IDuration) t1).getValue();
	    return createDuration(XmlDurationWorkAroundHelper.subtract(d0, d1));
	}

	return null;
    }

    /**
     * <p>
     * Produces the product of two terms. The resulting term will be of the most
     * accurate type of the submitted ones.
     * </p>
     * <p>
     * At the moment only INumericTerms are supported.
     * </p>
     * 
     * @param t0
     *            the first factor
     * @param t1
     *            the second factor
     * @return the product
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     * @throws IllegalArgumentException
     *             if one of the terms is not a INumericTerm
     */
    public static ITerm multiply(final ITerm t0, final ITerm t1) {
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The terms must not be null");
	}

	if ((t0 instanceof IIntegerTerm) && (t1 instanceof IIntegerTerm)) {
	    // int * int = int
	    return CONCRETE.createInteger(((IIntegerTerm) t0).getValue()
		    * ((IIntegerTerm) t1).getValue());
	}

	if (t0 instanceof INumericTerm && t1 instanceof INumericTerm) // number
								      // -
								      // number
								      // =
								      // number
	    return toAppropriateType(getDouble((INumericTerm) t0)
		    * getDouble((INumericTerm) t1), t0, t1);

	return null;
    }

    /**
     * <p>
     * Produces the quotient of two terms. The resulting term will be of the
     * most accurate type of the submitted ones.
     * </p>
     * <p>
     * At the moment only INumericTerms are supported.
     * </p>
     * 
     * @param t0
     *            the dividend
     * @param t1
     *            the divisor
     * @return the quotient
     * @throws EvaluationException
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     */
    public static ITerm divide(final ITerm t0, final ITerm t1)
	    throws EvaluationException {
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The terms must not be null");
	}

	if ((t0 instanceof IIntegerTerm) && (t1 instanceof IIntegerTerm)) {
	    int denominator = ((IIntegerTerm) t1).getValue();

	    if (denominator == 0) {
		handleDivideByZero();
		return null;
	    }

	    // int / int = int
	    return CONCRETE.createInteger(((IIntegerTerm) t0).getValue()
		    / denominator);
	}

	if (t0 instanceof INumericTerm && t1 instanceof INumericTerm) {
	    double denominator = getDouble((INumericTerm) t1);

	    if (denominator == 0.0) {
		handleDivideByZero();
		return null;
	    }

	    return toAppropriateType(
		    getDouble((INumericTerm) t0) / denominator, t0, t1);
	}

	return null;
    }

    /**
     * Method to call whenever a divide by zero occurs.
     * 
     * @throws EvaluationException
     */
    private static void handleDivideByZero() throws EvaluationException {
	    throw new EvaluationException("Divide by zero error");
    }

    static ITerm increment(ITerm argument) {
	assert argument != null;

	if (argument instanceof IIntegerTerm)
	    return CONCRETE
		    .createInteger(((IIntegerTerm) argument).getValue() + 1);

	if (argument instanceof INumericTerm)
	    return toAppropriateType(getDouble((INumericTerm) argument) + 1,
		    argument, argument);

	return null;
    }

    /**
     * <p>
     * Produces the modulus of two terms. The resulting term will be of the most
     * accurate type of the submitted ones.
     * </p>
     * <p>
     * At the moment only INumericTerms are supported.
     * </p>
     * 
     * @param t0
     *            the first argument
     * @param t1
     *            the second argument
     * @return the product = t0 % t1
     * @throws EvaluationException
     * @throws NullPointerException
     *             if one of the terms is <code>null</code>
     * @throws IllegalArgumentException
     *             if one of the terms is not a INumericTerm
     */
    public static ITerm modulus(final ITerm t0, final ITerm t1)
	    throws EvaluationException {
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The terms must not be null");
	}

	if ((t0 instanceof IIntegerTerm) && (t1 instanceof IIntegerTerm)) {
	    int numerator = ((IIntegerTerm) t0).getValue();
	    if (numerator < 0) {
		handleInvalidModulusNumerator();
		return null;
	    }

	    int denominator = ((IIntegerTerm) t1).getValue();
	    if (denominator < 1) {
		handleInvalidModulusDenominator();
		return null;
	    }

	    return CONCRETE.createInteger(((IIntegerTerm) t0).getValue()
		    % denominator);
	}

	if (t0 instanceof INumericTerm && t1 instanceof INumericTerm) {
	    double numerator = getDouble((INumericTerm) t0);
	    if (numerator < 0) {
		handleInvalidModulusNumerator();
		return null;
	    }

	    double denominator = getDouble((INumericTerm) t1);
	    if (denominator <= 0.0) {
		handleDivideByZero();
		return null;
	    }

	    return toAppropriateType(numerator % denominator, t0, t1);
	}

	return null;
    }

    private static void handleInvalidModulusNumerator() {
    }

    private static void handleInvalidModulusDenominator() {
    }

    /**
     * Constructs a number term with of the most appropriate term type.
     * 
     * @param n
     *            the value for the returned term
     * @param t0
     *            the first term (only the type of this term will be taken into
     *            account)
     * @param t1
     *            the first term (only the type of this term will be taken into
     *            account)
     * @return a term of the most appropriate type of the submitted ones with
     *         the given value.
     */
    private static ITerm toAppropriateType(final Number n, final ITerm t0,
	    final ITerm t1) {
	assert n != null;
	assert t0 != null;
	assert t1 != null;
	assert t0 instanceof INumericTerm;
	assert t1 instanceof INumericTerm;

	if ((t0 instanceof IIntegerTerm) && (t1 instanceof IIntegerTerm))
	    return CONCRETE.createInteger(n.intValue());

	if ((t0 instanceof IDecimalTerm) || (t1 instanceof IDecimalTerm))
	    return CONCRETE.createDecimal(n.doubleValue());

	if ((t0 instanceof IDoubleTerm) || (t1 instanceof IDoubleTerm))
	    return CONCRETE.createDouble(n.doubleValue());

	if ((t0 instanceof IFloatTerm) && (t1 instanceof IFloatTerm))
	    return CONCRETE.createFloat(n.floatValue());

	return CONCRETE.createDouble(n.doubleValue());
    }

    /**
     * Determines the indexes of the ground terms in a collection.
     * 
     * @param t
     *            the collection where to search for ground terms
     * @return the indexes of the ground terms (the first term has the index 0)
     * @throws NullPointerException
     *             if the collection is <code>null</code>
     */
    public static int[] determineGround(final Collection<ITerm> t) {
	if (t == null) {
	    throw new NullPointerException("The tuple must not be null");
	}
	final int[] res = new int[t.size()];
	int i = 0;
	int pos = 0;
	for (final ITerm term : t) {
	    if (term.isGround()) {
		res[i++] = pos;
	    }
	    pos++;
	}
	final int[] ret = new int[i];
	System.arraycopy(res, 0, ret, 0, i);
	return ret;
    }

    /**
     * Returns the terms at a given position in a collection.
     * 
     * @param t
     *            the collection from where to retrieve the terms
     * @param pos
     *            the positions of the terms to retrieve
     * @return the retrieved terms
     * @throws NullPointerException
     *             if the collection is <code>null</code>
     * @throws NullPointerException
     *             if the position array is <code>null</code>
     * @throws IllegalArgumentException
     *             if ther are more terms requested, than given (pos.length &gt;
     *             t.size())
     */
    public static ITerm[] getIndexes(final Collection<ITerm> t, final int[] pos) {
	if (pos == null) {
	    throw new NullPointerException(
		    "The position array must not be null");
	}
	if (t == null) {
	    throw new NullPointerException("The tuple must not be null");
	}
	if (pos.length > t.size()) {
	    throw new IllegalArgumentException("There are " + pos.length + " <"
		    + Arrays.asList(pos) + "> terms requested, but only "
		    + t.size() + " <" + t + "> terms given");
	}
	final ITerm[] ret = new ITerm[pos.length];
	final ITerm[] in = t.toArray(new ITerm[t.size()]);
	int idx = 0;

	for (final int i : pos) {
	    ret[idx++] = in[i];
	}
	return ret;
    }

    /**
     * Determines the indexes of the unground terms in a collection.
     * 
     * @param t
     *            the collection where to search for ground terms
     * @return the indexes of the unground terms (the first term has the index
     *         0)
     * @throws NullPointerException
     *             if the collection is <code>null</code>
     */
    public static int[] determineUnground(final Collection<ITerm> t) {
	if (t == null) {
	    throw new NullPointerException("The tuple must not be null");
	}
	final int[] res = new int[t.size()];
	int i = 0;
	int pos = 0;
	for (final ITerm term : t) {
	    if (!term.isGround()) {
		res[i++] = pos;
	    }
	    pos++;
	}
	final int[] ret = new int[i];
	System.arraycopy(res, 0, ret, 0, i);
	return ret;
    }

    /**
     * <p>
     * Computes the complement of an index array.
     * </p>
     * <p>
     * E.g. we have computed an index array <code>[1, 3, 4]</code> of a
     * collection with length 5 we would get <code>[0, 2]</code> as complement.
     * </p>
     * 
     * @param i
     *            the array from which to compute the complement
     * @param l
     *            the length of the collection whe took the index from
     * @return the complement
     * @throws NullPointerException
     *             if the index array was <code>null</code>
     * @throws IllegalArgumentException
     *             if the lenght was nevative
     * @see #determineGround(Collection<ITerm>)
     * @see #determineUnground(Collection<ITerm>)
     */
    public static int[] complement(final int[] i, final int l) {
	if (l < 0) {
	    throw new IllegalArgumentException(
		    "The length must not be negative");
	}
	// TODO: this method needs a rewrite (get rid of this
	// arraycopy)! WHY DON'T WE USE PERL!?!?!
	int[] ret = new int[l - i.length];
	int[] clone = new int[i.length];
	System.arraycopy(i, 0, clone, 0, i.length);
	Arrays.sort(clone);
	for (int j = 0, pos = 0; pos < ret.length; j++) {
	    if (Arrays.binarySearch(clone, j) < 0) {
		ret[pos++] = j;
	    }
	}
	return ret;
    }

    /**
     * <p>
     * Concats two term arrays taking an index array into account.
     * </p>
     * <p>
     * E.g. we got an index of <code>[0, 3, 4]</code>, the firs array is
     * <code>['a', 'b', 'c']</code> and the second <code>[12, 13, 14]</code> we
     * will get <code>['a', 12, 13, 'b', 'c', 14]</code>.
     * </p>
     * 
     * @param idx0
     *            the index array
     * @param t0
     *            the first array (this terms will be put at he positions of the
     *            index array)
     * @param t1
     *            the second array (with this terms the gaps will be filled up)
     * @throws NullPointerException
     *             if the index array is <code>null</code>
     * @throws NullPointerException
     *             if one of the term arrays is <code>null</code>
     * @throws IllegalArgumentException
     *             if the lenght of the index and the first term array don't
     *             match
     * @see #determineGround(Collection<ITerm>)
     * @see #determineUnground(Collection<ITerm>)
     */
    public static ITerm[] concat(final int[] idx0, final ITerm[] t0,
	    final ITerm[] t1) {
	if (idx0 == null) {
	    throw new NullPointerException("The index array must not be null");
	}
	if ((t0 == null) || (t1 == null)) {
	    throw new NullPointerException("The term arrays must not be null");
	}
	if (idx0.length != t0.length) {
	    throw new IllegalArgumentException(
		    "The length of the index array and "
			    + "the first array must be equal, but was "
			    + idx0.length + " and " + t0.length);
	}
	final java.util.List<ITerm> res = new java.util.LinkedList<ITerm>();
	res.addAll(Arrays.asList(t1));
	for (int i = 0; i < idx0.length; i++) {
	    res.add(idx0[i], t0[i]);
	}
	return res.toArray(new ITerm[res.size()]);
    }
}
