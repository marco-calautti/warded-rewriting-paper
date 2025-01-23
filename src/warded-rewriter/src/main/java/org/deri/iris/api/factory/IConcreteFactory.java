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

import org.deri.iris.api.terms.concrete.IBase64Binary;
import org.deri.iris.api.terms.concrete.IBooleanTerm;
import org.deri.iris.api.terms.concrete.IDateTerm;
import org.deri.iris.api.terms.concrete.IDateTime;
import org.deri.iris.api.terms.concrete.IDecimalTerm;
import org.deri.iris.api.terms.concrete.IDoubleTerm;
import org.deri.iris.api.terms.concrete.IDuration;
import org.deri.iris.api.terms.concrete.IFloatTerm;
import org.deri.iris.api.terms.concrete.IGDay;
import org.deri.iris.api.terms.concrete.IGMonth;
import org.deri.iris.api.terms.concrete.IGMonthDay;
import org.deri.iris.api.terms.concrete.IGYear;
import org.deri.iris.api.terms.concrete.IGYearMonth;
import org.deri.iris.api.terms.concrete.IHexBinary;
import org.deri.iris.api.terms.concrete.IIntegerTerm;
import org.deri.iris.api.terms.concrete.IIri;
import org.deri.iris.api.terms.concrete.ISqName;
import org.deri.iris.api.terms.concrete.ITime;

/**
 * <p>
 * An interface that can be used to create set of data types supported by this
 * engine.
 * </p>
 */
public interface IConcreteFactory {
    public IBase64Binary createBase64Binary(String s);

    /**
     * Create a boolean term from a boolean value.
     * 
     * @param b
     *            The value of the term
     * @return The boolean term.
     */
    public IBooleanTerm createBoolean(boolean b);

    /**
     * Create a boolean term with a string value.
     * 
     * @param value
     *            The string value, which must be either 'true' or '1' for true,
     *            or 'false' or '0' for false.
     * @return The boolean term.
     */
    public IBooleanTerm createBoolean(String value);

    /**
     * Creates a datetime object with a given timezone.
     * 
     * @param year
     *            the years
     * @param month
     *            the months (1-12)
     * @param day
     *            day of the month
     * @param hour
     *            the hours
     * @param minute
     *            the minutes
     * @param second
     *            the decimal seconds
     * @param tzHour
     *            the timezone hours (relative to GMT)
     * @param tzMinute
     *            the timezone minutes (relative to GMT)
     * @throws IllegalArgumentException
     *             if, the tzHour and tzMinute wheren't both positive, or
     *             negative
     */
    public IDateTime createDateTime(int year, int month, int day, int hour,
	    int minute, double second, int tzHour, int tzMinute);

    /**
     * Creates a datetime object with a given timezone.
     * 
     * @param year
     *            the years
     * @param month
     *            the months (1-12)
     * @param day
     *            day of the month
     * @param hour
     *            the hours
     * @param minute
     *            the minutes
     * @param second
     *            the seconds
     * @param millisecond
     *            the milliseconds
     * @param tzHour
     *            the timezone hours (relative to GMT)
     * @param tzMinute
     *            the timezone minutes (relative to GMT)
     * @throws IllegalArgumentException
     *             if, the tzHour and tzMinute wheren't both positive, or
     *             negative
     */
    public IDateTime createDateTime(int year, int month, int day, int hour,
	    int minute, int second, int millisecond, int tzHour, int tzMinute);

    /**
     * Creates a time object with a given timezone.
     * 
     * @param hour
     *            the hours
     * @param minute
     *            the minutes
     * @param second
     *            the decimal seconds
     * @param tzHour
     *            the timezone hours (relative to GMT)
     * @param tzMinute
     *            the timezone minutes (relative to GMT)
     * @throws IllegalArgumentException
     *             if, the tzHour and tzMinute wheren't both positive, or
     *             negative
     */
    public ITime createTime(int hour, int minute, double second, int tzHour,
	    int tzMinute);

    /**
     * Creates a time object with a given timezone.
     * 
     * @param hour
     *            the hours
     * @param minute
     *            the minutes
     * @param second
     *            the seconds
     * @param millisecond
     *            the milliseconds
     * @param tzHour
     *            the timezone hours (relative to GMT)
     * @param tzMinute
     *            the timezone minutes (relative to GMT)
     * @throws IllegalArgumentException
     *             if, the tzHour and tzMinute wheren't both positive, or
     *             negative
     */
    public ITime createTime(int hour, int minute, int second, int millisecond,
	    int tzHour, int tzMinute);

    /**
     * Creates a new date object. The timezone will be set to GMT.
     * 
     * @param year
     *            the year
     * @param month
     *            the mont (1-12)
     * @param day
     *            the day
     */
    public IDateTerm createDate(int year, int month, int day);

    /**
     * Creates a new date object within the given timezone.
     * 
     * @param year
     *            the year
     * @param month
     *            the mont (1-12)
     * @param day
     *            the day
     * @param tzHour
     *            the timezone hours (relative to GMT)
     * @param tzMinute
     *            the timezone minutes (relative to GMT)
     * @throws IllegalArgumentException
     *             if, the tzHour and tzMinute wheren't both positive, or
     *             negative
     */
    public IDateTerm createDate(int year, int month, int day, int tzHour,
	    int tzMinute);

    /**
     * Create a new decimal term.
     * 
     * @param d
     *            The decimal value
     * @return The new decimal term
     */
    public IDecimalTerm createDecimal(double d);

    /**
     * Create a double term.
     * 
     * @param d
     *            The double values
     * @return The new term
     */
    public IDoubleTerm createDouble(double d);

    /**
     * Constructs a new duration.
     * 
     * @param positive
     *            <code>true</code>if the duration is positive, otherwise
     *            <code>false</code>
     * @param year
     *            the yearspan
     * @param month
     *            the monthspa (1-12)
     * @param day
     *            the dayspan
     * @param hour
     *            the hourspan
     * @param minute
     *            the minutespan
     * @param second
     *            the secondspan
     * @param millisecond
     *            the millisecondspan
     */
    public IDuration createDuration(boolean positive, int year, int month,
	    int day, int hour, int minute, int second, int millisecond);

    /**
     * Create a new Duration term.
     * 
     * @param positive
     *            true is a positive duration
     * @param year
     * @param month
     * @param day
     * @param hour
     * @param minute
     * @param second
     * @return
     */
    public IDuration createDuration(boolean positive, int year, int month,
	    int day, int hour, int minute, double second);

    /**
     * Constructs a new duration out of a given amount of milliseconds. The
     * milliseconds will be round down to the next second.
     * 
     * @param millis
     *            the millisecond span
     */
    public IDuration createDuration(long millis);

    /**
     * Create a new float term
     * 
     * @param f
     *            The float value
     * @return The new float term
     */
    public IFloatTerm createFloat(float f);

    /**
     * Create a new day term
     * 
     * @param day
     *            The day value
     * @return The new term
     */
    public IGDay createGDay(int day);

    /**
     * Create a new month/day term
     * 
     * @param month
     *            The month value
     * @param day
     *            The day value
     * @return The new term
     */
    public IGMonthDay createGMonthDay(int month, int day);

    /**
     * Create a new month term
     * 
     * @param month
     *            The month value
     * @return The new term
     */
    public IGMonth createGMonth(int month);

    /**
     * Create a new year/month term
     * 
     * @param year
     *            The year value
     * @param month
     *            The month value
     * @return The new term
     */
    public IGYearMonth createGYearMonth(int year, int month);

    /**
     * Create a new integer term
     * 
     * @param i
     *            The integer value
     * @return The new term
     */
    public IIntegerTerm createInteger(int i);

    /**
     * Create a new year term
     * 
     * @param year
     *            The year value
     * @return The new term
     */
    public IGYear createGYear(int year);

    /**
     * Create a new HexBinary term
     * 
     * @param s
     *            The hex binary value
     * @return The new term
     */
    public IHexBinary createHexBinary(String s);

    /**
     * Create a new IRI term
     * 
     * @param s
     *            The IRI value
     * @return The new term
     */
    public IIri createIri(String s);

    /**
     * Create a new SQName term
     * 
     * @param s
     *            The SQName value
     * @return The new term
     */
    public ISqName createSqName(String s);

    /**
     * Create a new SQName term
     * 
     * @param iri
     *            The IRI value
     * @param s
     *            The SQName value
     * @return The new term
     */
    public ISqName createSqName(IIri iri, String name);
}
