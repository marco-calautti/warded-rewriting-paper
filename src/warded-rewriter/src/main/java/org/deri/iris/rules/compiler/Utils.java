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
package org.deri.iris.rules.compiler;

import java.util.ArrayList;
import java.util.List;

import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.ITerm;

/**
 * Utilities for classes in this package.
 */
public class Utils {
    /**
     * Convert a list of integers to an array.
     * 
     * @param list
     *            The list of integers.
     * @return An array of integers.
     */
    public static int[] integerListToArray(List<Integer> list) {
	int[] result = new int[list.size()];

	for (int i = 0; i < list.size(); ++i)
	    result[i] = list.get(i);

	return result;
    }

    /**
     * Make a list of terms by selecting them from a tuple.
     * 
     * @param tuple
     *            The tuple containing terms to select.
     * @param indices
     *            The indices of terms to use.
     * @return The list of selected tuples.
     */
    public static List<ITerm> makeKey(ITuple tuple, int[] indices) {
	List<ITerm> key = new ArrayList<ITerm>(indices.length);

	for (int i = 0; i < indices.length; ++i)
	    key.add(tuple.get(indices[i]));

	return key;
    }

}
