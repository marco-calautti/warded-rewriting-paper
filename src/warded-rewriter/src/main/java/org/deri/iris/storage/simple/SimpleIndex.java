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
package org.deri.iris.storage.simple;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.storage.IIndex;
import org.deri.iris.storage.IRelation;

/**
 * A simple, in-memory, hash-based index.
 */
public class SimpleIndex implements IIndex {
    /**
     * Constructor. Create an index on the given relation, on the specified term
     * indices.
     * 
     * @param relation
     *            The relation to index.
     * @param indices
     *            The term indices using zero-based indexing. Each index value
     *            must be greater than or equal to zero and less than the arity
     *            if the relation.
     */
    public SimpleIndex(IRelation relation, int... indices) {
	mIndices = indices;
	mRelation = relation;
    }

    // TODO change to return Iterator<ITuple> - for really big relations??
    public List<ITuple> get(List<ITerm> key) {
	assert key.size() == mIndices.length;

	update();

	List<ITuple> result = mBag.get(key);

	if (result == null)
	    result = mEmptyTupleList;

	return result;
    }

    /**
     * Update this index by reading any tuples not yet seen from the relation.
     */
    private void update() {
	for (; mLastIndexOfView < mRelation.size(); ++mLastIndexOfView) {
	    ITuple viewTuple = mRelation.get(mLastIndexOfView);
	    List<ITerm> key = makeKey(viewTuple);

	    List<ITuple> values = mBag.get(key);
	    if (values == null) {
		values = new ArrayList<ITuple>();
		mBag.put(key, values);
	    }
	    values.add(viewTuple);
	}
    }

    /**
     * Make a key from the given tuples and the known term index positions.
     * 
     * @param tuple
     *            The tuples
     * @return
     */
    private List<ITerm> makeKey(ITuple tuple) {
	List<ITerm> key = new ArrayList<ITerm>(mIndices.length);

	for (int i = 0; i < mIndices.length; ++i)
	    key.add(tuple.get(mIndices[i]));

	return key;
    }

    @Override
    public String toString() {
	StringBuilder result = new StringBuilder();

	result.append("Indices: ");
	result.append(Arrays.toString(mIndices));

	return result.toString();
    }

    /** The index of the last last known tuple from the relation. */
    private int mLastIndexOfView = 0;

    /** The maps of unique key values to matching tuples. */
    private final Map<List<ITerm>, List<ITuple>> mBag = new HashMap<List<ITerm>, List<ITuple>>();

    /** The term indices to index the relation on. */
    private final int[] mIndices;

    /** The relation being indexed. */
    private final IRelation mRelation;

    private static final List<ITuple> mEmptyTupleList = Collections
	    .unmodifiableList(new ArrayList<ITuple>());
}
