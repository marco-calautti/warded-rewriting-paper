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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.deri.iris.api.basics.ITuple;
import org.deri.iris.storage.IRelation;
import org.deri.iris.utils.UniqueList;

/**
 * A simple, in-memory, array-based relation.
 */
public class SimpleRelation implements IRelation {
  /**
   * Constructor. For performance reasons where the user of the class can enforce uniqueness (or does not require it),
   * uniqueness enforcement can be turned off.
   * 
   * @param forceUniqueness
   *          true, if this object should enforce uniqueness.
   */
  public SimpleRelation() {
    mTuples = new UniqueList<ITuple>();
  }

  @Override public boolean add(final ITuple tuple) {
    assert mTuples.isEmpty() || mTuples.get(0).size() == tuple.size();

    return mTuples.add(tuple);
  }

  @Override public boolean addAll(final IRelation relation) {
    boolean added = false;

    for (int i = 0; i < relation.size(); ++i)
      if (add(relation.get(i))) {
        added = true;
      }

    return added;
  }

  @Override public ITuple get(final int index) {
    return mTuples.get(index);
  }

  @Override public int size() {
    return mTuples.size();
  }

  @Override public boolean contains(final ITuple tuple) {
    return mTuples.contains(tuple);
  }

  public boolean contains(final IRelation relation) {
    for (int i = 0; i < relation.size(); i++) {
      if (!mTuples.contains(relation.get(i)))
        return false;
    }
    return true;
  }

  @Override public String toString() {
    return mTuples.toString();
  }

  /** The array list (or unique list) of tuples. */
  private final List<ITuple> mTuples;

  public Set<ITuple> tuples() {
    return new HashSet<ITuple>(mTuples);
  }

}
