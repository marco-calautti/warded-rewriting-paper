/**
 * 
 */
package org.deri.iris.queryrewriting;

import java.util.Comparator;
import java.util.Set;

import org.deri.iris.api.basics.IAtom;

/**
 * @author jd
 */
public class SetSizeComparator implements Comparator<Set<IAtom>> {

	@Override
	public int compare(final Set<IAtom> o1, final Set<IAtom> o2) {

		if (((Set<?>) o1).size() < ((Set<?>) o2).size())
			return 1;
		else if (((Set<?>) o1).size() > ((Set<?>) o2).size())
			return -1;
		else
			return 0;
	}
}
