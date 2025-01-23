/**
 * 
 */
package org.deri.iris.queryrewriting.caching;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * @author Giorgio Orsi <giorgio.orsi@cs.ox.ac.uk> - Department of Computer Science, University of Oxford.
 * @version 1.0
 */
public class MGUCache {

	private static Map<Pair<IAtom, Map<IVariable, ITerm>>, ILiteral> mguCache;

	private static MGUCache instance;

	public static MGUCache getCache() {
		if (instance == null) {
			instance = new MGUCache();
		}
		return instance;
	}

	public static MGUCache getClearCache() {
		return new MGUCache();
	}

	public void clearCache() {
		mguCache.clear();
	}

	private MGUCache() {
		//Marco: make map thread-safe
		mguCache = Collections.synchronizedMap(
			new HashMap<Pair<IAtom, Map<IVariable, ITerm>>, ILiteral>(1000000, (float) .95));

	}

	private static void cache(final Pair<IAtom, Map<IVariable, ITerm>> pair, final ILiteral literal) {
		mguCache.put(pair, literal);
	}

	public static void cache(final IAtom atom, final Map<IVariable, ITerm> mgu, final ILiteral literal) {
		cache(Pair.of(atom, mgu), literal);
	}

	private static boolean inCache(final Pair<IAtom, Map<IVariable, ITerm>> pair) {
		return mguCache.containsKey(pair);
	}

	public static boolean inCache(final IAtom atom, final Map<IVariable, ITerm> mgu) {
		return inCache(Pair.of(atom, mgu));
	}

	public static ILiteral getLiteral(final Pair<Set<ILiteral>, Set<ILiteral>> pair) {
		return mguCache.get(pair);
	}

	public static ILiteral getLiteral(final IAtom atom, final Map<IVariable, ITerm> mgu) {
		return mguCache.get(Pair.of(atom, mgu));
	}

	public static long size() {
		return mguCache.size();
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		sb.append("MGU CACHE");
		for (final Pair<IAtom, Map<IVariable, ITerm>> p : mguCache.keySet()) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}
		sb.append(IOUtils.LINE_SEPARATOR);

		return sb.toString();
	}
}
