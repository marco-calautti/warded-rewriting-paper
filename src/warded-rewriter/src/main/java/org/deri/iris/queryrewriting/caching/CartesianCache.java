/**
 * 
 */
package org.deri.iris.queryrewriting.caching;

import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * @author Giorgio Orsi
 */
public class CartesianCache {

	private static Map<Pair<Set<ITerm>, Set<ITerm>>, Set<Map<IVariable, ITerm>>> cartesianCache;

	private static CartesianCache instance;

	public static CartesianCache getCache() {
		if (instance == null) {
			instance = new CartesianCache();
		}
		return instance;
	}

	public static CartesianCache getClearCache() {
		return new CartesianCache();
	}

	public void clearCache() {
		cartesianCache.clear();
	}

	private CartesianCache() {
		cartesianCache = new ConcurrentHashMap<Pair<Set<ITerm>, Set<ITerm>>, Set<Map<IVariable, ITerm>>>(300000);
	}

	private static void cache(final Pair<Set<ITerm>, Set<ITerm>> pair, final Set<Map<IVariable, ITerm>> map) {
		cartesianCache.put(pair, map);
	}

	public static void cache(final Set<ITerm> left, final Set<ITerm> right, final Set<Map<IVariable, ITerm>> map) {
		cache(Pair.of(left, right), map);
	}

	private static boolean inCache(final Pair<Set<ITerm>, Set<ITerm>> pair) {
		return cartesianCache.containsKey(pair);
	}

	public static boolean inCache(final Set<ITerm> left, final Set<ITerm> right) {
		return inCache(Pair.of(left, right));
	}

	public static Set<Map<IVariable, ITerm>> getCartesian(final Pair<Set<ITerm>, Set<ITerm>> pair) {
		return cartesianCache.get(pair);
	}

	public static Set<Map<IVariable, ITerm>> getCartesian(final Set<ITerm> left, final Set<ITerm> right) {
		return cartesianCache.get(Pair.of(left, right));
	}

	public long size() {
		return cartesianCache.size();
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		sb.append("CARTESIAN CACHE");
		for (final Pair<Set<ITerm>, Set<ITerm>> p : cartesianCache.keySet()) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}

		return sb.toString();
	}
}
