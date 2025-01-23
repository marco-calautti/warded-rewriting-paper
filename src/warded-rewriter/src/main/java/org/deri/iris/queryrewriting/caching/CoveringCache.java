/**
 * 
 */
package org.deri.iris.queryrewriting.caching;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.basics.ILiteral;

/**
 * @author Giorgio Orsi
 */
public class CoveringCache {
	public static enum CacheType {
		COVERING, NOT_COVERING;
	}

	private static Set<Pair<ILiteral, ILiteral>> coveringCache;
	private static Set<Pair<ILiteral, ILiteral>> nonCoveringCache;

	private static CoveringCache instance;

	public static CoveringCache getCache() {
		if (instance == null) {
			instance = new CoveringCache();
		}
		return instance;
	}

	public static CoveringCache getClearCache() {
		return new CoveringCache();
	}

	public void clearCache(final CacheType type) {
		if (type.equals(CacheType.COVERING)) {
			coveringCache.clear();
		} else {
			nonCoveringCache.clear();
		}
	}

	private CoveringCache() {
		//Marco: make sets thread-safe
		coveringCache = Collections.synchronizedSet(new HashSet<Pair<ILiteral, ILiteral>>(300000));
		nonCoveringCache = Collections.synchronizedSet(new HashSet<Pair<ILiteral, ILiteral>>(300000));
	}

	private static void cache(final Pair<ILiteral, ILiteral> pair, final CacheType type) {
		if (type.equals(CacheType.COVERING)) {
			coveringCache.add(pair);
		} else {
			nonCoveringCache.add(pair);
		}
	}

	public static void cache(final ILiteral left, final ILiteral right, final CacheType type) {
		cache(Pair.of(left, right), type);
	}

	private static boolean inCache(final Pair<ILiteral, ILiteral> pair, final CacheType type) {
		if (type.equals(CacheType.COVERING))
			return coveringCache.contains(pair);
		else
			return nonCoveringCache.contains(pair);
	}

	public static boolean inCache(final ILiteral left, final ILiteral right, final CacheType type) {
		assert left != null;
		assert right != null;
		return inCache(Pair.of(left, right), type);
	}

	public long size(final CacheType type) {
		if (type.equals(CacheType.COVERING))
			return coveringCache.size();
		else
			return nonCoveringCache.size();
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		sb.append("COVERING CACHE");
		for (final Pair<ILiteral, ILiteral> p : coveringCache) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}
		sb.append(IOUtils.LINE_SEPARATOR);
		sb.append("NON-COVERING CACHE");
		for (final Pair<ILiteral, ILiteral> p : nonCoveringCache) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}

		return sb.toString();
	}
}
