/**
 * 
 */
package org.deri.iris.queryrewriting.caching;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.basics.ILiteral;

/**
 * @author Giorgio Orsi
 */
public class MapsToCache {
	public static enum CacheType {
		MAPSTO, NOT_MAPSTO;
	}

	private static Set<Pair<Set<ILiteral>, Set<ILiteral>>> mapsToCache;
	private static Set<Pair<Set<ILiteral>, Set<ILiteral>>> notMapsToCache;

	private static MapsToCache instance;

	public static MapsToCache getCache() {
		if (instance == null) {
			instance = new MapsToCache();
		}
		return instance;
	}

	public static MapsToCache getClearCache() {
		return new MapsToCache();
	}

	public void clearCache(final CacheType type) {
		if (type.equals(CacheType.MAPSTO)) {
			mapsToCache.clear();
		} else {
			notMapsToCache.clear();
		}
	}

	private MapsToCache() {
		//Marco: make sets thread-safe
		mapsToCache = Collections.synchronizedSet(new LinkedHashSet<Pair<Set<ILiteral>, Set<ILiteral>>>());
		notMapsToCache = Collections.synchronizedSet(new LinkedHashSet<Pair<Set<ILiteral>, Set<ILiteral>>>());
	}

	private static void cache(final Pair<Set<ILiteral>, Set<ILiteral>> pair, final CacheType type) {
		if (type.equals(CacheType.MAPSTO)) {
			mapsToCache.add(pair);
		} else {
			notMapsToCache.add(pair);
		}
	}

	public static void cache(final Set<ILiteral> left, final Set<ILiteral> right, final CacheType type) {
		cache(Pair.of(left, right), type);
	}

	private static boolean inCache(final Pair<Set<ILiteral>, Set<ILiteral>> pair, final CacheType type) {
		if (type.equals(CacheType.MAPSTO))
			return mapsToCache.contains(pair);
		else
			return notMapsToCache.contains(pair);
	}

	public static boolean inCache(final Set<ILiteral> left, final Set<ILiteral> right, final CacheType type) {
		return inCache(Pair.of(left, right), type);
	}

	public static long size(final CacheType type) {
		if (type.equals(CacheType.MAPSTO))
			return mapsToCache.size();
		else
			return notMapsToCache.size();
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		sb.append("MAPSTO CACHE");
		for (final Pair<Set<ILiteral>, Set<ILiteral>> p : mapsToCache) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}
		sb.append(IOUtils.LINE_SEPARATOR);
		sb.append("NOT MAPSTO CACHE");
		for (final Pair<Set<ILiteral>, Set<ILiteral>> p : notMapsToCache) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}

		return sb.toString();
	}
}
