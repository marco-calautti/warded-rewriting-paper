/**
 * 
 */
package org.deri.iris.queryrewriting.caching;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.basics.IRule;

/**
 * @author jd
 */
public class RenamingCache {

	private static Map<Pair<IRule, String>, IRule> renamingCache;

	private static RenamingCache instance;

	public static RenamingCache getCache() {
		if (instance == null) {
			instance = new RenamingCache();
		}
		return instance;
	}

	public static RenamingCache getClearCache() {
		return new RenamingCache();
	}

	public void clearCache() {
		renamingCache.clear();
	}

	private RenamingCache() {
		//Marco: make map thread-safe
		renamingCache = Collections.synchronizedMap(new LinkedHashMap<Pair<IRule, String>, IRule>());
	}

	private static void cache(final Pair<IRule, String> pair, final IRule renamed) {
		renamingCache.put(pair, renamed);
	}

	public static void cache(final IRule literals, final String pattern, final IRule renamed) {
		cache(Pair.of(literals, pattern), renamed);
	}

	private static boolean inCache(final Pair<IRule, String> pair) {
		return renamingCache.containsKey(pair);
	}

	public static boolean inCache(final IRule literals, final String pattern) {
		return inCache(Pair.of(literals, pattern));
	}

	public static IRule getRenamed(final Pair<IRule, String> pair) {
		return renamingCache.get(pair);
	}

	public static IRule getRenamed(final IRule literals, final String pattern) {
		return renamingCache.get(Pair.of(literals, pattern));
	}

	public static long size() {
		return renamingCache.size();
	}

	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		sb.append("SUBSUMED CACHE");
		for (final Pair<IRule, String> p : renamingCache.keySet()) {
			sb.append(p);
			sb.append(IOUtils.LINE_SEPARATOR);
		}
		return sb.toString();
	}

}
