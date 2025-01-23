/**
 * 
 */
package org.deri.iris.queryrewriting.caching;

/**
 * @author jd
 */
public class CacheManager {

	public static void setupCaching() {

		CoveringCache.getClearCache();

		MapsToCache.getClearCache();

		CartesianCache.getClearCache();

		MGUCache.getClearCache();

		RenamingCache.getClearCache();
	}
}
