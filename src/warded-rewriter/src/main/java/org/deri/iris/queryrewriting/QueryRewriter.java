/**
 * 
 */
package org.deri.iris.queryrewriting;

import java.util.Set;
import java.util.concurrent.Callable;

import org.deri.iris.api.basics.IRule;

/**
 * @author jd
 */
public interface QueryRewriter extends Callable<Set<IRule>> {

	Set<IRule> rewrite();

}
