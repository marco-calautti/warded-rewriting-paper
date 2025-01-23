/**
 * 
 */
package org.deri.iris.api.queryrewriting;

import java.util.List;
import java.util.Set;

import org.deri.iris.EvaluationException;
import org.deri.iris.api.basics.IRule;

/**
 * An interface for all the conjunctive query rewriting algorithms.
 * 
 * @author Giorgio Orsi (orsi at elet dot polimi dot it)
 *
 */
public interface IQueryRewriter {
    
    public List<Set<IRule>> getRewritings(List<IRule> queries) throws EvaluationException;
    
    public Set<IRule> getRewriting(IRule query) throws EvaluationException;
 
}
