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
package org.deri.iris.rules.compiler;

import java.util.List;

import org.deri.iris.Configuration;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.facts.IFacts;
import org.deri.iris.storage.IRelation;

/**
 * A compiled rule element representing the first literal in a rule body, when
 * that literal is a positive ordinary predicate.
 */
public class FirstSubgoal extends BodyRuleElement {
    /**
     * Constructor.
     * 
     * @param predicate
     *            The predicate for this literal.
     * @param relation
     *            The relation for this literal.
     * @param viewCriteria
     *            The tuple from the sub-goal in the rule.
     */
    public FirstSubgoal(IPredicate predicate, IRelation relation,
	    ITuple viewCriteria, Configuration configuration) {
	assert predicate != null;
	assert relation != null;
	assert viewCriteria != null;
	assert configuration != null;

	mConfiguration = configuration;

	mView = new View(relation, viewCriteria, mConfiguration.relationFactory);

	mPredicate = predicate;
	mViewCriteria = viewCriteria;
	mOutputVariables = mView.variables();
    }

    /**
     * Constructor used for iterative evaluation.
     * 
     * @param predicate
     *            The predicate for this literal.
     * @param relation
     *            The relation for this literal.
     * @param viewCriteria
     *            The tuple from the sub-goal in the rule.
     * @param variables
     *            Calculated variables.
     * @param simple
     *            Indicator if the view is a simple one (only unique variables).
     */
    public FirstSubgoal(IPredicate predicate, IRelation relation,
	    ITuple viewCriteria, List<IVariable> variables, boolean simple,
	    Configuration configuration) {
	assert predicate != null;
	assert relation != null;
	assert viewCriteria != null;
	assert configuration != null;

	mConfiguration = configuration;

	mView = new View(relation, viewCriteria, variables, simple,
		mConfiguration.relationFactory);

	mPredicate = predicate;
	mViewCriteria = viewCriteria;
	mOutputVariables = mView.variables();
    }

    @Override
    public IRelation process(IRelation leftRelation) {
	assert leftRelation != null;
	assert leftRelation.size() == 1; // i.e. there is no left relation, just
					 // a starting point.

	return mView;
    }

    @Override
    public RuleElement getDeltaSubstitution(IFacts deltas) {
	IRelation delta = deltas.get(mPredicate);

	if (delta == null || delta.size() == 0)
	    return null;

	return new FirstSubgoal(mPredicate, delta, mViewCriteria, mView
		.variables(), mView.isSimple(), mConfiguration);
    }

    public IPredicate getPredicate() {
	return (mPredicate);
    }

    public View getView() {
	return (mView);
    }

    /** Predicate of the literal. */
    private final IPredicate mPredicate;

    /** The tuple from the sub-goal in the rule. */
    private final ITuple mViewCriteria;

    /** The view on this literal. */
    private final View mView;

    private final Configuration mConfiguration;
}
