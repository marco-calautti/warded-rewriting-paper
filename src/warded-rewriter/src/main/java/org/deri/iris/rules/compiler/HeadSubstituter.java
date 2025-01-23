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
import org.deri.iris.EvaluationException;
import org.deri.iris.RuleUnsafeException;
import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.storage.IRelation;
import org.deri.iris.utils.TermMatchingAndSubstitution;

/**
 * A compiled rule element representing the substitution of variable bindings in
 * to the rule head.
 */
public class HeadSubstituter extends RuleElement {
    /**
     * Constructor.
     * 
     * @param variables
     *            The variables from the rule body.
     * @param headTuple
     *            The tuple from the rule head.
     * @throws EvaluationException
     */
    public HeadSubstituter(List<IVariable> variables, IAtom headAtom,
	    Configuration configuration) throws EvaluationException {
	assert variables != null;
	assert headAtom != null;
	assert configuration != null;

	mConfiguration = configuration;

	mHeadAtom = headAtom;

	// Work out the indices of variables in substitution order
	List<IVariable> variablesToSubstitute = TermMatchingAndSubstitution
		.getVariables(mHeadAtom.getTuple(), false);
	mIndices = new int[variablesToSubstitute.size()];

	int i = 0;
	for (IVariable variable : variablesToSubstitute) {
	    int index = variables.indexOf(variable);
	    if (index < 0)
		//if (guardedRules)
		    /*
		     * In the original IRIS, here a RuleUnsafeException(
		     * "Unbound variable in rule head: " + variable ) is thrown.
		     * We relax the constraint in order to accept unbounded
		     * variables in the head.
		     */
		    mIndices[i++] = -1;
		//else
		//    throw new RuleUnsafeException(
		//	    "Unbound variable in rule head: " + variable);
	    else
		mIndices[i++] = index;
	}
    }

    @Override
    public IRelation process(IRelation inputRelation) {
	assert inputRelation != null;

	IRelation result = mConfiguration.relationFactory.createRelation();

	for (int i = 0; i < inputRelation.size(); ++i) {
	    ITuple inputTuple = inputRelation.get(i);

	    ITuple outputTuple = TermMatchingAndSubstitution
		    .substituteVariablesInToTuple(mHeadAtom, inputTuple,
			    mIndices);

	    result.add(outputTuple);
	}

	return result;
    }

    public ITuple getHeadTuple() {
	return ( this.mHeadAtom.getTuple() );
    }
    
    public IPredicate getPredicate() {
	return ( this.mHeadAtom.getPredicate() );
    }
    
    /** The rule head tuple. */
    private final IAtom mHeadAtom;

    /** The indices of variables in substitution order. */
    private final int[] mIndices;

    /** The knowledge-base's configuration object. */
    private final Configuration mConfiguration;
}
