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

import java.util.ArrayList;
import java.util.List;

import org.deri.iris.Configuration;
import org.deri.iris.EvaluationException;
import org.deri.iris.api.basics.IPosition;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.basics.Position;
import org.deri.iris.factory.Factory;
import org.deri.iris.facts.IFacts;
import org.deri.iris.storage.IRelation;
import org.deri.iris.storage.RelationFactory;

/**
 * A compiled rule.
 */
public class CompiledRule implements ICompiledRule {
	/**
	 * Constructor.
	 * @param elements The rule elements produced by the rule compiler.
	 * @param headPredicate The head predicate of the original rule.
	 */
	public CompiledRule(final List<RuleElement> elements, final IPredicate headPredicate,
	        final Configuration configuration) {
		assert elements.size() > 0;
		assert configuration != null;

		mConfiguration = configuration;

		mHeadPredicate = headPredicate;

		mElements = elements;

	}

	/**
	 * Evaluate the rule. Each element is called in turn to produce tuples to pass on to the next rule element. If any
	 * rule element outputs an empty relation, then stop.
	 * @throws EvaluationException
	 */
	@Override
	public IRelation evaluate() throws EvaluationException {
		// The first literal receives the starting relation (which has one zero
		// length tuple in it). */
		IRelation output = mStartingRelation;

		for (final RuleElement element : mElements) {
			output = element.process(output);

			// Must always get some output relation, even if it is empty.
			assert output != null;

			// All literals are conjunctive, so if any literal produces no
			// results,
			// then the whole rule produces no results.
			if (output.size() == 0) {
				break;
			}
		}

		return output;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.deri.iris.rules.compiler.ICompiledRule#evaluateIteratively(org.deri.iris.facts.IFacts)
	 */
	@Override
	public IRelation evaluateIteratively(final IFacts deltas) throws EvaluationException {
		final IRelation union = mConfiguration.relationFactory.createRelation();

		/*
		 * for each literal (rule element) for which there exists a delta substitution substitute the rule element with
		 * the delta evaluate the whole rule store the results combine all the results and return
		 */
		for (int r = 0; r < mElements.size(); ++r) {
			final RuleElement original = mElements.get(r);

			final RuleElement substitution = original.getDeltaSubstitution(deltas);

			if (substitution != null) {
				mElements.set(r, substitution);

				// Now just evaluate the modified rule
				final IRelation output = evaluate();

				for (int t = 0; t < output.size(); ++t) {
					union.add(output.get(t));
				}

				// Put the original rule element back the way it was
				mElements.set(r, original);
			}
		}

		return union;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.deri.iris.rules.compiler.ICompiledRule#headPredicate()
	 */
	@Override
	public IPredicate headPredicate() {
		return mHeadPredicate;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.deri.iris.rules.compiler.ICompiledRule#getVariablesBindings()
	 */
	@Override
	public List<IVariable> getVariablesBindings() {
		if (mElements.size() > 0)
			return mElements.get(mElements.size() - 1).getOutputVariables();
		else
			return new ArrayList<IVariable>();
	}

	/**
	 * Returns a list of IVariable objects representing the variables in the rule's body.
	 * @return The variables in the rule's body
	 */
	@Override
	public List<IVariable> getBodyVariables() {

		final List<IVariable> bodyVars = new ArrayList<IVariable>();

		if (mElements.size() > 0) {
			// Retrieve the variables from the rule body.
			for (int i = 0; i < (mElements.size() - 1); i++) {
				final BodyRuleElement curEl = (BodyRuleElement) mElements.get(i);
				for (int j = 0; j < curEl.getView().variables().size(); j++) {
					final IVariable curVar = curEl.getView().variables().get(j);
					if (!bodyVars.contains(curVar)) {
						bodyVars.add(curVar);
					}
				}
			}
		}

		return (bodyVars);

	}

	/**
	 * Returns a list of IVariable objects representing the variables in the rule's head.
	 * @return The variables in the rule's head.
	 */
	public List<IVariable> getHeadVariables() {

		final List<IVariable> headVars = new ArrayList<IVariable>();

		if (mElements.size() > 0) {
			// Retrieve the existentially quantified variables from the rule
			// head.
			headVars.addAll(((HeadSubstituter) mElements.get(mElements.size() - 1)).getHeadTuple().getAllVariables());
		}

		return (headVars);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.deri.iris.rules.compiler.ICompiledRule#getExistentiallyQuantifiedVariables()
	 */
	@Override
	public List<IVariable> getExistentiallyQuantifiedVariables() {

		final List<IVariable> exVars = new ArrayList<IVariable>();

		exVars.addAll(getHeadVariables());
		exVars.removeAll(getBodyVariables());

		return (exVars);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.deri.iris.rules.compiler.ICompiledRule#getLeftmostGuard(java.util.List)
	 */
	@Override
	public BodyRuleElement getLeftmostGuard(final List<IPosition> affectedPositions) {

		// Get the universally quantified variables in the body.
		final List<IVariable> uQtfied = getBodyVariables();

		// Get the universally quantified variables in affected positions in the body
		if (mElements.size() > 0) {
			/*
			 * Look for the left-most atom that contains all the universally quantified variables that appear only in
			 * affected positions in the body.
			 */
			for (int i = 0; i < (mElements.size() - 1); i++) {

				// Check whether the atom contains all the needed universally
				// quantified variables.
				final List<IVariable> atomVars = ((BodyRuleElement) mElements.get(i)).getView().variables();

				if (atomVars.containsAll(uQtfied))
					return ((BodyRuleElement) mElements.get(i));
			}
		}
		// This should not happen.
		return (null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String result = "";

		final HeadSubstituter head = (HeadSubstituter) mElements.get(mElements.size() - 1);

		result += "Head: " + head.getPredicate() + head.getHeadTuple() + "\n";
		result += "Body: ";
		for (int i = 0; i < (mElements.size() - 1); i++) {
			final BodyRuleElement ruleEl = (BodyRuleElement) mElements.get(i);
			result += ruleEl.getPredicate() + " " + ruleEl.getView() + ", ";
		}
		result += "\n";
		result = result.replace(", \n", "\n");
		return (result);
	}

	/** The starting relation for evaluating each sub-goal. */
	private static IRelation mStartingRelation = new RelationFactory().createRelation();;

	static {
		// Start the evaluation with a single, zero-length tuple.
		// TODO Check this!
		mStartingRelation.add(Factory.BASIC.createTuple());
	}

	/**
	 * Gets all the positions of the given variable within the body literals.
	 * @param body the body of the rule.
	 * @return the list of variable positions in the body
	 */
	public static List<IPosition> getVariableBodyPositions(final IVariable var, final List<RuleElement> ruleElements) {

		final List<IPosition> result = new ArrayList<IPosition>();

		// Check if the literal contains the needed variable
		for (int j = 0; j < (ruleElements.size() - 1); j++) {
			final BodyRuleElement curEl = (BodyRuleElement) ruleElements.get(j);
			final List<IVariable> vars = curEl.getView().variables();

			for (int i = 0; i < vars.size(); i++)
				if (vars.get(i).equals(var)) {
					result.add(new Position(curEl.getPredicate().getPredicateSymbol(), i + 1));
				}
		}

		return (result);
	}

	/** The rule elements in order. */
	private final List<RuleElement> mElements;

	/** The head predicate. */
	private final IPredicate mHeadPredicate;

	/** The engine configuration. */
	private final Configuration mConfiguration;
}
