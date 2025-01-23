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
package org.deri.iris.rules;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.terms.IConstructedTerm;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.builtins.ArithmeticBuiltin;
import org.deri.iris.builtins.EqualBuiltin;
import org.deri.iris.utils.TermMatchingAndSubstitution;

/**
 * We use the definition of a safe rule as described by Ullman, page 105. A rule is safe if all variables are limited. A
 * variable is limited if: 1) It appears in a positive ordinary predicate 2) It appears in a positive equality with a
 * constant, e.g. ?X = 'a' 3) It appears in a positive equality with another variable known to be limited, e.g. ?X = ?Y,
 * ?Y = 'a' However, variables that ONLY appear in a negated ordinary predicate (and nowhere else) can still make for a
 * safe rule, as such a rule can be re-written to move the negated sub-goal to a separate rule, see the example in
 * Ullman, page 129-130 Furthermore, variables that appear in arithmetic predicates can also be considered limited if
 * all the remaining variables are limited, e.g. X + Y = Z, X = 3, Z = 4, implies that Y is also limited Furthermore,
 * rules with unbounded, existential variables in the head can also be considered safe if there exists an atom in the
 * body which contains ALL the universally quantified variables of the rule (Calì, Gottlob, Lukasiewic 2009). These
 * three relaxations of the definition of a safe rule are configurable (on/off).
 */
public class RuleValidator {
	/**
	 * Constructor. Each instance of this rule can process exactly one rule, after which it must be discarded.
	 * @param allowNotLimitedVariablesInNegatedSubGoals false, if the strict Ullman definition should be enforced for
	 *            variables in negated sub-goals.
	 * @param limitedTernaryOperandsImplyLimitedResult false, if the strict Ullman definition should be enforced for
	 *            variables in that are in arithmetic predicates.
	 * @param allowGuardedRules false, if existentially quantified variables in rule head are not allowed in the
	 *            program.
	 */
	public RuleValidator(final IRule rule, final boolean allowNotLimitedVariablesInNegatedSubGoals,
	        final boolean allowArithmeticPredicatesToImplyLimited, final boolean allowGuardedRules) {
		mRule = rule;
		mAllowNotLimitedVariablesInNegatedSubGoals = allowNotLimitedVariablesInNegatedSubGoals;
		mAllowArithmeticPredicatesToImplyLimited = allowArithmeticPredicatesToImplyLimited;
		mAllowGuardedRules = allowGuardedRules;

		// Add all the head variables
		for (final ILiteral headLiteral : rule.getHead()) {
			addHeadVariables(extractVariables(headLiteral));
		}

		// Then for each literal in the rule
		for (final ILiteral lit : rule.getBody()) {
			// If it has any variables at all
			if (!lit.getAtom().isGround()) {
				final boolean positive = lit.isPositive();
				final IAtom atom = lit.getAtom();
				;
				final List<IVariable> variables = extractVariables(lit);
				final boolean builtin = lit.getAtom().isBuiltin();

				if (builtin) {
					if (positive && isEquality(atom)) {
						final ITuple tuple = atom.getTuple();
						assert tuple.size() == 2;

						final Map<IVariable, ITerm> variableMap = new HashMap<IVariable, ITerm>();
						if (TermMatchingAndSubstitution.unify(tuple.get(0), tuple.get(1), variableMap)) {
							for (final Map.Entry<IVariable, ITerm> entry : variableMap.entrySet()) {
								final List<IVariable> variableMapping = new ArrayList<IVariable>();
								variableMapping.add(entry.getKey());
								if (entry.getValue() instanceof IVariable) {
									variableMapping.add((IVariable) entry.getValue());
									addVariablesFromPositiveArithmeticPredicate(true, variableMapping);
								} else if (entry.getValue() instanceof IConstructedTerm) {
									final IConstructedTerm constructedTerm = (IConstructedTerm) entry.getValue();
									final Set<IVariable> constructedArgs = constructedTerm.getVariables();

									if (constructedArgs.size() == 0) {
										// Effectively: variable = ground term
										addVariablesFromPositiveArithmeticPredicate(true, variableMapping);
									} else if (constructedArgs.size() == 1) {
										// e.g. ?X = f(?Z)
										variableMapping.add(constructedArgs.iterator().next());
										addVariablesFromPositiveArithmeticPredicate(true, variableMapping);
									} else {
										// e.g. ?X = f(?Y,?Z)
										addVariableDependancy(entry.getKey(), constructedArgs);
									}
								} else {
									// => variable = ground term
									addVariablesFromPositiveArithmeticPredicate(true, variableMapping);
								}
							}
						}
					} else if (positive && isArithmetic(atom)) {
						addVariablesFromPositiveArithmeticPredicate(isEquality(atom), variables);
					} else {
						addVariablesFromBuiltinPredicate(variables);
					}
				} else {
					// Ordinary predicate
					addVariablesFromOrdinaryPredicate(positive, variables);
				}
			}
		}

		processBuiltinsAndDependencies();
	}

	/**
	 * Add variables that appears in the rule head.
	 * @param variables The variable names.
	 */
	private void addHeadVariables(final List<IVariable> variables) {
		mHeadVariables.addAll(variables);
	}

	/**
	 * Add variables that appear in an ordinary predicate.
	 * @param positive true if the predicate is positive, i.e. not negated.
	 * @param variables The variable names.
	 */
	private void addVariablesFromOrdinaryPredicate(final boolean positive, final List<IVariable> variables) {
		if (positive) {
			mLimitedVariables.addAll(variables);
		} else {
			mNegativeOrdinary.addAll(variables);
		}
	}

	/**
	 * Add variables from any built-in predicate other than positive arithmetic and equality predicates.
	 * @param variables The variable names.
	 */
	private void addVariablesFromBuiltinPredicate(final List<IVariable> variables) {
		mBuiltin.addAll(variables);
	}

	/**
	 * Add variables from arithmetic or equality predicates
	 * @param isEquality true if the predicate is equality.
	 * @param variables The variable names.
	 */
	private void addVariablesFromPositiveArithmeticPredicate(final boolean isEquality, final List<IVariable> variables) {
		mBuiltin.addAll(variables);

		if (isEquality || mAllowArithmeticPredicatesToImplyLimited) {
			mArithmeticGroups.add(variables);
		}
	}

	/**
	 * @return The universally quantified variables in the rule body
	 */
	public Set<IVariable> getUniversalVariables() {

		return (mRule.getBodyVariables());
	}

	/**
	 * @return The existential variables in the rule head.
	 */
	public List<IVariable> getExistentialVariables() {
		final List<IVariable> result = new ArrayList<IVariable>();

		final List<IVariable> unlimitedHeadVariables = new ArrayList<IVariable>(mHeadVariables);
		unlimitedHeadVariables.removeAll(mLimitedVariables);

		result.addAll(unlimitedHeadVariables);

		return (result);
	}

	public List<IVariable> getAllUnlimitedVariables() {

		final Set<IVariable> result = new HashSet<IVariable>();

		final List<IVariable> unlimitedBuiltinVariables = new ArrayList<IVariable>(mBuiltin);
		unlimitedBuiltinVariables.removeAll(mLimitedVariables);

		result.addAll(unlimitedBuiltinVariables);

		if (!mAllowNotLimitedVariablesInNegatedSubGoals) {
			final List<IVariable> unlimitedNegativeOrdinaryVariables = new ArrayList<IVariable>(mNegativeOrdinary);
			unlimitedNegativeOrdinaryVariables.removeAll(mLimitedVariables);

			result.addAll(unlimitedNegativeOrdinaryVariables);
		}

		if (mAllowGuardedRules) {

			// Check if the rule is a TGD, then check the guardness of the rule:

			// Get all the universally quantified variables
			final Set<IVariable> universalVariables = getUniversalVariables();

			boolean guarded = false;

			for (final ILiteral literal : mRule.getBody()) {
				/*
				 * Check if there exists a positive literal in the body that contains all the quantified variables.
				 */
				if (literal.isPositive()) {
					final List<IVariable> atomVariables = literal.getAtom().getTuple().getAllVariables();
					if (atomVariables.containsAll(universalVariables)) {
						guarded = true;
					}
				}
			}
			if (!guarded) {
				result.addAll(mHeadVariables);
			}
		}
		return new ArrayList<IVariable>(result);
	}

	public boolean isSaneTGD() {

		// Check if the rule is a TGD
		final Iterator<IVariable> uIt = getUniversalVariables().iterator();

		while (uIt.hasNext()) {
			final IVariable v = uIt.next();
			if (mHeadVariables.contains(v))
				return (true);
		}
		return (false);
	}

	/**
	 * Do the special case handling of built-in predicates.
	 */
	private void processBuiltinsAndDependencies() {
		// Process the positive arithmetic predicates
		boolean changed = true;
		while (changed) {
			changed = false;
			for (final List<IVariable> group : mArithmeticGroups) {
				if (group.removeAll(mLimitedVariables)) {
					changed = true;
				}

				if (group.size() == 1) {
					mLimitedVariables.add(group.get(0));
					group.clear();
					changed = true;
				}
			}

			final Iterator<Map.Entry<IVariable, Set<IVariable>>> fnIterator = mVariableDependancies.entrySet()
			        .iterator();
			while (fnIterator.hasNext()) {
				final Map.Entry<IVariable, Set<IVariable>> entry = fnIterator.next();
				final Set<IVariable> dependents = entry.getValue();
				if (dependents.removeAll(mLimitedVariables)) {
					changed = true;
				}

				if (dependents.size() == 0) {
					mLimitedVariables.add(entry.getKey());
					fnIterator.remove();
					changed = true;
				}
			}
		}
	}

	/**
	 * Get the variable terms in a literal.
	 * @param literal The literal to be processed.
	 * @return The names of variables.
	 */
	private List<IVariable> extractVariables(final ILiteral literal) {
		return literal.getAtom().getTuple().getAllVariables();
	}

	/**
	 * Utility to check if an atom is an equality built-in
	 * @param atom The atom to check
	 * @return true if it is
	 */
	private boolean isEquality(final IAtom atom) {
		return atom instanceof EqualBuiltin;
	}

	/**
	 * Utility to check if an atom is one of the ternary arithmetic built-ins
	 * @param atom The atom to check
	 * @return true if it is
	 */
	private boolean isArithmetic(final IAtom atom) {
		return atom instanceof ArithmeticBuiltin;
	}

	/** Indicate a (one-way) variable dependency on other variables. */
	private void addVariableDependancy(final IVariable variable, final Set<IVariable> dependents) {
		mVariableDependancies.put(variable, dependents);
	}

	/**
	 * Flag to indicate if variables in negated sub goals must be limited or not.
	 */
	private final boolean mAllowNotLimitedVariablesInNegatedSubGoals;

	/**
	 * Flag to indicate if limited variables as operands of a ternary operator imply that the target is also limited.
	 */
	private final boolean mAllowArithmeticPredicatesToImplyLimited;

	/** Flag to indicate if guarded rules are allowed */
	private final boolean mAllowGuardedRules;

	/** All head variables. */
	private final Set<IVariable> mHeadVariables = new HashSet<IVariable>();

	/** All variables from negated ordinary predicates. */
	private final Set<IVariable> mNegativeOrdinary = new HashSet<IVariable>();

	/**
	 * All variables from built-in predicates, EXCEPT the targets of positive, ternary predicates.
	 */
	private final Set<IVariable> mBuiltin = new HashSet<IVariable>();

	/**
	 * All variables that appear in 'variable = variable' positive, equality predicates.
	 */
	private final List<List<IVariable>> mArithmeticGroups = new ArrayList<List<IVariable>>();

	/** All limited variables. */
	private final Set<IVariable> mLimitedVariables = new HashSet<IVariable>();

	/** To hold dependencies detected when unifying terms. */
	private final Map<IVariable, Set<IVariable>> mVariableDependancies = new HashMap<IVariable, Set<IVariable>>();

	/** Stores the rule to be validated */
	private final IRule mRule;

}
