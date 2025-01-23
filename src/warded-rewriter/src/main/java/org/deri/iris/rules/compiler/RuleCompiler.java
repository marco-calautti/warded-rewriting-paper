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
import java.util.Collection;
import java.util.List;

import org.deri.iris.Configuration;
import org.deri.iris.EvaluationException;
import org.deri.iris.api.basics.IAtom;
import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.api.basics.IQuery;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.api.builtins.IBuiltinAtom;
import org.deri.iris.api.terms.IConstructedTerm;
import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;
import org.deri.iris.facts.IFacts;
import org.deri.iris.storage.IRelation;
import org.deri.iris.storage.IRelationFactory;
import org.deri.iris.storage.RelationFactory;

/**
 * A rule compiler for creating objects that compute new facts using forward-chaining techniques.
 */
public class RuleCompiler {

  /**
   * Constructor.
   * 
   * @param facts
   *          The facts that will be used by the compiled rules.
   */
  public RuleCompiler(final IFacts facts, final Configuration configuration) {
    mFacts = facts;
    mConfiguration = configuration;
  }

  /**
   * Compile a rule. No optimisations of any kind are attempted.
   * 
   * @param rule
   *          The rule to be compiled
   * @return The compiled rule, ready to be evaluated
   * @throws EvaluationException
   *           If the query can not be compiled for any reason.
   */
  public ICompiledRule compile(final IRule rule) throws EvaluationException {
    final List<RuleElement> elements = compileBody(rule.getBody());

    List<IVariable> variables;

    if (elements.size() == 0) {
      variables = new ArrayList<IVariable>();
    } else {
      final RuleElement lastElement = elements.get(elements.size() - 1);
      variables = lastElement.getOutputVariables();
    }

    // Rule head
    final IAtom headAtom = rule.getHead().iterator().next().getAtom();
    final HeadSubstituter substituter = new HeadSubstituter(variables, headAtom, mConfiguration);
    elements.add(substituter);

    return new CompiledRule(elements, rule.getHead().iterator().next().getAtom().getPredicate(), mConfiguration);
  }

  /**
   * Compile a query. No optimisations of any kind are attempted.
   * 
   * @param query
   *          The query to be compiled
   * @return The compiled query, ready to be evaluated
   * @throws EvaluationException
   *           If the query can not be compiled for any reason.
   */
  public ICompiledRule compile(final IQuery query) throws EvaluationException {
    final List<RuleElement> elements = compileBody(query.getLiterals());

    return new CompiledRule(elements, null, mConfiguration);
  }

  /**
   * Compile a rule body (or query). The literals are compiled in the order given. However, if one literal can not be
   * compiled, because one or more of its variables are not bound from the proceeding literal, then it is skipped an
   * re-tried later.
   * 
   * @param bodyLiterals
   *          The list of literals to compile
   * @return The compiled rule elements.
   * @throws EvaluationException
   *           If a rule construct can not be compiled (e.g. a built-in has constructed terms)
   */
  private List<RuleElement> compileBody(final Collection<ILiteral> bodyLiterals) throws EvaluationException {
    final List<ILiteral> literals = new ArrayList<ILiteral>(bodyLiterals);

    final List<RuleElement> elements = new ArrayList<RuleElement>();

    List<IVariable> previousVariables = new ArrayList<IVariable>();

    while (elements.size() < bodyLiterals.size()) {
      EvaluationException lastException = null;

      boolean added = false;
      for (int l = 0; l < literals.size(); ++l) {
        final ILiteral literal = literals.get(l);
        final IAtom atom = literal.getAtom();
        final boolean positive = literal.isPositive();

        RuleElement element;

        try {
          if (atom instanceof IBuiltinAtom) {
            final IBuiltinAtom builtinAtom = (IBuiltinAtom) atom;

            boolean constructedTerms = false;
            for (final ITerm term : atom.getTuple()) {
              if (term instanceof IConstructedTerm) {
                constructedTerms = true;
                break;
              }
            }

            if (constructedTerms) {
              element = new BuiltinForConstructedTermArguments(previousVariables, builtinAtom, positive, mConfiguration);
            } else {
              element = new Builtin(previousVariables, builtinAtom, positive, mConfiguration);
            }
          } else {
            final IPredicate predicate = atom.getPredicate();
            IRelation relation;

            relation = mFacts.get(predicate);
            

            final ITuple viewCriteria = atom.getTuple();

            if (positive) {
              if (previousVariables.size() == 0) {
                // First sub-goal
                element = new FirstSubgoal(predicate, relation, viewCriteria, mConfiguration);
              } else {
                element = new Joiner(previousVariables, predicate, relation, viewCriteria, mConfiguration.indexFactory,
                    mConfiguration.relationFactory);
              }
            } else {
              // This *is* allowed to be the first literal for
              // rules such as:
              // p('a') :- not q('b')
              // or even:
              // p('a') :- not q(?X)
              element = new Differ(previousVariables, relation, viewCriteria, mConfiguration);
            }
          }
          previousVariables = element.getOutputVariables();

          elements.add(element);

          literals.remove(l);
          added = true;
          break;
        } catch (final EvaluationException e) {
          // Oh dear. Store the exception and try the next literal.
          lastException = e;
        }
      }
      if (!added)
        // No more literals, so the last error really was serious.
        throw lastException;
    }
    return elements;
  }

  /** The knowledge-base facts used to attach to the compiled rule elements. */
  private final IFacts mFacts;

  /** The knowledge-base configuration. */
  private final Configuration mConfiguration;
}
