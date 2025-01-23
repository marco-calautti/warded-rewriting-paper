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
package org.deri.iris.api.basics;

import java.util.Collection;
import java.util.List;
import java.util.Set;

import org.deri.iris.api.terms.ITerm;
import org.deri.iris.api.terms.IVariable;

/**
 * <p>
 * Represents a rule in the program. A rule has a form:
 * </p>
 * <p>
 * q :- p1, p2,...,pn
 * </p>
 * <p>
 * where q is a positive literal (the head), and p1, p2,...,pn is a conjunction of several literals (the body). Only
 * safe rules are supported. A rule is safe if its every variable occurs in one of its positive, non built-in, atoms of
 * the body.
 * </p>
 * <p>
 * $Id: IRule.java,v 1.9 2007-10-30 08:28:27 poettler_ric Exp $
 * </p>
 * 
 * @author Darko Anicic, DERI Innsbruck
 * @version $Revision: 1.9 $
 */
public interface IRule {
  /**
   * Get the rule head-
   * 
   * @return The rule head.
   */
  public Set<ILiteral> getHead();

  /**
   * Get the rule body.
   * 
   * @return The rule body.
   */
  public Set<ILiteral> getBody();

  /**
   * <p>
   * A rule is rectified if its head has the same form as heads of the other rules from the program, e.g. p(X1,...,Xk)
   * for variables X1,...,Xk.
   * </p>
   * <p>
   * For a given pair of rules:
   * </p>
   * <ul>
   * <li>p(a, X, Y) :- r(X, Y)</li>
   * <li>p(X, Y, X) :- r(Y, X)</li>
   * </ul>
   * <p>
   * after the rectification we get the following rules:
   * </p>
   * <ul>
   * <li>p(U, V, W) :- r(V, W), U='a'.</li>
   * <li>p(U, V, W) :- r(V, U), W=U.</li>
   * </ul>
   * <p>
   * where both rules have heads of the same form.
   * </p>
   * 
   * @return True if the rule is rectified; otherwise false.
   */
  public boolean isRectified();

  /**
   * Returns the variables in the body of the rule
   * 
   * @return the body variables
   */
  public Set<IVariable> getBodyVariables();

  /**
   * Returns the variables in the head of the rule
   * 
   * @return the head variables
   */
  public Set<IVariable> getHeadVariables();

  /**
   * Returns the existential variables in the of the head of the rule
   * 
   * @return the existential variables
   */
  public Set<IVariable> getExistentialVariables();

  /**
   * Return the positions of a term in the body of the rule
   * 
   * @param t
   *          the term
   * @return the positions of the term in the body of the rule
   */
  public Set<IPosition> getTermBodyPositions(ITerm t);

  /**
   * Return the positions of a term in the head of the rule
   * 
   * @param t
   *          the term
   * @return the positions of the term in the head of the rule
   */
  public Set<IPosition> getTermHeadPositions(ITerm t);

  /**
   * Return all the positions in this rule
   * 
   * @return the positions in this rule
   */
  public Set<IPosition> getRulePositions();

  // public IRule canonize();

  public Set<ITerm> getBodyTerms(IPosition p);

  public List<IPosition> getExistentialPositions(IRule r);

  public Set<IPosition> getExistentialPositions();

  public Set<IPosition> getPositions(ITerm v);

  public Set<IPredicate> getPredicates();

  public Set<ILiteral> getAllLiterals();

  public boolean isShared(ITerm t);

  Set<ITerm> getBodyTerms(Set<IPosition> positions);

  Set<IPredicate> getBodyPredicates();

  Set<IPredicate> getHeadPredicates();

  Set<IVariable> getFrontierVariables();

  Set<IVariable> getAllVariables();

  Set<IPosition> getHeadPositions();

  Set<IPosition> getBodyPositions();

  Set<IVariable> getBodyVariables(Set<IPosition> positions);

  Set<IVariable> getBodyVariables(IPosition p);

  Set<IPosition> getBodyPositions(Collection<? extends ITerm> terms);

  Set<IPosition> getHeadPositions(Collection<? extends ITerm> terms);

  Set<IVariable> getHeadVariables(IPosition p);

  Set<IVariable> getHeadVariables(Set<IPosition> positions);

  @Override boolean equals(Object o);

}
