/*
 * Integrated Rule Inference System (IRIS+-):
 * An extensible rule inference system for datalog with extensions.
 * 
 * Copyright (C) 2009 ICT Institute - Dipartimento di Elettronica e Informazione (DEI), 
 * Politecnico di Milano, Via Ponzio 34/5, 20133 Milan, Italy.
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
package org.deri.iris.queryrewriting;

import org.deri.iris.api.basics.IPosition;

/**
 * @author Giorgio Orsi <orsi@elet.polimi.it> - Politecnico di Milano
 * @version 1.0
 */
public class PositionJoin implements Comparable<PositionJoin> {

  private IPosition leftPosition;
  private IPosition rightPosition;
  private int count;

  public PositionJoin(final IPosition p1, final IPosition p2, final int count) {
    setLeftPosition(p1);
    setRightPosition(p2);
    setCount(count);
  }

  /**
   * @return the leftPosition
   */
  public IPosition getLeftPosition() {
    return leftPosition;
  }

  /**
   * @param leftPosition
   *          the leftPosition to set
   */
  public void setLeftPosition(final IPosition leftPosition) {
    this.leftPosition = leftPosition;
  }

  /**
   * @return the rightPosition
   */
  public IPosition getRightPosition() {
    return rightPosition;
  }

  /**
   * @param rightPosition
   *          the rightPosition to set
   */
  public void setRightPosition(final IPosition rightPosition) {
    this.rightPosition = rightPosition;
  }

  /**
   * @return the count
   */
  public int getCount() {
    return count;
  }

  /**
   * @param count
   *          the count to set
   */
  public void setCount(final int count) {
    this.count = count;
  }

  @Override public boolean equals(final Object o) {

    if (!(o instanceof PositionJoin))
      return false;

    final PositionJoin j = (PositionJoin) o;
    if ((getLeftPosition().equals(j.getLeftPosition()) && getRightPosition().equals(j.getRightPosition()) || getLeftPosition()
        .equals(j.getRightPosition()) && getRightPosition().equals(j.getLeftPosition()))
        && getCount() == j.getCount())
      return true;
    else
      return false;
  }

  @Override public String toString() {
    return getLeftPosition() + " >< " + getRightPosition() + " : " + "[" + getCount() + "]";
  }

  @Override public int compareTo(final PositionJoin pj) {
    if (equals(pj))
      return 0;
    else
      return getLeftPosition().compareTo(pj.getLeftPosition());
  }

  @Override public int hashCode() {
    return getLeftPosition().hashCode() * 37 + getRightPosition().hashCode() * 37 + getCount() * 17;
  }

}
