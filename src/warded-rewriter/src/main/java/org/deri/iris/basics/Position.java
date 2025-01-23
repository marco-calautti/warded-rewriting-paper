package org.deri.iris.basics;

import org.deri.iris.api.basics.IPosition;

public class Position implements IPosition, Comparable<IPosition> {

	private String pred;
	private int position;

	public Position(final String pred, final int position) {
		this.pred = pred;
		this.position = position;
	}

	/**
	 * @return the predicate.
	 */
	@Override
	public String getPredicate() {
		return (pred);
	}

	/**
	 * @param pred The predicate.
	 */
	public void setPred(final String pred) {
		this.pred = pred;
	}

	@Override
	public int hashCode() {
		return (position * 37) + pred.hashCode();
	}

	/**
	 * @return the position within the predicate.
	 */
	@Override
	public int getPosition() {
		return position;
	}

	/**
	 * @param position the position within the predicate.
	 */
	public void setPosition(final int position) {
		this.position = position;
	}

	@Override
	public boolean equals(final Object o) {
		return (compareTo((IPosition) o) == 0);
	}

	@Override
	public String toString() {
		return (getPredicate() + "[" + getPosition() + "]");
	}

	@Override
	public int compareTo(final IPosition o) {
		if (!(o instanceof IPosition))
			return -1;

		if (!(o.getPredicate().equals(getPredicate())))
			return -1;
		else {
			if (o.getPosition() < getPosition())
				return (-1);
			else if (o.getPosition() > getPosition())
				return (1);
			else
				return (0);
		}

	}

}
