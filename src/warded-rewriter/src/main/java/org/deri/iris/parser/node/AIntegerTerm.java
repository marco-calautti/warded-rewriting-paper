/* This file was generated by SableCC (http://www.sablecc.org/). */

package org.deri.iris.parser.node;

import org.deri.iris.parser.analysis.Analysis;

@SuppressWarnings("nls")
public final class AIntegerTerm extends PTerm
{
    private TTInt _tInt_;

    public AIntegerTerm()
    {
        // Constructor
    }

    public AIntegerTerm(
        @SuppressWarnings("hiding") TTInt _tInt_)
    {
        // Constructor
        setTInt(_tInt_);

    }

    @Override
    public Object clone()
    {
        return new AIntegerTerm(
            cloneNode(this._tInt_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAIntegerTerm(this);
    }

    public TTInt getTInt()
    {
        return this._tInt_;
    }

    public void setTInt(TTInt node)
    {
        if(this._tInt_ != null)
        {
            this._tInt_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._tInt_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._tInt_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._tInt_ == child)
        {
            this._tInt_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._tInt_ == oldChild)
        {
            setTInt((TTInt) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
