package org.unimi;

import java.util.Set;

import org.deri.iris.api.basics.ILiteral;
import org.deri.iris.api.basics.IRule;
import org.deri.iris.api.basics.ITuple;
import org.deri.iris.queryrewriting.NormalizationUtils;

public class Component{
    
    private ITuple qTuple;
    private Set<ILiteral> qBody;
    private IRule query;
    private IRule canonicalQuery;

    private int hashCode;

    public Component(IRule query){
        this.query = query;
        this.canonicalQuery = NormalizationUtils.canonicalRenaming(query, "U");
        qTuple = canonicalQuery.getHead().iterator().next().getAtom().getTuple();
        qBody = canonicalQuery.getBody();
        hashCode = (qTuple.hashCode()+qBody.hashCode())*13;
    }


    public IRule getQuery(){
        return query;
    }

    public IRule getCanonicalQuery(){
        return canonicalQuery;
    }
    @Override
    public boolean equals(Object o){
        if(o == this)
            return true;
        
        if(o == null || !(o instanceof Component))
            return false;
        
        Component other = (Component)o;

        ITuple otherTuple = other.qTuple;
        Set<ILiteral> otherBody = other.qBody; 

        if (qTuple.size() != otherTuple.size() || !otherTuple.equals(qTuple)){
            return false;
        }
       
        return qBody.equals(otherBody);
    }

    @Override
    public int hashCode(){
        return hashCode;
    }
}
