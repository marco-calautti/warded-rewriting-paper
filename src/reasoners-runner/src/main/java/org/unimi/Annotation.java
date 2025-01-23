package org.unimi;

import org.deri.iris.api.basics.IPredicate;

public class Annotation {

    public static enum AnnotationType{
        INPUT,
        OUTPUT
    }

    public Annotation(IPredicate pred, String csvPath, AnnotationType type){
        this.predicate = pred;
        this.csvPath = csvPath;
        this.type = type;
    }

    public IPredicate getPredicate() {
        return predicate;
    }
    public String getCsvPath() {
        return csvPath;
    }

    public AnnotationType getType() {
        return type;
    }

    @Override
    public boolean equals(Object other){
        if(other == null || !(other instanceof Annotation))
            return false;
        
        if(this == other)
            return true;

        Annotation otherAn = (Annotation)other;
        return this.predicate.getPredicateSymbol().equals(otherAn.getPredicate().getPredicateSymbol());
    }
    
    private IPredicate predicate;
    private String csvPath;
    private AnnotationType type;
}
