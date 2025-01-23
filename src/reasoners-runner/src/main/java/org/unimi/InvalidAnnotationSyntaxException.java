package org.unimi;

public class InvalidAnnotationSyntaxException extends Exception{

    public InvalidAnnotationSyntaxException(){
        super();
    }

    public InvalidAnnotationSyntaxException(String message){
        super(message);
    }
}
