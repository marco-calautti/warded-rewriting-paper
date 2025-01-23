package org.unimi;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang3.tuple.Pair;
import org.deri.iris.api.basics.IPredicate;
import org.deri.iris.factory.Factory;
import org.unimi.Annotation.AnnotationType;


public class AnnotationsParser {
    
    public void parse(String annotations) throws InvalidAnnotationSyntaxException{

        inputAnnotationList = new ArrayList<>();
        outputAnnotationList = new ArrayList<>();

        Set<String> inputPredicates = new HashSet<>();
        Set<String> outputPredicates = new HashSet<>();
        Map<String,Integer> predicateArity = new HashMap<>();
        Map<String,Pair<String,String>> predicateCsv = new HashMap<>();

        Pattern pattern = Pattern.compile("@(\\w+)\\((.*(,.*)*)\\)");
        Matcher matcher = pattern.matcher(annotations);

        while(matcher.find()){
            String command = matcher.group(1);
            String parameters = matcher.group(2);

            String[] paramArray = parameters.split(",");
            for (int i = 0; i < paramArray.length; i++) {
                paramArray[i] = paramArray[i].replaceAll("^\"|\"$", "");
            }

            switch (command) {
                case "input":
                    if (paramArray.length != 1) {
                        throw new InvalidAnnotationSyntaxException("Expected 1 parameters for input command");
                    }
                    inputPredicates.add(paramArray[0]);
                break;
                case "output":
                    if (paramArray.length != 1) {
                        throw new InvalidAnnotationSyntaxException("Expected 1 parameters for output command");
                    }
                    outputPredicates.add(paramArray[0]);
                    break;
                case "bind":
                    if (paramArray.length != 4) {
                        throw new InvalidAnnotationSyntaxException("Expected 4 parameters for bind command");
                    }

                    predicateCsv.put(paramArray[0],Pair.of(paramArray[2],paramArray[3]));
                    break;
                case "mapping":
                    if (paramArray.length != 4) {
                        throw new InvalidAnnotationSyntaxException("Expected 4 parameters for mapping command");
                    }
                    predicateArity.put(paramArray[0],1+predicateArity.getOrDefault(paramArray[0], 0));
                break;
                default:
                    throw new InvalidAnnotationSyntaxException("Wrong command "+command);
            }
        }

        for(String edb : inputPredicates){
            Pair<String,String> csvInfo = predicateCsv.get(edb);
            String csvPath = Paths.get(csvInfo.getLeft(),csvInfo.getRight()).toString();
            int arity = predicateArity.get(edb);
            IPredicate predicate = Factory.BASIC.createPredicate(edb, arity);
            inputAnnotationList.add(new Annotation(predicate, csvPath, AnnotationType.INPUT));
        }

        for(String idb : outputPredicates){
            Pair<String,String> csvInfo = predicateCsv.get(idb);
            String csvPath = Paths.get(csvInfo.getLeft(),csvInfo.getRight()).toString();
            IPredicate predicate = Factory.BASIC.createPredicate(idb, 0);
            outputAnnotationList.add(new Annotation(predicate, csvPath, AnnotationType.OUTPUT));
        }
    }

    public List<Annotation> getInputAnnotations(){
        return inputAnnotationList;
    }

    public List<Annotation> getOutputAnnotations(){
        return outputAnnotationList;
    }
    
    private List<Annotation> inputAnnotationList;
    private List<Annotation> outputAnnotationList;
}
