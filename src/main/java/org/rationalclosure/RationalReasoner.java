package org.rationalclosure;

import java.util.ArrayList;

import org.tweetyproject.logics.pl.parser.PlParser;
import org.tweetyproject.logics.pl.syntax.Implication;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.PlBeliefSet;
import org.tweetyproject.logics.pl.syntax.PlFormula;

public class RationalReasoner {
    
    TernaryEntailment tObject = new TernaryEntailment();
    ArrayList<PlBeliefSet> rankedKB = new ArrayList<PlBeliefSet>();
    PlBeliefSet knowledgeBase = new PlBeliefSet();
    PlParser parser = new PlParser();
    PlBeliefSet[] rankedKBArray; 

    public RationalReasoner(ArrayList<PlBeliefSet> rankedKB, PlBeliefSet formulasToCheck) {
        
        this.rankedKB = rankedKB;
        rankedKBArray = new PlBeliefSet[rankedKB.size()];
        this.rankedKBArray = rankedKB.toArray(rankedKBArray);
    }

    public RationalReasoner(ArrayList<PlBeliefSet> rankedKB) {
        
        this.rankedKB = rankedKB;
        rankedKBArray = new PlBeliefSet[rankedKB.size()];
        this.rankedKBArray = rankedKB.toArray(rankedKBArray);
    }

    public boolean query(PlFormula formula, String alg) {
        
        PlFormula negation = new Negation(((Implication) formula).getFormulas().getFirst());
        return tObject.checkEntailment(rankedKBArray, formula, 0, rankedKB.size(), negation);
        
    }

    public void check (PlBeliefSet formulasToCheck, PlBeliefSet antecedants){
        
        IndexingEntailment iObject = new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, 0, formulasToCheck.size());
        iObject.getAntecedants(formulasToCheck);
    }
}
