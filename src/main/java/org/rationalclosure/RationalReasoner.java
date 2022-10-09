/* Author: Evashna Pillay */
package org.rationalclosure;

import java.util.ArrayList;

//import org.tweetyproject.logics.pl.parser.PlParser;
import org.tweetyproject.logics.pl.syntax.Implication;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.PlBeliefSet;
import org.tweetyproject.logics.pl.syntax.PlFormula;

public class RationalReasoner {
    
    /* This TernaryEntailment object is instantiated for the checking of entailment using the ternary approach. */
    TernaryEntailment tObject = new TernaryEntailment();
    ArrayList<PlBeliefSet> rankedKB = new ArrayList<PlBeliefSet>();
    PlBeliefSet knowledgeBase = new PlBeliefSet();
    //PlParser parser = new PlParser();
    PlBeliefSet[] rankedKBArray; 

    /* This RationalReasoner object is instantiated for the concurrent/indexing approach. */
    public RationalReasoner(ArrayList<PlBeliefSet> rankedKB, PlBeliefSet formulasToCheck) {
        
        this.rankedKB = rankedKB;
        rankedKBArray = new PlBeliefSet[rankedKB.size()];
        this.rankedKBArray = rankedKB.toArray(rankedKBArray);
    }

    /* This RationalReasoner object is instantiated for the "simple" ternary approach. */
    public RationalReasoner(ArrayList<PlBeliefSet> rankedKB) {
        
        this.rankedKB = rankedKB;
        rankedKBArray = new PlBeliefSet[rankedKB.size()];
        this.rankedKBArray = rankedKB.toArray(rankedKBArray);
    }

    /* The App class will call the query() method. This method in turn checks entailment using
     the TernaryEntailment object instantiated above, specifically using the checkEntailment() method. */
    public boolean query(PlFormula formula) {
        
        PlFormula negation = new Negation(((Implication) formula).getFormulas().getFirst());
        return tObject.checkEntailment(rankedKBArray, formula, 0, rankedKB.size(), negation);
        
    }

    /* The App class will call the check() method. This method in turn instantiates the 
    IndexingEntailment object and calls the getAntecedents() method of the object. */
    public void check(PlBeliefSet formulasToCheck, PlBeliefSet antecedants){
        
        IndexingEntailment iObject = new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, 0, formulasToCheck.size());
        iObject.getAntecedants(formulasToCheck);
    }
}
