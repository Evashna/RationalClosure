package org.rationalclosure;

import java.util.Arrays;
import org.tweetyproject.logics.pl.syntax.*;
import org.tweetyproject.logics.pl.syntax.PlBeliefSet;
import org.tweetyproject.logics.pl.reasoner.SatReasoner;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;

public class TernaryEntailment {

    private static int rankRemove = -1;

    public boolean checkEntailment(PlBeliefSet[] rankedKB, PlFormula formula, int left, int right, PlFormula negation) {
        
        SatSolver.setDefaultSolver(new Sat4jSolver());
        SatReasoner reasoner = new SatReasoner();
        int rlength = rankedKB.length;

        if (right > left) {
            
            int mid = left + (right - left) / 3;
            int mid2 = right - (right - left) / 3;
            
            if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid + 1, rankedKB.length)),negation)) {
                        
                if (mid2 < rankedKB.length) {

                    if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid2 + 1, rankedKB.length)),negation)) { 
                        
                        return checkEntailment(rankedKB, formula, mid2 + 1, right, negation);

                    } else {
                        
                        if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid2, rankedKB.length)),negation)) {
                            System.out.println("Removing ranks: 0 to " + Integer.toString(mid2));
                            rankRemove = mid2;

                        } else {
                            return checkEntailment(rankedKB, formula, mid + 1, mid2 - 1, negation);
                        }
                    }

                } else if (mid2 == rankedKB.length) {
                    return checkEntailment(rankedKB, formula, mid + 1, mid2 - 1, negation);
                }

            } else {

                if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid, rankedKB.length)),negation)) {     
                    
                    System.out.println("Removing ranks: 0 to " + Integer.toString(mid));
                    rankRemove = mid;

                } else {
                    return checkEntailment(rankedKB, formula, left, mid, negation);
                }
            }

        }

        if (rankRemove + 1 < rlength) {
            
            if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, rankRemove + 1, rlength)), formula)) {
                return true;
            } 
            else {
                return false;
            }
        } 
        else {
            return true;
        }
    }

    public static PlBeliefSet combine(PlBeliefSet[] ranks) {
        
        PlBeliefSet combined = new PlBeliefSet();
        
        for (PlBeliefSet rank : ranks) {
            combined.addAll(rank);
        }

        return combined;
    }

}
