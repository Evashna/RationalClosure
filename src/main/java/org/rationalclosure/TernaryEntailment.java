/* Author: Evashna Pillay */
package org.rationalclosure;

import java.util.Arrays;
import org.tweetyproject.logics.pl.syntax.*;
import org.tweetyproject.logics.pl.syntax.PlBeliefSet;
import org.tweetyproject.logics.pl.reasoner.SatReasoner;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;

public class TernaryEntailment {

    private static int rankRemove = -1;
    /* NOTE: that a formula is consistent with a knowledge base K when its negation is not entailed by K. */

    /* The first computation of the algorithm sets a min value of 0 (left) and a max value equal to the number of ranks n (right). 
       This is the initial search range. */
    public boolean checkEntailment(PlBeliefSet[] rankedKB, PlFormula formula, int left, int right, PlFormula negation) {
        
        /* Sat4j is configured as our default SAT solver. 
        This establishes whether an assignment exists that satisfies a specific Boolean formula. */
        SatSolver.setDefaultSolver(new Sat4jSolver());

        /* The default SAT reasoner is instantiated to perform reasoning in propositional logic.
        - queries the given belief base for the given formula. */
        SatReasoner reasoner = new SatReasoner();
        int rlength = rankedKB.length;

        /* in the first computation, we determine if the number of ranks is greater than 0 then only 
         will we continue, otherwise we return true as there are no statements/nor ranks to contradict
         the defeasible query */
        if (right > left) {
            
            /* The two midpoints are then determined given the left and right values, we refer to these 
            midpoints as mid and mid2. */
            int mid = left + (right - left) / 3;
            int mid2 = right - (right - left) / 3;
            
            /* Check if removing rank mid and all those above it results in the antecedent 
            being consistent with the knowledge base; if the negation is consistent with kb at mid + 1
            then then we search lower down (i.e., ranks with higher numbers.. from mid2 + 1) else check if the negation 
            of the antecedent is consistent with the kb at mid, if so then remove mid */
            if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid + 1, rankedKB.length)),negation)) {
                  
                /* This accounts for the use of (mid2 + 1), if mid2 > rankedKB.length the system would throw an error, so
                 to avoid this we ensure the value is smaller than rankedKB.length otherwise we check if they are equal. */
                if (mid2 < rankedKB.length) {

                     /* Check if removing rank mid2 and all those above it results in the antecedent 
                    being consistent with the knowledge base; if the negation is consistent with kb at mid2 + 1
                    then then we search lower down (i.e., ranks with higher numbers) else check if the negation 
                    of the antecedent is consistent with the kb at mid2, if so then remove mid2 */
                    if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid2 + 1, rankedKB.length)),negation)) { 
                        
                        return checkEntailment(rankedKB, formula, mid2 + 1, right, negation);

                    } else {
                        /* check if the negation of the antecedent is consistent with the kb at mid2, if so then remove mid2 */
                        if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid2, rankedKB.length)),negation)) {
                            System.out.println("Removing ranks: 0 to " + Integer.toString(mid2));
                            rankRemove = mid2;
                        /* else check if the negation of the antecedent is consistent with the kb lower in the search range
                        (i.e., that is ranks with higher numbers) */
                        } else {
                            return checkEntailment(rankedKB, formula, mid + 1, mid2 - 1, negation);
                        }
                    }
                
                /* if mid2 == rankedKB.length, it is not possible to check for mid2 + 1, therefore we change the search range
                to (mid + 1) - (mid2 - 1). This range is also necessary as we have not checked it in the other if statements,
                we have only checked from 0 to mid and mid2 to rankedKB.length. */
                } else if (mid2 == rankedKB.length) {
                    return checkEntailment(rankedKB, formula, mid + 1, mid2 - 1, negation);
                }

            } else {
                /* check if the negation of the antecedent is consistent with the kb at mid, if so then remove mid */
                if (reasoner.query(combine(Arrays.copyOfRange(rankedKB, mid, rankedKB.length)),negation)) {     
                    
                    System.out.println("Removing ranks: 0 to " + Integer.toString(mid));
                    rankRemove = mid;
                /* else check if the negation of the antecedent is consistent with the kb higher up in the search range
                (i.e., that is ranks with lower numbers) */
                } else {
                    return checkEntailment(rankedKB, formula, left, mid, negation);
                }
            }

        }

        else {
            /* if right == left, there are no mid values to check. */
            if (right == left) {
                rankRemove = right;
            }
            /* In some instances the first rank (0) or last rank will be set to rankRemove when right == left
            however this may contain the antecedent, which means there is no rank to remove, thus 
            we check if the negation is not consistent with the kb at rankRemove. If so, we subtract 1 from
            rankRemove. */
            if (!reasoner.query(combine(Arrays.copyOfRange(rankedKB, rankRemove, rankedKB.length)),negation)){
                rankRemove -= 1;
            }

        }
        
        /* Once we have determined the rank to remove or the above if statements finish executing, we query the formula
         with the kb from the rank after the rank which was removed. If we do not have a value for rankReove we
         return false, else the reasoner queries the formula to determine whether it is true or false. */
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
    /* In order to query the reasoner we need to convert the array data structure 
    containing ranks of statements to a single PlBeliefSet data structure 
    as the reasoner requires this format. */
    public static PlBeliefSet combine(PlBeliefSet[] ranks) {
        
        PlBeliefSet combined = new PlBeliefSet();
        
        for (PlBeliefSet rank : ranks) {
            combined.addAll(rank);
        }

        return combined;
    }

}
