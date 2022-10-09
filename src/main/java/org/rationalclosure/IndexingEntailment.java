/* Author: Evashna Pillay */
package org.rationalclosure;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;

import org.tweetyproject.logics.pl.reasoner.SatReasoner;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.syntax.Implication;
import org.tweetyproject.logics.pl.syntax.Negation;
import org.tweetyproject.logics.pl.syntax.PlBeliefSet;
import org.tweetyproject.logics.pl.syntax.PlFormula;


/* RecursiveTask is an abstract class and it extends ForkJoinTask. */
public class IndexingEntailment extends RecursiveTask<HashMap<PlFormula, Integer>>{

     /* NOTE: the sequential threshold is set to 10. During the initial stages of testing 
     thresholds ranging from 5, 10 and 20 were tested, this threshold was chosen due to its 
     performance being faster. However, future researchers can test on computers with more 
     than two cores to determine a more optimum threshold. */
    private static final int SEQUENTIAL_THRESHOLD = 10;

    static int rankRemove = -1;
    HashMap<PlFormula, Integer> negRank = new HashMap<PlFormula, Integer>();
    private PlBeliefSet formulasToCheck;
    private PlBeliefSet antecedants;
    private PlBeliefSet[] rankedKBArray;
    private int high;
    private int low;
    private List<PlFormula> form;

     /* IndexingEntailment object instantiated. */
    public IndexingEntailment(PlBeliefSet[] ranks, PlBeliefSet formulasToCheck, PlBeliefSet antecedants, int low, int high) {
        this.formulasToCheck = formulasToCheck;
        this.rankedKBArray = ranks;
        this.antecedants = antecedants;
        this.high = high;
        this.low = low;
        this.form = formulasToCheck.getCanonicalOrdering();
    }

    /* class IndexingEntailment is overriding compute() method of RecursiveTask */
    @Override
    protected HashMap<PlFormula, Integer> compute(){

        /* If the difference is smaller (e.g., for the first computation: the total number of queries - 0) than 
        the threshold, we compute the algorithm in a sequential manner. */
       if (high - low <= SEQUENTIAL_THRESHOLD) { 

            /* Sat4j is configured as our default SAT solver. 
            This establishes whether an assignment exists that satisfies a specific Boolean formula. */
            SatSolver.setDefaultSolver(new Sat4jSolver());

            for (int i = low; i < high; i++){
                PlFormula f = form.get(i);
                if (!antecedants.contains(((Implication) f).getFormulas().getFirst())) {
                    System.out.println("The query " + f + " is false"); 
                } 
                
                else {
                    PlFormula n = new Negation(((Implication) f).getFormulas().getFirst());
                    System.out.println("The query " + f + " is " + checkEntailment(f, 0, rankedKBArray.length - 1, n));
                }
            }

            return negRank;
        }

         /* Otherwise: we divide the number of threads by two. */
        else {

            int mid = (high + low) / 2;

            IndexingEntailment left  = new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, low, mid);
            IndexingEntailment right = new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, mid, high);

            /* each half is resubmitted as a "child" task by making a fork() call, the current task will wait for 
            results from its two halves by calling join().
            fork() -  starts parallel computation  
            to return the result, call the join() on the fork()
            join() will get the result from compute() */

            left.fork();
            HashMap<PlFormula, Integer> result = right.compute();
            result.putAll(left.join());
            return result;
        }
    }

    /* NOTE: that a formula is consistent with a knowledge base K when its negation is not entailed by K. */

    /* The first computation of the algorithm sets a min value of 0 (left) and a max value equal to the number of ranks n (right). 
       This is the initial search range. */

    public boolean checkEntailment(PlFormula formula, int left, int right, PlFormula negation) {  
    
        int rlength = rankedKBArray.length;
        /* Sat4j is configured as our default SAT solver. 
        This establishes whether an assignment exists that satisfies a specific Boolean formula. */ 
        SatSolver.setDefaultSolver(new Sat4jSolver());

        /* The default SAT reasoner is instantiated to perform reasoning in propositional logic.
        - queries the given belief base for the given formula. */
        SatReasoner classicalReasoner = new SatReasoner();

         /* If the rank at which the negation is consistent with a knowledge base K has already been computed
         then we return the rank and determine wehther the query is true or false. Otherwise we search the ranks below. */
        if (negRank.get(negation) != null) {
            rankRemove = negRank.get(negation);
            System.out.println("We know to remove rank " + Integer.toString(rankRemove) 
            + " and all ranks above it. (antecedent:" + ((Implication) formula).getFormulas().getFirst() + ")");

        } else {
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
                if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid + 1, rankedKBArray.length)),
                    negation)) {
                     
                /* This accounts for the use of (mid2 + 1), if mid2 > rankedKB.length the system would throw an error, so
                 to avoid this we ensure the value is smaller than rankedKB.length otherwise we check if they are equal. */
                if (mid2 < rankedKBArray.length) {
                   
                     /* Check if removing rank mid2 and all those above it results in the antecedent 
                    being consistent with the knowledge base; if the negation is consistent with kb at mid2 + 1
                    then then we search lower down (i.e., ranks with higher numbers) else check if the negation 
                    of the antecedent is consistent with the kb at mid2, if so then remove mid2 */
                    if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid2 + 1, rankedKBArray.length)),
                            negation)) {                          
                        
                        return checkEntailment(formula, mid2 + 1, right, negation);

                    } else {
                         /* check if the negation of the antecedent is consistent with the kb at mid2, if so then remove mid2 */
                        if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid2, rankedKBArray.length)),negation)) {

                            System.out.println("Removing ranks: 0 to " + Integer.toString(mid2) + " for (antecedent:" + ((Implication) formula).getFormulas().getFirst() + ")");
                            negRank.put(negation, mid2);
                            rankRemove = mid2;
                        
                        /* else check if the negation of the antecedent is consistent with the kb lower in the search range
                        (i.e., that is ranks with higher numbers) */
                        } else {
                            return checkEntailment(formula, mid + 1, mid2 - 1, negation);
                        }
                    }
                /* if mid2 == rankedKB.length, it is not possible to check for mid2 + 1, therefore we change the search range
                to (mid + 1) - (mid2 - 1). This range is also necessary as we have not checked it in the other if statements,
                we have only checked from 0 to mid and mid2 to rankedKB.length. */
                } else if (mid2 == rankedKBArray.length) {
                    return checkEntailment(formula, mid + 1, mid2 - 1, negation);

                }

                } else {
                    /* check if the negation of the antecedent is consistent with the kb at mid, if so then remove mid */
                    if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid, rankedKBArray.length)),negation)) {

                        System.out.println("Removing ranks: 0 to " + Integer.toString(mid) +" for (antecedent:" + ((Implication) formula).getFormulas().getFirst() + ")");
                        negRank.put(negation, mid);
                        rankRemove = mid;
                    
                    /* else check if the negation of the antecedent is consistent with the kb higher up in the search range
                    (i.e., that is ranks with lower numbers) */
                    } else {
                        return checkEntailment(formula, left, mid, negation);
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
                if (!classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, rankRemove, rankedKBArray.length)),negation)){
                    rankRemove -= 1;
                }

            }
        }

        /* Once we have determined the rank to remove or the above if statements finish executing, we query the formula
         with the kb from the rank after the rank which was removed. If we do not have a value for rankReove we
         return false, else the reasoner queries the formula to determine whether it is true or false. */
         if (rankRemove + 1 < rlength) {
            if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, rankRemove + 1, rlength)), formula)) {
                return true;
            
            } else {
                    return false;
            }
        } else {
            return true;
        }   
    }
    
    /* ForkJoinPool is a specialized implementation of ExecutorService implementing the work-stealing algorithm
    (i.e., idle worker threads steal the work/tasks from those worker threads that are busy).*/
    public void getRankAntecedants() {
        ForkJoinPool.commonPool().invoke(new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, 0, formulasToCheck.size()));
    }
    
    /* Before we distrubute tasks to threads, we determine whether or not the negation and the rank at which it is 
    consistent with the kb is in the hashmap, if the negation is not present we place the negation, as well as
    null in the place of rank.*/
    public void getAntecedants(PlBeliefSet formulasToCheck){
        
        for (PlFormula f : formulasToCheck) {
            PlFormula n = new Negation(((Implication) f).getFormulas().getFirst());
            if (!negRank.containsKey(n)){
                negRank.put(n, null);
            } 
        }
        /* We then call the method containing the ForkJoinPool to invoke it */
        getRankAntecedants();
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
