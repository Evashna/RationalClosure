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

public class IndexingEntailment extends RecursiveTask<HashMap<PlFormula, Integer>>{
    
    private static final int SEQUENTIAL_THRESHOLD = 10;
    static int rankRemove = -1;
    HashMap<PlFormula, Integer> negRank = new HashMap<PlFormula, Integer>();
    private PlBeliefSet formulasToCheck;
    private PlBeliefSet antecedants;
    private PlBeliefSet[] rankedKBArray;
    private int high;
    private int low;
    private List<PlFormula> form;

    public IndexingEntailment(PlBeliefSet[] ranks, PlBeliefSet formulasToCheck, PlBeliefSet antecedants, int low, int high) {
        this.formulasToCheck = formulasToCheck;
        this.rankedKBArray = ranks;
        this.antecedants = antecedants;
        this.high = high;
        this.low = low;
        this.form = formulasToCheck.getCanonicalOrdering();
    }
    
    @Override
    protected HashMap<PlFormula, Integer> compute(){

       if (high - low <= SEQUENTIAL_THRESHOLD) { 
        
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
        else {

            int mid = (high + low) / 2;

            IndexingEntailment left  = new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, low, mid);
            IndexingEntailment right = new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, mid, high);

            left.fork();
            HashMap<PlFormula, Integer> result = right.compute();
            result.putAll(left.join());
            return result;
        }
    }

    public boolean checkEntailment(PlFormula formula, int left, int right, PlFormula negation) {   
        SatSolver.setDefaultSolver(new Sat4jSolver());
        SatReasoner classicalReasoner = new SatReasoner();

        if (negRank.get(negation) != null) {
            rankRemove = negRank.get(negation);
            System.out.println("We know to remove rank " + Integer.toString(rankRemove) 
            + " and all ranks above it. (antecedent:" + ((Implication) formula).getFormulas().getFirst() + ")");

        } else {
            
            if (right > left) {

                int mid = left + (right - left) / 3;
                int mid2 = right - (right - left) / 3;
                
                if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid + 1, rankedKBArray.length)),
                    negation)) {
                        
                if (mid2 < rankedKBArray.length) {
                   
                    if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid2 + 1, rankedKBArray.length)),
                            negation)) {                          
                                
                        return checkEntailment(formula, mid2 + 1, right, negation);

                    } else {

                        if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid2, rankedKBArray.length)),negation)) {

                            System.out.println("Removing ranks: 0 to " + Integer.toString(mid2));
                            negRank.put(negation, mid2);
                            rankRemove = mid2;

                        } else {
                            return checkEntailment(formula, mid + 1, mid2 - 1, negation);
                        }
                    }
                } else if (mid2 == rankedKBArray.length) {
                    return checkEntailment(formula, mid + 1, mid2 - 1, negation);

                }

                } else {
                
                    if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, mid, rankedKBArray.length)),negation)) {

                        System.out.println("Removing ranks: 0 to " + Integer.toString(mid) +" for (antecedent:" + ((Implication) formula).getFormulas().getFirst() + ")");
                        negRank.put(negation, mid);
                        rankRemove = mid;

                    } else {
                        return checkEntailment(formula, left, mid, negation);
                    }

                }
            }
        }

        if (rankRemove + 1 < rankedKBArray.length) {
            if (classicalReasoner.query(combine(Arrays.copyOfRange(rankedKBArray, rankRemove + 1, rankedKBArray.length)), formula)) {
                return true;
            
            } else {
                    return false;
            }
        } else {
            return true;
        }   
    }

    public void getRankAntecedants() {
        ForkJoinPool.commonPool().invoke(new IndexingEntailment(rankedKBArray, formulasToCheck, antecedants, 0, formulasToCheck.size()));
    }
    
    public void getAntecedants(PlBeliefSet formulasToCheck){
        
        for (PlFormula f : formulasToCheck) {
            PlFormula n = new Negation(((Implication) f).getFormulas().getFirst());
            if (!negRank.containsKey(n)){
                negRank.put(n, null);
            } 
        }

        getRankAntecedants();
    }
    
    public static PlBeliefSet combine(PlBeliefSet[] ranks) {
        PlBeliefSet combined = new PlBeliefSet();
        
        for (PlBeliefSet rank : ranks) {
            combined.addAll(rank);
        }
        
        return combined;
    }
}
