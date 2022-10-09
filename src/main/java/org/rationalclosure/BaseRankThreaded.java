/* Code originally written by Daniel Park, that has been adjusted to run for our approaches. */

package org.rationalclosure;

import java.util.*;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.RecursiveTask;
import org.tweetyproject.logics.pl.syntax.*;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.reasoner.SatReasoner;

/* RecursiveTask is an abstract class and it extends ForkJoinTask. */
public class BaseRankThreaded extends RecursiveTask<PlBeliefSet> {

    private PlBeliefSet kb;
    private PlBeliefSet antecedants;
    /* The default SAT reasoner - query() method queries the given belief base for the given formula. */
    private SatReasoner reasoner;
    private int start;
    private int end;
    private int threshold;
    private static ArrayList<PlBeliefSet> rankedKB = new ArrayList<PlBeliefSet>();
    private static PlBeliefSet cStatements;

    /* BaseRankThreaded object instantiated. */
    public BaseRankThreaded(int start, int end, int threshold, PlBeliefSet antecedants, PlBeliefSet kb) {

        /* Sat4j is configured as our default SAT solver. 
        This establishes whether an assignment exists that satisfies a specific Boolean formula. */
        SatSolver.setDefaultSolver(new Sat4jSolver());
        
        /* The default SAT reasoner is instantiated to perform reasoning in propositional logic.
        queries the given belief base for the given formula. */
        reasoner = new SatReasoner();
        this.antecedants = antecedants;
        this.kb = kb;
        this.start = start;
        this.end = end;
        this.threshold = threshold;
    }

     /* class BaseRankThreaded is overriding compute() method of RecursiveTask */
    @Override
    protected PlBeliefSet compute() {
        
        /* If the difference is smaller (e.g., for the first computation: the total number of ranks - 0) than 
        the threshold, we compute the algorithm in a sequential manner. */
        if ((end - start) <= threshold) {
            
            PlBeliefSet exceptionals = new PlBeliefSet();
            List<PlFormula> list = antecedants.getCanonicalOrdering();
            
            for (int i = start; i < end; i++) {
                
                PlFormula antecedant = list.get(i);
                
                if (reasoner.query(kb, new Negation(antecedant))) {
                    exceptionals.add(list.get(i));
                }
            }

            return exceptionals;
        }

        int mid = start + (end - start) / 2;
        BaseRankThreaded lower = new BaseRankThreaded(start, mid, threshold, antecedants, kb);
        BaseRankThreaded upper = new BaseRankThreaded(mid, end, threshold, antecedants, kb);
        lower.fork();
        upper.fork();
        PlBeliefSet result = new PlBeliefSet();
        result.addAll(lower.join());
        result.addAll(upper.join());
        return new PlBeliefSet(result);
    }

    private static PlBeliefSet getExceptionals(PlBeliefSet antecedants, PlBeliefSet kb, int threshold) {
        BaseRankThreaded brt = new BaseRankThreaded(0, antecedants.size(), threshold, antecedants, kb);
        ForkJoinPool pool = new ForkJoinPool();
        PlBeliefSet result = pool.invoke(brt);
        return result;
    }
    /* Adjustments: Use of recursion for code completeness/maintainability. */
    public static ArrayList<PlBeliefSet> rank(PlBeliefSet curMaterial, PlBeliefSet prevMaterial) {
       
        prevMaterial = curMaterial;
        curMaterial = new PlBeliefSet();

        PlBeliefSet rank = new PlBeliefSet();       

        PlBeliefSet temp = new PlBeliefSet(prevMaterial);
        temp.addAll(cStatements);
        PlBeliefSet antecedants = new PlBeliefSet();

        for (PlFormula f : prevMaterial) {
            antecedants.add(((Implication) f).getFormulas().getFirst());
        }  

        /* Threshold determined by Math.max(antecedants.size() / 6, 1) */
        PlBeliefSet exceptionals = getExceptionals(antecedants, temp, Math.max(antecedants.size() / 6, 1));
        for (PlFormula f : prevMaterial) {
            PlFormula ante = ((Implication) f).getFormulas().getFirst();
                if (exceptionals.contains(ante))
                    curMaterial.add(f);

                if (!cStatements.contains(f) && !curMaterial.contains(f)){
                    rank.add(f);
                }
        }

        if (rank.size() != 0) {
            rankedKB.add(rank);
            int rSize = rankedKB.size() - 1;
            System.out.println("Rank " + Integer.toString(rSize) + ":" + rankedKB.get(rSize).toString());

        } else {
        // some statements that appear defeasible are in fact classical, and appear on the bottom rank. 
        //This is due to the fact that R ⊩ ¬α |∼ ⊥ if and only if R ⊩ α.
            cStatements.addAll(curMaterial);
        }

        if (!curMaterial.equals(prevMaterial)){
            /* recursive call */
            return rank(curMaterial, prevMaterial);
        } 

        rankedKB.add(cStatements);
        System.out.println("Infinite Rank:" + cStatements.toString());
    
        return rankedKB;

        
    }
    /* (Setter) method to set classical beliefset, used in App class. */
    public static void setCkb(PlBeliefSet ckb){
        cStatements = ckb;
    }

}
