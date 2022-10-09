/* Code originally written by Joel Hamilton, that has been adjusted to run for our approaches. */
package org.rationalclosure;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Scanner;
import java.util.concurrent.TimeUnit;

import org.tweetyproject.logics.pl.parser.PlParser;
import org.tweetyproject.logics.pl.syntax.PlBeliefSet;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import org.tweetyproject.logics.pl.syntax.PlFormula;
import org.tweetyproject.logics.pl.syntax.Implication;

public class TimedReasonerComparison {
    
    public static void main(String[] args) {
        
        /* Sat4j is configured as our default SAT solver. 
        This establishes whether an assignment exists that satisfies a specific Boolean formula. */
        SatSolver.setDefaultSolver(new Sat4jSolver());
        ArrayList<String> strQueryNames = new ArrayList<>();
        PlBeliefSet classical = new PlBeliefSet();
        PlBeliefSet beliefSet = new PlBeliefSet();
        
        /*Instantiate parser to convert string to PLFormula. */
        PlParser parser = new PlParser();
        PlBeliefSet formulastoCheck = new PlBeliefSet();
        PlBeliefSet antecedants = new PlBeliefSet();
        
        /* The kb file is assigned to the string variable knowledgeBaseFile. */
        String knowledgeBaseFile = args[0];
        
        /* The query file/s is/are added to the arraylist strQueryNames. */
        for (int i = 1; i < args.length; i++) {
            strQueryNames.add(args[i]);
        }

        try {

            File kbfile = new File(knowledgeBaseFile);
            Scanner input = new Scanner(kbfile);
            
            /* The kb file is read until the end of file. */
            while (input.hasNextLine()) {
                    
                String formulaToAdd = input.nextLine();
                    
                if (formulaToAdd.contains("~>")) {
                    /* Reformatting of the defeasible implications of the kb if necessary, as well as 
                     the reformatting of the defasible queries from ~> to =>. */
                    formulaToAdd = reformatConnectives(reformatDefeasible(formulaToAdd));
                    /* All defeasible implications are added to the defeasible beliefset. */
                    //Parse formula from string.
                    beliefSet.add((PlFormula) parser.parseFormula(formulaToAdd));
                }
                
                else {
                    /* Reformatting of the classical implications of the kb if necessary. */
                    formulaToAdd = reformatConnectives(formulaToAdd);
                    /* All classical implications are added to the classical beliefset. */
                    //Parse formula from string.
                    classical.add((PlFormula) parser.parseFormula(formulaToAdd));
                }
                
                //Parse formula from string
                PlFormula f = (PlFormula) parser.parseFormula(formulaToAdd);
                /* All antecendents from the classical and defeasible beliefsets are added to 
                another beliefset for later use. */
                antecedants.add(((Implication) f).getFormulas().getFirst());
            }
            
            input.close();
        /* Error catching to account for incorrect format/file not found of implications/textfile. */
        } catch (Exception e) {
            System.out.println("This knowledge base file does not exist/or is not in the correct format.");
        }

         /* Setting the classical implications of the kb in the BaseRankThreaded class. */
        BaseRankThreaded.setCkb(classical);
         /* Ranking of the kb is computed and displayed in the console of the screen. */
        ArrayList<PlBeliefSet> rankedKnowledgeBase = BaseRankThreaded.rank(beliefSet, classical);

        /* The built-in system time calls are measured by the difference of the endTime and startTime. */
        long startTime;
        long endTime;

        /* All the queries are the textfile/s are added to the arraylists queries and the beliefset formulastoCheck. */
        for (String stringQueryFile : strQueryNames) {
                
            ArrayList<PlFormula> queries = new ArrayList<PlFormula>();
                
            try {
                    
                File queryFile = new File(stringQueryFile);
                Scanner secondInput = new Scanner(queryFile);

                /* All the defeasible implications from a single query file of the set is added to the queries (arraylist)
                for the ternary approach, as well as the formulastoCheck (beliefset) for the concurrent indexing approach.
                NOTE: The arraylist is instantiated for every iteration of the for loop above, whereas the
                formalstoCheck was instantiated at the beginning of the class, this is to ensure that all queries
                from all sets are computed at once for the concurrent/indexing approach. */
                while (secondInput.hasNextLine()) {

                    String formulaToAdd = secondInput.nextLine();
                    //Parse formula from string
                    queries.add((PlFormula) parser.parseFormula(reformatConnectives(reformatDefeasible(formulaToAdd))));
                    formulastoCheck.add((PlFormula) parser.parseFormula(reformatConnectives(reformatDefeasible(formulaToAdd))));
                }
            
                secondInput.close();
            
            /* Error catching to account for incorrect format/file not found of implications/textfile. */
            } catch (Exception e) {
                System.out.println("This query file does not exist.");
            }
            
            /* RationalReasoner class instantiated for ternary approach with input of base ranking of kb. */
            RationalReasoner tObject = new RationalReasoner(rankedKnowledgeBase);
        
            try {
        
                FileWriter outputFileWriter = new FileWriter(strQueryNames.get(0) + "_queriesResultsSimple" +".csv");
                    
                outputFileWriter.write("The number of ranks to check is: " + rankedKnowledgeBase.size() + "\n");
                outputFileWriter.write("The number of queries to check is: " + queries.size() + "\n");
                outputFileWriter.write("query, ternary \n");
                
                for (PlFormula query : queries) {
                        
                    outputFileWriter.write(query + ", ");  
                    /* Java built-in system time calls instantiated. */
                    startTime = System.nanoTime();
                     /* The query method of the tObject is called with the input parameter containing the formula to check. */
                    tObject.query(query);
                    /* Java built-in system time calls instantiated. */
                    endTime = System.nanoTime();
                    outputFileWriter.write(TimeUnit.MILLISECONDS.convert((endTime - startTime), TimeUnit.NANOSECONDS) + "\n");
                }
            
                outputFileWriter.close();

            } catch (IOException e) {
                e.printStackTrace();
            }


        }

        /* Note: The RationalReasoner iObject is only instantiated once all the formulas are obtained. */
        RationalReasoner iObject = new RationalReasoner(rankedKnowledgeBase, formulastoCheck);
        
        try {
        
            FileWriter outputIndexFile = new FileWriter(knowledgeBaseFile +"_queriesResultsIndex" +".csv");
                
                
            outputIndexFile.write("The number of ranks to check is: " + rankedKnowledgeBase.size() + "\n");
            outputIndexFile.write("The number of queries to check is: " + formulastoCheck.size() + "\n");
            outputIndexFile.write("numberofranks, ternary_indexing \n");
            
            /* Java built-in system time calls instantiated. */
            startTime = System.nanoTime();
            /* The check method of the iObject is called with the input parameters containing the formulas to check along
            with the arraylist of antecedants. */
            iObject.check(formulastoCheck, antecedants);
            /* Java built-in system time calls instantiated. */
            endTime = System.nanoTime();
            outputIndexFile.write(Long.toString(TimeUnit.MILLISECONDS.convert((endTime - startTime), TimeUnit.NANOSECONDS)) + "\n");
                
            outputIndexFile.close();

        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /* The methods below allows the application to make any reformatting necessary possible, and takes into consideration
     the logic that may be useed by the end user, however this may not account for all possibilities. In that case,
     the user will be asked to reformat their defeasible implications. */

    public static String reformatDefeasible(String formula) {
        int index = formula.indexOf("~>");
        formula = "(" + formula.substring(0, index) + ") => (" + formula.substring(index + 2, formula.length()) + ")";
        return formula;
    }

    public static String reformatConnectives(String formula) {
        formula = formula.replaceAll("¬", "!");
        formula = formula.replaceAll("~", "!");
        formula = formula.replaceAll("&", "&&");
        formula = formula.replaceAll("<->", "<=>");
        formula = formula.replaceAll("->", "=>");
        return formula;
    }
}