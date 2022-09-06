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
    
        SatSolver.setDefaultSolver(new Sat4jSolver());
        ArrayList<String> strQueryNames = new ArrayList<>();
        PlBeliefSet classical = new PlBeliefSet();
        PlBeliefSet beliefSet = new PlBeliefSet();
        PlParser parser = new PlParser();
        PlBeliefSet formulastoCheck = new PlBeliefSet();
        PlBeliefSet antecedants = new PlBeliefSet();
        

        String knowledgeBaseFile = args[0];
            
        for (int i = 1; i < args.length; i++) {
            strQueryNames.add(args[i]);
        }

        try {

            File kbfile = new File(knowledgeBaseFile);
            Scanner input = new Scanner(kbfile);
                
            while (input.hasNextLine()) {
                    
                String formulaToAdd = input.nextLine();
                    
                if (formulaToAdd.contains("~>")) {
                    
                    formulaToAdd = reformatConnectives(reformatDefeasible(formulaToAdd));
                    beliefSet.add((PlFormula) parser.parseFormula(formulaToAdd));
                }
                
                else {
                    formulaToAdd = reformatConnectives(formulaToAdd);
                    classical.add((PlFormula) parser.parseFormula(formulaToAdd));
                }
                    
                PlFormula f = (PlFormula) parser.parseFormula(formulaToAdd);
                antecedants.add(((Implication) f).getFormulas().getFirst());
            }
            
            input.close();

        } catch (Exception e) {
            System.out.println("This knowledge base file does not exist.");
        }

        BaseRankThreaded.setCkb(classical);
        ArrayList<PlBeliefSet> rankedKnowledgeBase = BaseRankThreaded.rank(beliefSet, classical);

        for (String stringQueryFile : strQueryNames) {
                
            ArrayList<PlFormula> queries = new ArrayList<PlFormula>();
                
            try {
                    
                File queryFile = new File(stringQueryFile);
                Scanner secondInput = new Scanner(queryFile);

                while (secondInput.hasNextLine()) {

                    String formulaToAdd = secondInput.nextLine();
                    queries.add((PlFormula) parser.parseFormula(reformatConnectives(reformatDefeasible(formulaToAdd))));
                    formulastoCheck.add((PlFormula) parser.parseFormula(reformatConnectives(reformatDefeasible(formulaToAdd))));
                }
            
                secondInput.close();

            } catch (Exception e) {
                System.out.println("This query file does not exist.");
            }
                
            RationalReasoner tObject = new RationalReasoner(rankedKnowledgeBase);
            RationalReasoner iObject = new RationalReasoner(rankedKnowledgeBase, formulastoCheck);
                
            long startTime;
            long endTime;
        
            try {
        
                FileWriter outputFileWriter = new FileWriter(knowledgeBaseFile + strQueryNames.get(0) + "test1" +".csv");
                    
                outputFileWriter.write("The number of ranks to check is: " + rankedKnowledgeBase.size() + "\n");
                outputFileWriter.write("The number of queries to check is: " + queries.size() + "\n");
                outputFileWriter.write("query, ternary \n");
                
                for (PlFormula query : queries) {
                        
                    outputFileWriter.write(query + ", ");  
                    startTime = System.nanoTime();
                    tObject.query(query, "simpleT");
                    endTime = System.nanoTime();
                    outputFileWriter.write(TimeUnit.MILLISECONDS.convert((endTime - startTime), TimeUnit.NANOSECONDS) + "\n");
                }
            
                outputFileWriter.close();

            } catch (IOException e) {
                e.printStackTrace();
            }

            try {
        
                FileWriter outputIndexFile = new FileWriter(knowledgeBaseFile + strQueryNames.get(0) +"test2" +".csv");
                    
                    
                outputIndexFile.write("The number of ranks to check is: " + rankedKnowledgeBase.size() + "\n");
                outputIndexFile.write("The number of queries to check is: " + formulastoCheck.size() + "\n");
                outputIndexFile.write("numberofranks, ternary_indexing \n");
            
                startTime = System.nanoTime();
                iObject.check(formulastoCheck, antecedants);
                endTime = System.nanoTime();
                outputIndexFile.write(Long.toString(TimeUnit.MILLISECONDS.convert((endTime - startTime), TimeUnit.NANOSECONDS)) + "\n");
                    
                outputIndexFile.close();

            } catch (IOException e) {
                e.printStackTrace();
            }


        }
    }

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