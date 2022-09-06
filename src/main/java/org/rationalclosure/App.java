package org.rationalclosure;

import java.io.*;
import java.util.Scanner;
import java.util.ArrayList;
import org.tweetyproject.logics.pl.syntax.*;
import org.tweetyproject.logics.pl.parser.PlParser;
import org.tweetyproject.commons.ParserException;

public class App {

    public static void main(String[] args) throws IOException, ParserException {
        
        PlBeliefSet beliefSet = new PlBeliefSet();
        PlBeliefSet classicalSet = new PlBeliefSet();
        PlBeliefSet antecedants = new PlBeliefSet();
        PlParser parser = new PlParser();
        
        String fileName = args[0];

        try {

            File file = new File(fileName);
            Scanner reader = new Scanner(file);

            while (reader.hasNextLine()) {

                String stringFormula = reader.nextLine();
                
                if (stringFormula.contains("~>")) {

                    stringFormula = reformatConnectives(reformatDefeasible(stringFormula));
                    beliefSet.add((PlFormula) parser.parseFormula(stringFormula));
                
                } else {

                    stringFormula = reformatConnectives(stringFormula);
                    classicalSet.add((PlFormula) parser.parseFormula(stringFormula));
                }

                PlFormula f = (PlFormula) parser.parseFormula(stringFormula);
                antecedants.add(((Implication) f).getFormulas().getFirst());
            }

            reader.close();

        } catch (FileNotFoundException e) {
            
            System.out.println("Incorrect format in textfile.");
			
			System.out.println("Each formula must be on a separate line.\n" 
							+ "Formulas must be in the following syntax format:");
            
			System.out.println("Implication symbol: =>\n" 
							 + "Defeasible Implication symbol: ~>\n" 
							 + "Conjunction symbol: && \n"
							 + "Disjunction symbol: ||\n"
							 + "Equivalence symbol: <=>\n"
							 + "Negation symbol: !");
        }

        System.out.println("Base Ranking of Knowledge Base:");
        BaseRankThreaded.setCkb(classicalSet);
        ArrayList<PlBeliefSet> rankedKnowledgeBase = BaseRankThreaded.rank(beliefSet, classicalSet);

        System.out.println("Enter the entailment checking algorithm you'd like to use (simpleT/indexT):");
        Scanner input = new Scanner(System.in);
        String type = input.nextLine();

        while ((!type.equalsIgnoreCase("simpleT")) && (!type.equalsIgnoreCase("indexT"))) {
            System.out.println("Please enter a valid entailment checking algorithm:");
            type = input.nextLine();
        }

        if (type.equalsIgnoreCase("simpleT")){

            RationalReasoner reasoner = new RationalReasoner(rankedKnowledgeBase);
            Scanner s = new Scanner(System.in);

            while (true){
				
                System.out.println("Enter defeasible query: (press enter to return result or quit to end program)");
				String line = s.nextLine();
                
                if ("quit".equalsIgnoreCase(line)) {
					break;
				}

                String first = reformatDefeasible(line);
                PlFormula formula = (PlFormula) parser.parseFormula(first);

                if (!antecedants.contains(((Implication) formula).getFormulas().getFirst())) {
                    
                    System.out.println("The query " + formula + " is false"); 

                } else {
                    System.out.println("The query " + formula + " is " + reasoner.query(formula, type));             	 
                }	    
            }

            s.close();
        }

        else if (type.equalsIgnoreCase("indexT")){

            PlFormula formulaCheckEntail;
            PlBeliefSet formulastoCheck = new PlBeliefSet();
            Scanner q = new Scanner(System.in);
            System.out.println("Enter defeasible query/s: (type \"quit\" to return result/s)");
			
            while (true){

				String line = q.nextLine();

				if ("quit".equalsIgnoreCase(line)) {
					break;
				}

				String first = reformatDefeasible(line);
				formulaCheckEntail = (PlFormula) parser.parseFormula(first);
				formulastoCheck.add(formulaCheckEntail);  
            }

            RationalReasoner reasoner = new RationalReasoner(rankedKnowledgeBase, formulastoCheck);
            reasoner.check(formulastoCheck, antecedants);
            q.close();
        }
        
        input.close(); 
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