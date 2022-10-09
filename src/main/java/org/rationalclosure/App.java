/* Author: Evashna Pillay */
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
        /*Instantiate parser to convert string to PLFormula. */
        PlParser parser = new PlParser();
        
        /* The kb file is assigned to the string variable fileName. */
        String fileName = args[0];

        try {

            File file = new File(fileName);
            Scanner reader = new Scanner(file);

            /* The file is read until the end of file. */
            while (reader.hasNextLine()) {

                String stringFormula = reader.nextLine();
                
                if (stringFormula.contains("~>")) {
                    /* Reformatting of the defeasible implications of the kb if necessary, as well as 
                     the reformatting of the defasible queries from ~> to =>. */
                    stringFormula = reformatConnectives(reformatDefeasible(stringFormula));
                    /* All defeasible implications are added to the defeasible beliefset. */
                    //Parse formula from string.
                    beliefSet.add((PlFormula) parser.parseFormula(stringFormula));
                
                } else {
                    /* Reformatting of the classical implications of the kb if necessary. */
                    stringFormula = reformatConnectives(stringFormula);
                    /* All classical implications are added to the classical beliefset. */
                    //Parse formula from string.
                    classicalSet.add((PlFormula) parser.parseFormula(stringFormula));
                }

                //Parse formula from string.
                PlFormula f = (PlFormula) parser.parseFormula(stringFormula);
                /* All antecendents from the classical and defeasible beliefsets are added to 
                another beliefset for later use. */
                antecedants.add(((Implication) f).getFormulas().getFirst());
            }

            reader.close();
        
        /* Error catching to account for incorrect format of textfiles/implications. */
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
        
        /* Ranking of the kb is computed and displayed in the console of the screen. */
        System.out.println("Base Ranking of Knowledge Base:");
         /* Setting the classical implications of the kb in the BaseRankThreaded class. */
        BaseRankThreaded.setCkb(classicalSet);
        /* The actual computation/printing of the ranking takes place in the following code. 
        The ranking is stored in the arraylist for use by the rational closure approaches/testing purposes
        later on. */
        ArrayList<PlBeliefSet> rankedKnowledgeBase = BaseRankThreaded.rank(beliefSet, classicalSet);

        System.out.println("Enter the entailment checking algorithm you'd like to use (simpleT/indexT):");
        Scanner input = new Scanner(System.in);
        String type = input.nextLine();

        /* Error catching to account for incorrect input of approach to be carried out. 
        simpleT for ternary approach
        indexT for ternary/concurrent/indexing approach*/

        while ((!type.equalsIgnoreCase("simpleT")) && (!type.equalsIgnoreCase("indexT"))) {
            System.out.println("Please enter a valid entailment checking algorithm:");
            type = input.nextLine();
        }

        if (type.equalsIgnoreCase("simpleT")){
            /* RationalReasoner class instantiated with input of base ranking of kb. */
            RationalReasoner reasoner = new RationalReasoner(rankedKnowledgeBase);
            Scanner s = new Scanner(System.in);

            /* User can enter defeasible implication one at a time, the result will be output to the console.
            To end the program, user must input "quit" to the console. */
            while (true){
				
                System.out.println("Enter defeasible query: (press enter to return result or quit to end program)");
				String line = s.nextLine();
                
                if ("quit".equalsIgnoreCase(line)) {
					break;
				}

                String first = reformatDefeasible(line);
                //Parse formula from string.
                PlFormula formula = (PlFormula) parser.parseFormula(first);

                /* If the antecedent of the defeasible query is not present from the arraylist mentioned above
                the system will return "false", otherwise the query will be run by the RationalReasoner class (i.e., 
                named reasoner below).*/
                if (!antecedants.contains(((Implication) formula).getFormulas().getFirst())) {
                    
                    System.out.println("The query " + formula + " is false"); 

                } else {
                    /* The query method of the reasoner is called with the input parameter containing the formula to check. */
                    System.out.println("The query " + formula + " is " + reasoner.query(formula));             	 
                }	    
            }

            s.close();
        }

        else if (type.equalsIgnoreCase("indexT")){

            PlFormula formulaCheckEntail;
            /* Multiple defeasible queuries are stored in the beliefset formulastoCheck. */
            PlBeliefSet formulastoCheck = new PlBeliefSet();

            Scanner q = new Scanner(System.in);
            System.out.println("Enter defeasible query/s: (type \"quit\" to return result/s)");
			
            /* User can enter multiple defeasible implications at a time, the results will be output to the console.
            To return the results and subsequently end the program, the user must input "quit" to the console. */
            while (true){

				String line = q.nextLine();

				if ("quit".equalsIgnoreCase(line)) {
					break;
				}

				String first = reformatDefeasible(line);
                //Parse formula from string.
				formulaCheckEntail = (PlFormula) parser.parseFormula(first);
				formulastoCheck.add(formulaCheckEntail);  
            }
            /* RationalReasoner class instantiated with input of base ranking of kb and the beliefset containing 
            all formulaes that must be checked. */

            /* Note: The RationalReasoner class is only instantiated once all the formulas are obtained. */
            RationalReasoner reasoner = new RationalReasoner(rankedKnowledgeBase, formulastoCheck);
            /* The check method of the reasoner is called with the input parameters containing the formulas to check along
            with the arraylist of antecedants. */
            reasoner.check(formulastoCheck, antecedants);
            q.close();
        }
        
        input.close(); 
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