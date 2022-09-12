# Console-application implementing Rational Closure for defeasible entailment

## Table of contents
* [General info](#general-info)
* [Technologies](#technologies)
* [Setup](#setup)
* [Replication Testing](*replication-testing)

## General info
The goal of this project is to build on previous work to design and implement algorithms for the Rational Closure 
and to evaluate the extent to which these algorithms are scalable. Our approaches include ternary search and concurrency.

Knowledge bases and defeasible implications (queries) must be formatted according to the propositional logic syntax recommended by the TweetyProject documentation (i.e., a ~> b). (http://tweetyproject.org/)
	
## Technologies
This project is created with/has the following dependencies:
* Java version: 16.0.2
* TweetyProject library and the built-in Sat4j version: 1.20
	
## Setup
To run this project, first compile using Maven:

```
$ mvn package
```
and then run jar:

```
$ java -cp target/rationalclosure-1.0-SNAPSHOT-jar-with-dependencies.jar org.rationalclosure.App kb.txt
```
where kb.txt is the name of the knowledge base that the defeasible queries are based on. 

## Replication Testing
First compile using Maven:

```
$ mvn package
```
and then run jar:

```
$ java -cp target/rationalclosure-1.0-SNAPSHOT-jar-with-dependencies.jar org.rationalclosure.TimedReasoner kb.txt queries1.txt queries2.txt
```
where queries1.txt and queries2.txt are sets of queries used to test both ternary and concurrent approaches. Note one 
or more query sets can be input. 



