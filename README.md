# Automated Theorem Prover (3806ICT)

This project implements a sequent calculus-based automated theorem prover based on Algorithm 2 from Hou (2021).

## Overview
The system performs backward proof search on first-order logic formulas using sequent calculus rules.

## Features
- Baseline backward proof search (Algorithm 2)
- Loop detection to avoid repeated states
- Memoisation (caching) to improve efficiency
- Iterative deepening search to control recursion depth

## Files
- main.py → runs test cases and outputs results
- prover.py → implements proof search algorithm
- parser.py → parses logical formulas into internal representation

## Example Formulas Tested
- P → P
- (P ∧ Q) → P
- (P → Q) → (¬Q → ¬P)
- ∀x P(x) → P(a)
- ∃x P(x) → ∃x P(x)

## How to Run
Run:

## Author
Krish Bhavsar  
Griffith University
