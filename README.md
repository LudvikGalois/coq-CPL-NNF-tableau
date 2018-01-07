# coq-CPL-NNF-tableau
A verfied tableau prover for classical propositional logic (in NNF)

This was mainly written as a template and proof-of-concept towards
a more general framework for verified tableau provers.

# Structure

## Syntax

This file simply presents the syntax of CPL (already in NNF).

The idea is to automatically generate this file (as well as all the needed proofs)
given the syntax of any logic.

Beyond the syntax it only provides a function to count the number of connectives
in a formula

## Sets

This file instantiates the set type for our formulae (we also instantiate variables
as being natural numbers, but this could be any totally ordered type with equality
being Leibniz equality).

## Semantics

This file defines the semantics of CPL. It also includes an unused proof
that a formula `F` is valid iff `¬F` is satisfiable.

## Tableau

This file defines the Tableau itself, constraining the type such that it can only
be built correctly, requiring the proofs of soundness for the rules in the
construction of the tableau. Since a proof of satisfiability or unsatisfiability
is eventually created for the initial set of formulae, we know that result is
correct (assuming the semantics were defined correctly)

## Extraction

This (along with the `Main.hs` Haskell file) are used to create a simple program
to actually run the prover itself. It also uses Haskell `Integer`s to represent
Coq's `nat`s in a more memory efficient way, but we don't extract any functions
over them to native Haskell functions, so we can be fairly sure this doesn't harm
correctness (since they, like `nat` can be of arbitrary size). 
