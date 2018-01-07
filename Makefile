all:	prog
automate:
	coqc CpdtTactics.v Automate.v
syntax: automate
	coqc Syntax.v
sets: syntax automate
	coqc Sets.v
semantics: automate syntax sets
	coqc Semantics.v
tableau: automate syntax sets semantics
	coqc Tableau.v

extraction: tableau
	coqc Extraction.v
prog: extraction
	ghc --make -O2 -o NNF Main.hs
clean:
	rm *.o *.vo *.glob *.hi NNFTableau.hs NNF
