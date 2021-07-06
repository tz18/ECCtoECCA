-~=How to run our beautiful Coq mechanization=~-

This is easiest to do on Linux but can also work on Cygwin with a bit of effort.

1. Install OPAM 
	(Instructions here: https://opam.ocaml.org/doc/Install.html)
2. If you haven't already: 
	opam switch create 4.12.0 
	(you need make and gcc installed for this)
3. Install Coq and coqide with OPAM: https://coq.inria.fr/opam-using.html 
i.e. 
	opam install opam-depext
	opam-depext coq 
	opam pin add coq 8.13.2
	opam-depext coqide
	opam install coqide
4. Install Coq-Equations:
	opam repo add coq-released https://coq.inria.fr/opam/released
	opam install coq-equations
(4.5) In this folder,run
	git submodule init; git submodule update
5. In this folder, run:
	make
Now all of our beautiful Coq mechanization is compiled.

Table of Contents:
shifted-names/ 	 	  . The shifted-names library from Tyde19 ^1
Common/Atom.v  	 	  . Definition of universes and connection to shifted-names
ECC/ECC.v      	 	  . Luo's Extended Calculus of Constructions (ECC); 
				    grammar, reduction, types, equivalence, etc.
ECCA/core.v    	 	  . The grammar of CC^AE, size measure,
			 	    ANF judgment on terms, induction principles
ECCA/core_lemmas.v 	 	  . Lemmas that naming operations preserve size 
ECCA/reduction.v   	 	  . Small-step reduction and congruence conversion rules
ECCA/reduction_lemmas.v 	  . placeholder
ECCA/equiv.v   	 	  . Equivalence rules
ECCA/equiv_lemmas.v 	 	  . Making equivalence a Coq Equivalence
ECCA/typing.v  	 	  . sub-typing, typing, and well-formed environments
ECCA/typing_lemmas.v 	 	  . weakening, well-typedness lemmas
ECCA/continuations.v	 	  . continuations, ANF judgment on continuations, 
				    continuation types, continuation composition, 
				    heterogeneous composition 
ECCA/continuations_lemmas.v  	  . proof of the naturality lemma from the paper 
ECCA/key_lemmas.v 		  . attempted proofs of cut, cut modulo equivalence, 
				    heterogeneous cut lemmas
translation/translator.v 	  . translating ECC to CC^AE, terms and environments
translation/compositionality.v   . proof of the compositionality lemma from the paper
translation/trans_preservation.v . outlining the proof of the main type preservation theorem

^1 (https://icfp19.sigplan.org/details/tyde-2019-papers/11/Syntax-with-Shifted-Names)
