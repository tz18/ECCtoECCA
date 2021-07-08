-~=How to run our beautiful Coq mechanization=~-

This is easiest to do on Linux but can also work on Cygwin with a bit of effort.

1. Install OPAM 
	(Instructions here: https://opam.ocaml.org/doc/Install.html)
2. If you haven't already: 
	opam switch create 4.12.0 
	eval $(opam env)
	(you need make and gcc installed for this)
3. Install Coq and coqide with OPAM: https://coq.inria.fr/opam-using.html 
i.e. 
	opam install opam-depext
	eval $(opam env)
	opam-depext coq 
	opam pin add coq 8.13.2
	opam-depext coqide
	opam install coqide
	eval $(opam env)
4. Install Coq-Equations:
	opam repo add coq-released https://coq.inria.fr/opam/released
	opam install coq-equations
	eval $(opam env)
5. In this folder, run:
	make
Now all of our beautiful Coq mechanization is compiled. 
You can open up the individual files in Coqide (or Proof General if you prefer), and step through the proofs.

Table of Contents:
shifted-names/ 	 	  . The shifted-names library from Tyde19 ^1
Common/Atom.v  	 	  . Definition of universes and connection to shifted-names
ECC/ECC.v      	 	  . Luo's Extended Calculus of Constructions (ECC); 
				    grammar, reduction, types, equivalence, etc.
ECCA/core.v    	 	  . The grammar of CC^AE, size measure,
			    ANF judgment on terms, induction principles
ECCA/reduction.v   	  . Small-step reduction and congruence conversion rules
ECCA/reduction_lemmas.v   . Placeholder
ECCA/equiv.v   	 	  . Equivalence rules
ECCA/equiv_lemmas.v 	  . Making equivalence a Coq Equivalence
ECCA/typing.v  	 	  . sub-typing, typing, and well-formed environments
ECCA/typing_lemmas.v 	  . Weakening, well-typedness lemmas (attempted) ^2
ECCA/continuations.v	  . Continuations, ANF judgment on continuations, 
				    continuation types, continuation composition, 
				    heterogeneous composition 
ECCA/continuations_lemmas.v  	  . Proof of the Naturality lemma from the paper ^3
ECCA/key_lemmas.v 		  . Attempted proofs of cut, cut modulo equivalence, 
				    heterogeneous cut lemmas ^2
translation/translator.v 	  . Translating ECC to CC^AE, terms and environments
translation/compositionality.v    . Proof of the Compositionality lemma from the paper ^3
translation/trans_preservation.v  . Outlining the proof of the main type preservation theorem

^1 (https://icfp19.sigplan.org/details/tyde-2019-papers/11/Syntax-with-Shifted-Names)
^2 Late in the process of developing this mechanization, it became apparent that 
   the implementation of type contexts used by shifted-names is broken by the addition
   of definitions, such that the normal type weakening lemma no longer holds.
   This is just a naming issue with the mechanization, not with the paper.
   In Severi and Poll the convention is that new names added to a context 
   are fresh in that context. Using shifted-names, this would mean shifting the context
   by the new name, but this is not currently supported. A more robust implentation
   of contexts is in development, however, this means that the proofs of 
   heterogeneous cut needed for the main type preservation proof are 
   not yet possible.
^3 These are proved with no admitted lemmas.