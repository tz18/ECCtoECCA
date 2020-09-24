Require Export reduction.

Lemma church_rosser (g: env) (e e1 e2 e3: @exp 0):
((g |- e =r> e1) ->
(g |- e =r> e2) ->
exists e3, (g |- e1 =r> e3) /\ (g |- e2 =r> e3))%ECCA.
Admitted.
