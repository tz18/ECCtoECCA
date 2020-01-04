

Fixpoint fill_hole (e: ECCAcomp) (K: ECCAcont): ECCAconf :=
  match K with
    | actHole => acfComp e
    | actLetHole x B => acfLet x e B
end.

(* Plan: starter function starts namestate at max of atoms in the ECCexp, so all new atoms are higher than old atoms. *)

(* {ns : NameState} *)

Fixpoint trans  (ns: atom) (e: ECCexp) (K: ECCAcont) : ECCAconf :=
  let X := (S ns) in
  let Y := (S (S ns)) in
  let Z := (S (S (S ns))) in
  match e with
    | eId x => (fill_hole (acpVal (avId x)) K)
    | ePi x A B => (fill_hole (acpVal (avPi (x) (trans ns A actHole) (trans ns B actHole))) K)
    | eAbs x A e => (fill_hole (acpVal (avAbs x (trans ns A actHole) (trans ns e actHole))) K)
    | eApp e1 e2 =>
        (trans X e1 (actLetHole X
            (trans Y e2 (actLetHole Y
                (fill_hole (acpApp (avId X) (avId Y)) K)))))
    | eLet x e1 e2 => (trans ns e1 (actLetHole x
                          (trans (ns) e2 K)))
    | eSig x A B => (fill_hole (acpVal (avSig x (trans ns A actHole) (trans ns B actHole))) K)
    | ePair e1 e2 A => (trans X e1 (actLetHole X
            (trans Y e2 (actLetHole Y
               (trans Z A (actLetHole Z
                (fill_hole (avPair (avId X) (avId Y) (avId Z)) K)))))))
    | eFst e => (trans X e (actLetHole X
                   (fill_hole (acpFst (avId X)) K)))
    | eSnd e => (trans X e (actLetHole X
                   (fill_hole (acpSnd X) K)))
    | eTru => (fill_hole (acpVal avTru) K)
    | eFls => (fill_hole (acpVal avFls) K)
    | eBool=> (fill_hole (acpVal avBool) K)
    | eUni u => (fill_hole (acpVal (avUni u)) K)
    | eIf e e1 e2 => (trans X e (actLetHole X 
                        (acfIf (avId X) 
                            (trans Y e1 (actLetHole Y (fill_hole (acpSubst X avTru (avId Y)) K)))
                            (trans Y e1 (actLetHole Y (fill_hole (acpSubst X avFls (avId Y)) K))))))
end.

Definition transStarter (e: ECCexp):=
  trans (fresh (FV e)) e actHole
.

Compute transStarter (LET X := Y in LET Y := type 1 in X)%ECC.
Compute transStarter (fst (<eTru , eFls> as 
                            (Sig X : eBool .. (eIf X eBool (Pi Y : eBool -> eBool))))).