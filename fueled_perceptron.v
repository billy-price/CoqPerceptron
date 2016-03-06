Set Implicit Arguments.

Require Import ZArith.

Require Import fuel perceptron.

Section fueled_perceptron.
  Variable n : nat. (** the dimensionality *)
  
  Definition perceptron_aux F (Tw : list (Zvec n * bool) * Zvec (S n)) : M (Zvec (S n)) :=
    match Tw with (T, w) => 
      match inner_perceptron T w with
        | None => ret w
        | Some w' => age (F (T, w'))
      end
    end.

  Lemma perceptron_aux_contractive : contractive perceptron_aux.
  Proof.
    unfold contractive.
    intros a G n0 H.
    induction n0.
    { unfold perceptron_aux; destruct a.
      destruct (inner_perceptron l z); auto.
    }
    unfold perceptron_aux; destruct a.
    destruct (inner_perceptron l z); auto.
  Qed.    
  
  Definition fueled_perceptron : list (Zvec n * bool) * Zvec (S n) -> M (Zvec (S n)) :=
    fuelFix perceptron_aux.

  Lemma fueled_perceptron_equiv T w E :
    fueled_perceptron (T, w) E = perceptron E T w.
  Proof.
    revert w.
    induction E; auto.
    simpl.
    intros w.
    destruct (inner_perceptron T w); simpl; auto.
  Qed.    
End fueled_perceptron.

Extraction Language Haskell.

Extraction "Benchmarks/hs/FueledPerceptron.hs" fuelIter fueled_perceptron.

Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extract Inductive Vector.t =>
  "([])" [ "[]" "(\a _ v -> a : v)" ]
              "(\fNil fCons v -> 
                   case v of 
                     [] -> fNil () 
                     (a : v') -> fCons a O v')".                                     

Extract Inductive positive =>
"Prelude.Integer" [ "(\x -> (Prelude.+) ((Prelude.*) 2 x) 1)"
                    "(\x -> (Prelude.*) 2 x)" "1" ]
              "(\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))".

Extract Inductive N =>
  "Prelude.Integer" [ "0" "" ]
              "(\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)".

Extract Inductive Z =>
  "Prelude.Integer" [ "0" "" "(\x -> (Prelude.*) x (-1))" ]
              "(\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))".

Extract Constant Z.add => "(Prelude.+)".
Extract Constant Z.mul => "(Prelude.*)".
Extract Constant Z.eqb => "(Prelude.==)".
Extract Constant Z.gtb => "(Prelude.>)".
Extract Constant Z.geb => "(Prelude.>=)".
Extract Constant Bool.eqb => "(Prelude.==)".
Extract Constant negb => "(Prelude.not)".
Extract Constant Coq.Vectors.Vector.map =>
  "(\g _ l -> Prelude.map g l)".
Extract Constant Coq.Vectors.Vector.map2 =>
  "(\g _ l1 l2 -> Prelude.map (\(x,y) -> g x y) (Prelude.zip l1 l2))".
Extract Constant Coq.Vectors.Vector.fold_left =>
  "(\g a _ l -> Prelude.foldl g a l)".

Extraction "Benchmarks/hs/FueledPerceptronOpt.hs" fuelIter fueled_perceptron.
