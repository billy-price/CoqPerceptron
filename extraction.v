Set Implicit Arguments.

Require Import QArith.
Require Import QvecArith PerceptronDef.

Require Extraction.
Extraction Language Haskell.

Extract Inductive Vector.t =>
  "([])" [ "[]" "(\a _ v -> a : v)" ]
              "(\fNil fCons v -> 
                   case v of 
                     [] -> fNil () 
                     (a : v') -> fCons a O v')".
Extract Inductive prod => "(,)" [ "(,)" ].
Extract Inductive list => "([])" [ "[]" "(:)" ].
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extract Constant Bool.eqb => "(Prelude.==)".
Extract Constant negb => "(Prelude.not)".
Extract Constant Coq.Vectors.Vector.map =>
  "(\g _ l -> Prelude.map g l)".
Extract Constant Coq.Vectors.Vector.map2 =>
  "(\g _ l1 l2 -> Prelude.map (\(x,y) -> g x y) (Prelude.zip l1 l2))".
Extract Constant Coq.Vectors.Vector.fold_left =>
  "(\g a _ l -> Prelude.foldl g a l)".

Definition gas (T : Type) (f : nat -> T) : T := f O.

Extract Constant gas =>
  "(\f -> let infiniteGas = S infiniteGas in f infiniteGas)".

Definition fueled_perceptron
           (n _ : nat)
           (T : list (Qvec n * bool)) (w : Qvec (S n))
  : option (Qvec (S n)) :=
  gas (fun fuel => perceptron fuel T w).

Extraction "./Benchmarks/hs/Perceptron.hs" fueled_perceptron inner_perceptron_MCE.

Extract Inductive positive =>
"Prelude.Integer" [ "(\x -> (Prelude.+) ((Prelude.*) 2 x) 1)"
                    "(\x -> (Prelude.*) 2 x)" "1" ]
              "(\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))".

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

Extract Inductive Q =>
  "Rational" [ "(\n d -> (Data.Ratio.%) n d)" ]
             "(\fNum fDen q -> Prelude.error ""induction on Q unsupported!"")".

Extract Constant Qplus => "(Prelude.+)".
Extract Constant Qmult => "(Prelude.*)".
Extract Constant Qred => "(\x -> x)".
Extract Constant Qeq_bool => "(Prelude.==)".
Extract Constant Qle_bool => "(Prelude.<=)".

Extraction "./Benchmarks/hsopt/Perceptron.hs" fueled_perceptron inner_perceptron_MCE.
