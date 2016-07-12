Set Implicit Arguments.

Require Import QArith.
Require Import QvecArith PerceptronDef.

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

Extraction "/home/charlie/CoqPerceptron/Benchmarks/hs/Perceptron.hs" fueled_perceptron inner_perceptron_MCE.
