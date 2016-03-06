Set Implicit Arguments.

Require Import FunctionalExtensionality.

(* fuel monad *)

Definition M (A : Type) := nat -> option A.

Definition ret (A : Type) (a : A) : M A := fun _ => Some a.

(* [age] runs [m] on fuel [n-1], or fails if there's no fuel left. 
   Its use is purely logical: In order to get a reasonable fixpoint theorem
   [cf. iter_unfold below], we need to ensure that functors [F] are 
   "contractive". *)
Definition age (A : Type) (m : M A) : M A :=
  fun n : nat =>
    match n with
      | O => None
      | S n' => m n'
    end.

Definition bind (A B : Type) (m : M A) (f : A -> M B) : M B :=
  fun n : nat =>
    match m n with
      | None => None
      | Some a => f a n
    end.

(* This section constructs a fixpoint combinator, [fuelFix], and proves 
   the usual unfolding property [fuelFix = F fuelFix] assuming some properties
   of the functor [F]. *)
Section fuelFix.
  Context {A B : Type}.

  Variable F : (A -> M B) -> A -> M B.

  (* We define our own option type in order to erase it at extraction time. *)
  Definition myoption (A : Type) := option A.

  Fixpoint fuelIter (a : A) (n : nat) : myoption B :=
    match n with
      | O => None
      | S n' => F (fun a' _ => fuelIter a' n') a n
    end.

  (* [F] yields [None] when provided 0 fuel. *)
  Variable F0 : forall a G, F G a 0 = None.

  (* [F] is contractive. *)
  Definition contractive :=
    forall a G n,
      (forall a, G a O = None) -> 
      F (fun a' _ => G a' n) a (S n) = F G a (S n).    
  Variable F_contractive : contractive.
  
  Lemma fuelIter_unfold a n : fuelIter a n = F fuelIter a n.
  Proof.
    revert a; induction n.
    { simpl; intros a; rewrite F0; auto.
    }
    intros a; simpl; erewrite F_contractive; eauto.
  Qed.    
  
  Definition fuelFix : A -> M B := fuelIter.

  (* Now here's the main theorem: *)
  Lemma fuelFix_unfold : fuelFix = F fuelFix.
  Proof.
    unfold fuelFix.
    extensionality x; extensionality y.
    apply fuelIter_unfold.
  Qed.
End fuelFix.

Section loeb.
  Context {A B : Type}.
  
  Variable P : nat -> (A -> M B) -> Prop.
  Variable P0 : forall G, P 0 G.
  
  Variable F : (A -> M B) -> A -> M B.
  Variable F0 : forall a G, F G a 0 = None.

  Let fp := fuelFix F.

  Variable P_step : forall n, P n fp -> P (S n) (F fp).

  Variable F_contractive : contractive F.
  
  Lemma ind n : P n fp.
  Proof.
    induction n.
    { intros; apply P0; auto.
    }
    unfold fp; rewrite fuelFix_unfold; auto.
  Qed.
End loeb.  

(* An example: addition on the naturals. Note that we first define a 
   nonrecursive functor (here of type 
     plus_aux
     : (nat * nat -> M nat) -> nat * nat -> M nat)
   that takes as parameters a recursion parameter [F] (which performs 
   all "recursive" calls) and the initial arguments [p : nat * nat]. 
   The currently, the arguments must be uncurried into a single tuple.

   Also note that we "guard" all calls to [F] with an application of [age].
   This is to ensure contractivity (we consume one fuel before every 
   recursive call). 
*)
Definition plus_aux F (p : nat * nat) :=
  age (
  match p with
    | (x, y) =>
      match x with
        | O => ret y
        | S x' => bind (F (x',y)) (fun res => ret (S res))
      end
  end).

Lemma plus_aux_contractive : contractive plus_aux.
Proof.
  intros a G n; revert a G; induction n.
  { simpl; unfold plus_aux; intros [x y] G.
    destruct x; auto.
  }
  intros [x y] G H.
  destruct x; auto.
Qed.  

Definition plus := fuelFix plus_aux.

Lemma plus_unfold : plus = plus_aux plus.
Proof.
  apply fuelFix_unfold.
  { intros [x y] G; destruct x; auto.
  }
  apply plus_aux_contractive.
Qed.

Eval compute in plus (3, 4) 10. (* = Some 7 *)
Eval compute in plus (3, 4) 2. (* = None *)

(* Here's a proof that makes use of [plus_unfold]. 
   (Other more complicated proofs may be made trickier by the use of fuel -- 
    we have to find some general reasoning principles/lemmas that facilitate. *)

Module Playground.
  Require Import Omega.

  Lemma plus0x x n : n >= 1 -> plus (0, x) n = Some x.
  Proof.
    rewrite plus_unfold; simpl.
    destruct n; try omega; auto.
  Qed.

  Lemma plus0x' x n : n >= 1 -> plus (0, x) n = Some x.
  Proof.
    unfold plus.
    set (P := fun n F => n >= 1 -> F (0, x) n = Some x).
    change (P n (fuelFix plus_aux)).
    apply ind; auto.
    { unfold P; intros; omega.
    }
    { (* step *)
      intros nx; unfold P; simpl; intros IH.
      inversion 1; subst; auto.
    }
    apply plus_aux_contractive.
  Qed.    

  Lemma plus_shift x y n : n > S x + y -> plus (S x, y) n = plus (x, S y) n.
  Proof.
    revert x y.
    induction n; auto.
    intros x y H.
    rewrite plus_unfold.
    simpl.
    destruct x.
    unfold bind. rewrite plus0x; try omega. auto.
    unfold bind. rewrite IHn; try omega. auto.
  Qed.
  
  Lemma plusC x y n : n > x + y -> plus (x, y) n = plus (y, x) n.
  Proof.
    revert x y.
    induction n; auto.
    destruct x.
    { simpl. destruct y; auto.
      unfold bind. intros H. assert (H2: n > y) by omega.
      rewrite IHn; try omega.
      assert (H3: n >= 1) by omega.
      rewrite plus0x; auto.
    }
    intros y H.
    rewrite plus_unfold.
    simpl.
    destruct y; simpl. 
    unfold bind.
    rewrite IHn; try omega.
    rewrite plus0x; try omega; auto.
    unfold bind.
    rewrite IHn; try omega.
    rewrite plus_shift; try omega.
    auto.
  Qed.
End Playground.  

(* Here's the Ackermann function: *)

Definition ack_aux F (p : nat * nat) :=
  age (
  match p with
    | (m, n) =>
      match m with
        | O => ret (S n)
        | S m' => match n with
                    | O => F (m', 1)
                    | S n' =>
                      bind (F (m, n'))
                           (fun res => F (m', res))
                  end
      end
  end).

Lemma ack_aux_contractive : contractive ack_aux.
Proof.
  intros a G n; revert a G; induction n.
  { simpl; unfold ack_aux; intros [x y] G H.
    destruct x; auto.
    destruct y; auto.
  }
  intros [x y] G H.
  destruct x; auto.
  destruct y; auto.
Qed.  

Definition ack := fuelFix ack_aux.

Lemma ack_unfold : ack = ack_aux ack.
Proof.
  apply fuelFix_unfold.
  { intros [x y] G; destruct x, y; auto.
  }
  apply ack_aux_contractive.
Qed.

Eval compute in ack (0, 0) 5.
Eval compute in ack (1, 0) 5.
Eval compute in ack (0, 1) 5.
Eval compute in ack (1, 1) 5.  (* = Some 3 *)
Eval compute in ack (2, 2) 10. (* = Some 7 *)

Extract Inlined Constant ret => "".

Extract Constant bind "'a" "'b" "m" "f" => "(\m f -> f m)".
Extraction Inline bind.

Extract Constant age "'a" "m" => "".
Extraction Inline age.

Extract Constant M "'unused" => "".
Extraction Inline M.

Extract Constant myoption "'unused" => "".
Extraction Inline myoption.

Extract Constant fuelIter "'a" "'b" "f" "a" "unused" =>
  "(\f a _ -> f (\a0 -> fuelIter f a0 O) a)". 

Extract Constant fuelFix "'a" "'b" "f" "a" "unused" =>
  "(\f a -> fuelIter f a O)".



