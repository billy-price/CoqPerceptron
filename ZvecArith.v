Require Import Coq.Vectors.Vector.
Require Import ZArith.
Require Import Omega.

(*****************************************************************************************
    Definitions and Fixpoints for operations on Zvecs
    (Also includes Fixpoints/Computation on Training Data: list ((Zvec n)*bool))
 *****************************************************************************************)

Definition Zvec := Vector.t Z. 
Definition Zvec_plus {n:nat} (v1 v2 : Zvec n) := map2 Zplus v1 v2.
Definition Zvec_dot {n:nat} (v1 v2 : Zvec n) := fold_left Zplus Z0 (map2 Zmult v1 v2).
Definition Zvec_normsq {n:nat} (v1 : Zvec n) := Zvec_dot v1 v1.
Definition Zvec_zero (n : nat) : Zvec n := const Z0 n.

Definition class (i : Z) : bool := Z.geb i Z0.
Definition correct_class (i : Z) (l : bool) : bool :=
  andb (Bool.eqb l (class i)) (negb (Z.eqb i Z0)).
Definition Zvec_mult_class {n:nat} (l :bool) (f : Zvec n) := if l then f else map (Zmult (Zneg 1)) f.
Definition consb {n : nat} (v : Zvec n) := cons _ (Zpos 1) _ v.


Fixpoint Zvec_sum_class {n : nat} (w : Zvec (S n)) (M : list ((Zvec n)*bool)) : Zvec (S n) :=
  match M with
  | List.nil => w
  | List.cons (f, l) M' => Zvec_sum_class (Zvec_plus w (Zvec_mult_class l (consb f))) M'
  end.

Fixpoint Zvec_sum {n : nat} (M : list ((Zvec n)*bool)) : Zvec (S n) :=
  match M with
  | List.nil => Zvec_zero (S n)
  | List.cons (f, l) M' => Zvec_plus (Zvec_mult_class l (consb f)) (Zvec_sum M')
  end.
 
Fixpoint min_element_product {n : nat} (w : Zvec (S n)) (T: list ((Zvec n)*bool)) : Z :=
  match T with
  | List.nil => (Zpos 1) (* avoid divide by zero *)
  | List.cons (f, l) List.nil => Zvec_dot w (Zvec_mult_class l (consb f))
  | List.cons (f, l) T' =>
      if (Z.leb (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w T'))
      then (Zvec_dot w (Zvec_mult_class l (consb f)))
      else (min_element_product w T')
  end.

Fixpoint max_element_normsq {n : nat} (T: list ((Zvec n)*bool)) : Z :=
  match T with
  | List.nil => (Zpos 1)
  | List.cons (f, l) List.nil => (Zvec_normsq (consb f))
  | List.cons (f, l) T' =>
      if (Z.geb (Zvec_normsq (consb f)) (max_element_normsq T'))
      then (Zvec_normsq (consb f))
      else (max_element_normsq T')
  end.

Fixpoint Zvec_sum_normsq {n:nat} (L: list ((Zvec n)*bool)) : Z :=
  match L with
  | List.nil => Z0
  | List.cons (f, l) L' => Z.add (Zvec_normsq (consb f)) (Zvec_sum_normsq L')
  end.

Fixpoint Zvec_sum_dot {n:nat} (w : Zvec (S n)) (L: list ((Zvec n)*bool)) : Z :=
  match L with
  | List.nil => Z0
  | List.cons (f, l) L' => Z.add (Zvec_dot w (Zvec_mult_class l (consb f))) (Zvec_sum_dot w L')
  end.

Fixpoint Zvec_foil {n:nat} (w : Zvec (S n)) (L: list ((Zvec n)*bool)) : Z :=
  match L with
  | List.nil => Z0
  | List.cons (f, l) L' => Z.add (Zvec_dot w (Zvec_mult_class l (consb f)))
                                 (Zvec_foil (Zvec_plus w (Zvec_mult_class l (consb f))) L')
  end.

 (****************************************************************************************
    Case Analysis for Vectors + Induction Principles for multiple vectors.
  ****************************************************************************************)
Definition Vector_0_is_nil {A} (v : t A 0) : v = nil A :=
match v with
| nil => eq_refl
end.

Definition Vector_S_is_cons {A} {n} (v: t A (S n)) : exists a, exists v0, v = cons A a n v0 :=
match v as v' in t _ n1
  return match n1 return t A n1 -> Prop with
  |0 => fun _ => True
  |S n => fun v => exists a, exists v0, v = cons A a n v0 end v' with
| nil => I
| cons a _ v0 => ex_intro _ a (ex_intro _ v0 (refl_equal _))
end.

Lemma mutual_induction : forall {A B: Type} (P : forall {n : nat}, t A n -> t B n -> Prop),
  (P (nil A) (nil B)) -> (forall (h1 : A) (h2 : B) {n : nat} (t1 : t A n) (t2 : t B n),
  (P t1 t2) -> (P (cons A h1 n t1) (cons B h2 n t2))) ->
  forall {n : nat} (v1 : t A n) (v2 : t B n), P v1 v2.
Proof.
  intros. induction n. rewrite (Vector_0_is_nil v1). rewrite (Vector_0_is_nil v2). apply H.
  assert (H1 := Vector_S_is_cons v1). assert (H2 := Vector_S_is_cons v2).
  destruct H1 as [a [v1' H1]]. destruct H2 as [b [v2' H2]]. rewrite H1. rewrite H2. apply H0. apply IHn. Qed.

Lemma triple_induction : forall {A B C: Type} (P : forall {n : nat}, t A n -> t B n -> t C n-> Prop),
  (P (nil A) (nil B) (nil C)) -> (forall (h1 : A) (h2 : B) (h3 : C) {n : nat} (t1 : t A n) (t2 : t B n) ( t3 : t C n),
  (P t1 t2 t3) -> (P (cons A h1 n t1) (cons B h2 n t2) (cons C h3 n t3))) ->
  forall {n : nat} (v1 : t A n) (v2 : t B n) (v3 : t C n), P v1 v2 v3.
Proof.
  intros. induction n. rewrite (Vector_0_is_nil v1). rewrite (Vector_0_is_nil v2). rewrite (Vector_0_is_nil v3). apply H.
  assert (H1 := Vector_S_is_cons v1). assert (H2 := Vector_S_is_cons v2). assert (H3 := Vector_S_is_cons v3).
  destruct H1 as [a [v1' H1]]. destruct H2 as [b [v2' H2]]. destruct H3 as [c [v3' H3]]. rewrite H1. rewrite H2. rewrite H3.
  apply H0. apply IHn. Qed.

 (****************************************************************************************
    Proofs about Arithmetic on Zvec, Fixpoints/Computations on Zvecs / Training Data.
  ****************************************************************************************)
Lemma fold_left_add_unfold : forall {n : nat} (v1 v2 : Zvec n) (A : Z),
 fold_left Z.add A (map2 Z.mul v1 v2) = Z.add A (fold_left Z.add Z0 (map2 Z.mul v1 v2)).
Proof.
  intros n v1 v2. set (P := fun {n : nat} (v1 v2 : Zvec n) => forall A : Z,
  fold_left Z.add A (map2 Z.mul v1 v2) = Z.add A (fold_left Z.add Z0 (map2 Z.mul v1 v2))).
  change (P n v1 v2). apply mutual_induction; unfold P; intros. apply Zplus_0_r_reverse. simpl. rewrite H.
  assert (fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2) = Z.add (Z.mul h1 h2) (fold_left Z.add Z0 (map2 Z.mul t1 t2))).
    apply H. rewrite H0. rewrite Z.add_assoc. reflexivity. Qed.

Lemma fold_left_add_unfold_1 : forall {n : nat} (v1 v2 : Zvec n) (A : Z),
 fold_left Z.add (Z.add 1 A) (map2 Z.mul v1 v2) = Z.add A (fold_left Z.add (Z.pos 1) (map2 Z.mul v1 v2)).
Proof.
  intros. rewrite Z.add_comm. rewrite fold_left_add_unfold. rewrite <- Z.add_assoc.
  rewrite <- fold_left_add_unfold. reflexivity. Qed.

Lemma Zvec_consb_gt_0 : forall {n : nat} (f : Zvec n),
 Z.gt (Zvec_normsq (consb f)) Z0.
Proof.
  intros n f. unfold Zvec_normsq. unfold Zvec_dot. unfold consb. simpl.
  induction f. simpl. omega.
  simpl. destruct (Z.mul h h) eqn:H0.
    apply IHf.
  { destruct p.
    assert (H1: (Z.pos (Pos.succ p)~0) = (Z.add 1 (Z.pos p~1))).
      simpl. reflexivity.
    rewrite H1. rewrite fold_left_add_unfold_1.
    assert (H2 := Zsgn_spec (Z.pos p~1)). inversion H2; inversion H;
    [omega | inversion H3; inversion H5 | inversion H3; inversion H5].
    assert (H1: (Z.pos p~1) = (Z.add (Z.pos 1) (Z.pos p~0))).
      simpl. reflexivity.
    rewrite H1. rewrite fold_left_add_unfold_1.
    assert (H2 := Zsgn_spec (Z.pos p~1)). inversion H2; inversion H;
    [omega | inversion H3; inversion H5 | inversion H3; inversion H5].
    assert (H1: (Z.pos 2) = (Z.add (Z.pos 1) (Z.pos 1))).
      reflexivity.
    rewrite H1. rewrite fold_left_add_unfold_1. omega.
  } destruct h; inversion H0. Qed.

Lemma Zvec_normsq_not_neg : forall {n : nat} (f : Zvec n),
 Z.le Z0 (Zvec_normsq f).
Proof.
  intros. induction f. unfold Zvec_normsq, Zvec_dot. reflexivity.
  unfold Zvec_normsq, Zvec_dot. simpl.
  destruct h eqn:H. apply IHf. rewrite fold_left_add_unfold.
  destruct (fold_left Z.add Z0 (map2 Z.mul f f)) eqn:H0; simpl; try(apply Zle_0_pos).
  unfold Zvec_normsq, Zvec_dot in IHf; rewrite H0 in IHf. assert (H1 := (Zlt_neg_0 p0)). omega.
  simpl. rewrite fold_left_add_unfold.
  destruct (fold_left Z.add Z0 (map2 Z.mul f f)) eqn:H0; simpl; try(apply Zle_0_pos).
  unfold Zvec_normsq, Zvec_dot in IHf; rewrite H0 in IHf. assert (H1 := (Zlt_neg_0 p0)). omega. Qed.

Lemma Zvec_sum_normsq_ge_0 : forall {n : nat} (L : list ((Zvec n)*bool)),
  Z.le Z0 (Zvec_sum_normsq L).
Proof.
  intros. induction L.
  simpl. omega.
  destruct a as [f l]. simpl. assert (H := Zvec_normsq_not_neg (consb f)). omega. Qed.

Lemma Zvec_normsq_zvec_zero : forall (n : nat),
 Zvec_normsq (Zvec_zero n) = Z0.
Proof.
  intros n. induction n. unfold Zvec_zero, Zvec_normsq, Zvec_dot. reflexivity.
  unfold Zvec_zero, Zvec_normsq, Zvec_dot. simpl. apply IHn. Qed.

Lemma normsq_mult_neg_1_same : forall {n : nat} (f : Zvec n),
  Zvec_normsq f = Zvec_normsq (map (Z.mul (-1)) f).
Proof.
  intros. induction f. simpl. reflexivity.
  unfold Zvec_normsq, Zvec_dot. unfold Zvec_normsq, Zvec_dot in IHf.
  simpl. destruct h; try (apply IHf); simpl; try (rewrite fold_left_add_unfold;
  rewrite IHf; rewrite <- fold_left_add_unfold; auto). Qed.

Lemma Zvec_dot_mult_neg_1 : forall {n:nat} (v1 v2 : Zvec n),
  Zvec_dot v1 (map (Z.mul (Z.neg 1)) v2) = Z.mul (Z.neg 1) (Zvec_dot v1 v2).
Proof.
  intros n v1 v2. set (P := fun (n : nat) (v1 v2 : t Z n) => Zvec_dot v1 (map (Z.mul (Z.neg 1)) v2) =
  Z.mul (Z.neg 1) (Zvec_dot v1 v2)). change (P n v1 v2). apply mutual_induction.
  unfold P. unfold Zvec_dot. reflexivity. intros.
  unfold P in H. unfold P. unfold Zvec_dot.
  assert (fold_left Z.add Z0 (map2 Z.mul (cons Z h1 n0 t1) (map (Z.mul (Z.neg 1)) (cons Z h2 n0 t2))) =
  fold_left Z.add (Z.mul (Z.neg 1) (Z.mul h1 h2)) (map2 Z.mul t1 (map (Z.mul (Z.neg 1)) t2))).
  assert (fold_left Z.add Z0 (map2 Z.mul (cons Z h1 n0 t1) (map (Z.mul (Z.neg 1)) (cons Z h2 n0 t2))) =
  fold_left Z.add (Z.mul h1 (Z.mul (Zneg 1) h2)) (map2 Z.mul t1 (map (Z.mul (Z.neg 1)) t2))). reflexivity.
  rewrite H0. assert (Z.mul h1 (Z.mul (Z.neg 1) h2) = Z.mul (Z.neg 1) (Z.mul h1 h2)).
  rewrite Z.mul_assoc. rewrite Z.mul_comm. rewrite Z.mul_assoc. rewrite Z.mul_assoc.
  rewrite Z.mul_comm. assert (Z.mul h1 h2 = Z.mul h2 h1). apply Z.mul_comm. rewrite <- H1.
  apply Z.mul_assoc. rewrite H1. reflexivity. rewrite H0. rewrite fold_left_add_unfold.
  unfold Zvec_dot in H. rewrite H.
  assert (fold_left Z.add Z0 (map2 Z.mul (cons Z h1 n0 t1) (cons Z h2 n0 t2)) =
          fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2)). reflexivity. rewrite H1.
  assert (fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2) =
          Z.add (Z.mul h1 h2) (fold_left Z.add Z0 (map2 Z.mul t1 t2))). apply fold_left_add_unfold.
  rewrite H2. omega. Qed.

Lemma Z_add_sub_mult_eq : forall (A B C : Z),
  Z.mul A B = Z.sub (Z.mul (Z.add A C) B) (Z.mul C B).
Proof.
  intros. rewrite <- (Zmult_minus_distr_r (Z.add A C) C B).
  rewrite <- Z.add_opp_r. rewrite <- Z.add_assoc. rewrite Z.add_opp_r.
  rewrite <- Zminus_diag_reverse. rewrite <- Zplus_0_r_reverse. reflexivity. Qed.

Lemma Zvec_dot_add_sub_mult_eq : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_dot v1 v2 = (Z.sub (Zvec_dot (Zvec_plus v1 v3) v2) (Zvec_dot v3 v2)).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Zvec n) => Zvec_dot v1 v2 = (Z.sub (Zvec_dot (Zvec_plus v1 v3) v2) (Zvec_dot v3 v2))).
  change (P n v1 v2 v3). apply triple_induction; unfold P; clear P; intros.
  { unfold Zvec_dot. reflexivity. }
  simpl. unfold Zvec_dot. simpl. rewrite fold_left_add_unfold. fold (Zvec_dot t1 t2).
  assert (fold_left Z.add (Z.mul (Z.add h1 h3) h2) (map2 Z.mul (Zvec_plus t1 t3) t2) =
          Z.add (Z.mul (Z.add h1 h3) h2) (fold_left Z.add Z0 (map2 Z.mul (Zvec_plus t1 t3) t2))).
    apply fold_left_add_unfold. rewrite H0. clear H0.
  assert (fold_left Z.add (Z.mul h3 h2) (map2 Z.mul t3 t2) = Z.add (Z.mul h3 h2) (fold_left Z.add Z0 (map2 Z.mul t3 t2))).
  apply fold_left_add_unfold. rewrite H0. clear H0. fold (Zvec_dot (Zvec_plus t1 t3) t2). fold (Zvec_dot t3 t2).
  rewrite H. assert (forall (A B C D : Z), Z.sub (Z.add A B) (Z.add C D) = Z.add (Z.sub A C) (Z.sub B D)). intros. omega.
  rewrite H0; clear H0. rewrite Z_add_sub_mult_eq with (C := h3). reflexivity. Qed.

Lemma Zvec_normsq_cons : forall {n : nat} (h : Z) (t : Zvec n),
  Zvec_normsq (cons Z h n t) = Z.add (Z.mul h h) (Zvec_normsq t).
Proof.
  intros. unfold Zvec_normsq, Zvec_dot. simpl. apply fold_left_add_unfold. Qed.

Lemma Zvec_dot_cons : forall {n : nat} (h1 h2 : Z) (t1 t2 : Zvec n),
  Zvec_dot (cons Z h1 n t1) (cons Z h2 n t2) = Z.add (Z.mul h1 h2) (Zvec_dot t1 t2).
Proof.
  intros. unfold Zvec_dot. simpl. apply fold_left_add_unfold. Qed.

Lemma Zvec_normsq_plus : forall {n: nat} (v1 v2 : Zvec n),
  Zvec_normsq (Zvec_plus v1 v2) = Z.add (Z.add (Zvec_normsq v1) (Z.mul 2 (Zvec_dot v1 v2))) (Zvec_normsq v2).
Proof.
  intros. set (P := fun n (v1 v2 : Zvec n) => Zvec_normsq (Zvec_plus v1 v2) = 
  Z.add (Z.add (Zvec_normsq v1) (Z.mul 2 (Zvec_dot v1 v2))) (Zvec_normsq v2)).
  change (P n v1 v2). apply mutual_induction; unfold P; intros. reflexivity.
  unfold Zvec_plus. assert (map2 Z.add (cons Z h1 n0 t1) (cons Z h2 n0 t2) =
                           cons Z (Z.add h1 h2) n0 (map2 Z.add t1 t2)). reflexivity. rewrite H0; clear H0.
  repeat (rewrite Zvec_normsq_cons). fold (Zvec_plus t1 t2). rewrite H.
  rewrite Zvec_dot_cons. assert (Z.mul 2 (Z.add (Z.mul h1 h2) (Zvec_dot t1 t2)) = 
  Z.add (Z.mul 2 (Z.mul h1 h2)) (Z.mul 2 (Zvec_dot t1 t2))). apply Z.mul_add_distr_l. rewrite H0; clear H0.
  assert ((Z.mul (Z.add h1 h2) (Z.add h1 h2)) = Z.add (Z.mul h1 h1) (Z.add (Z.mul 2 (Z.mul h1 h2)) (Z.mul h2 h2))).
  rewrite Z.mul_add_distr_l. repeat (rewrite Z.mul_add_distr_r). assert (Z.mul 2 (Z.mul h1 h2) = Z.mul (Z.mul h1 h2) 2). omega.
  rewrite H0; clear H0. rewrite <- Zplus_diag_eq_mult_2. repeat (rewrite Z.add_assoc).
  assert (Z.mul h1 h2 = Z.mul h2 h1). apply Z.mul_comm. rewrite H0; clear H0. reflexivity.
  rewrite H0; clear H0. omega. Qed.

Lemma Zvec_dot_Zvec_zero : forall {n : nat} (v : Zvec n),
  Zvec_dot (Zvec_zero n) v = Z0.
Proof.
  intros. induction v. unfold Zvec_zero, Zvec_dot. reflexivity.
  unfold Zvec_dot. simpl. apply IHv. Qed.

Lemma Zvec_dot_Zvec_zero_r : forall {n : nat} (v : Zvec n),
  Zvec_dot v (Zvec_zero n) = Z0.
Proof.
  intros. induction v. unfold Zvec_zero, Zvec_dot. reflexivity.
  unfold Zvec_dot. simpl. rewrite <- Zmult_0_r_reverse. apply IHv. Qed.

Lemma Zvec_plus_Zvec_zero : forall {n : nat} (v : Zvec n),
  Zvec_plus (Zvec_zero n) v = v.
Proof.
  intros. induction v. unfold Zvec_plus, Zvec_zero. reflexivity.
  unfold Zvec_plus, Zvec_zero. simpl. unfold Zvec_plus, Zvec_zero in IHv.
  rewrite IHv. reflexivity. Qed.

Lemma Zvec_plus_Zvec_zero_r : forall {n : nat} (v : Zvec n),
  Zvec_plus v (Zvec_zero n) = v.
Proof.
  intros. induction v. unfold Zvec_plus, Zvec_zero. reflexivity.
  unfold Zvec_plus, Zvec_zero. simpl. unfold Zvec_plus, Zvec_zero in IHv.
  rewrite IHv. rewrite <- Zplus_0_r_reverse. reflexivity. Qed.

Lemma Zvec_dot_dist_l : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_dot (Zvec_plus v1 v2) v3 = Z.add (Zvec_dot v1 v3) (Zvec_dot v2 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Zvec n) =>
  Zvec_dot (Zvec_plus v1 v2) v3 = Z.add (Zvec_dot v1 v3) (Zvec_dot v2 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; intros. reflexivity.
  simpl. rewrite Zvec_dot_cons. rewrite H.
  unfold Zvec_dot. simpl. assert (fold_left Z.add (Z.mul h1 h3) (map2 Z.mul t1 t3) =
  Z.add (Z.mul h1 h3) (fold_left Z.add Z0 (map2 Z.mul t1 t3))). apply fold_left_add_unfold.
  rewrite H0; clear H0. assert (fold_left Z.add (Z.mul h2 h3) (map2 Z.mul t2 t3) =
  Z.add (Z.mul h2 h3) (fold_left Z.add Z0 (map2 Z.mul t2 t3))). apply fold_left_add_unfold.
  rewrite H0; clear H0. fold (Zvec_dot t1 t3). fold (Zvec_dot t2 t3). rewrite Z.add_assoc.
  rewrite Z.add_assoc. rewrite Z.mul_add_distr_r. omega. Qed.

Lemma Zvec_dot_dist_r : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_dot v1 (Zvec_plus v2 v3) = Z.add (Zvec_dot v1 v2) (Zvec_dot v1 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Zvec n) =>
  Zvec_dot v1 (Zvec_plus v2 v3) = Z.add (Zvec_dot v1 v2) (Zvec_dot v1 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. rewrite Zvec_dot_cons. rewrite H. unfold Zvec_dot. simpl.
  assert (fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2) =
  Z.add (Z.mul h1 h2) (fold_left Z.add Z0 (map2 Z.mul t1 t2))). apply fold_left_add_unfold.
  rewrite H0; clear H0. fold (Zvec_dot t1 t2).
  assert (fold_left Z.add (Z.mul h1 h3) (map2 Z.mul t1 t3) =
  Z.add (Z.mul h1 h3) (fold_left Z.add Z0 (map2 Z.mul t1 t3))). apply fold_left_add_unfold.
  rewrite H0; clear H0. fold (Zvec_dot t1 t3). repeat (rewrite Z.add_assoc).
  rewrite Z.mul_add_distr_l. omega. Qed.

Lemma Zvec_plus_shuffle : forall {n: nat} (v1 v2 v3 : Zvec n),
  Zvec_plus (Zvec_plus v1 v2) v3 = Zvec_plus (Zvec_plus v1 v3) v2.
Proof.
  intros. set (P := fun n (v1 v2 v3 : Zvec n) => 
  Zvec_plus (Zvec_plus v1 v2) v3 = Zvec_plus (Zvec_plus v1 v3) v2). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. rewrite H. assert (Z.add (Z.add h1 h2) h3 = Z.add (Z.add h1 h3) h2). omega.
  rewrite H0; clear H0. reflexivity. Qed.

Lemma Zvec_plus_comm : forall {n : nat} (v1 v2 : Zvec n),
  Zvec_plus v1 v2 = Zvec_plus v2 v1.
Proof.
  intros. set (P := fun n (v1 v2 : Zvec n) => Zvec_plus v1 v2 = Zvec_plus v2 v1).
  change (P n v1 v2). apply mutual_induction; unfold P; intros; clear P. reflexivity.
  simpl. rewrite H. rewrite Z.add_comm. reflexivity. Qed.

Lemma Zvec_foil_w_0 : forall {n : nat} (v1 v2 : Zvec (S n)) (L : list ((Zvec n)*bool)),
  Z.add (Zvec_dot v1 (Zvec_sum L)) (Zvec_foil v2 L) = Zvec_foil (Zvec_plus v2 v1) L.
Proof.
  intros; generalize dependent v1; generalize dependent v2; induction L; intros.
  simpl. rewrite Zvec_dot_Zvec_zero_r. reflexivity. destruct a as [f l].
  unfold Zvec_sum. fold (Zvec_sum L). unfold Zvec_foil.
  fold (Zvec_foil  (Zvec_plus v2 (Zvec_mult_class l (consb f)))).
  fold (Zvec_foil (Zvec_plus (Zvec_plus v2 v1) (Zvec_mult_class l (consb f)))). rewrite Zvec_dot_dist_r.
  rewrite Z.add_assoc.
  assert (forall (A B C D : Z), Z.add (Z.add (Z.add A B) C) D = Z.add (Z.add A C) (Z.add B D)). intros. omega.
  rewrite H; clear H. rewrite IHL. rewrite <- Zvec_dot_dist_l.
  rewrite Zvec_plus_shuffle. rewrite Zvec_plus_comm. reflexivity. Qed.

Lemma Zvec_dot_sum_eq : forall {n : nat} (w : Zvec (S n)) (L : list ((Zvec n)*bool)),
  Zvec_dot w (Zvec_sum L) = Zvec_sum_dot w L.
Proof.
  intros. induction L. simpl.  apply Zvec_dot_Zvec_zero_r. destruct a as [f l].
  simpl. rewrite Zvec_dot_dist_r. rewrite IHL. reflexivity. Qed.

Lemma Zvec_foil_0_w : forall {n : nat} (v1 v2 : Zvec (S n)) (L : list ((Zvec n)*bool)),
  Zvec_foil v1 L = Z.sub (Zvec_foil (Zvec_plus v1 v2) L) (Zvec_sum_dot v2 L).
Proof.
  intros. assert (H := Zvec_foil_w_0 v2 v1 L).
  rewrite <- Zplus_minus_eq with _ _ (Zvec_foil v1 L). reflexivity.
  rewrite <- Zvec_dot_sum_eq. rewrite H. reflexivity. Qed.

Lemma Zvec_normsq_eq_sum_normsq_foil : forall {n: nat} (L : list ((Zvec n)*bool)),
  Zvec_normsq (Zvec_sum L) = Z.add (Zvec_sum_normsq L) (Z.mul 2 (Zvec_foil (Zvec_zero (S n)) L)).
Proof.
  intros. induction L. simpl. apply Zvec_normsq_zvec_zero.
  destruct a as [f l]. unfold Zvec_normsq. unfold Zvec_sum. fold (Zvec_sum L).
  unfold Zvec_sum_normsq. fold (Zvec_sum_normsq L). unfold Zvec_foil.
  fold (Zvec_foil (Zvec_plus (Zvec_zero (S n)) (Zvec_mult_class l (consb f))) L).
  fold (Zvec_normsq (Zvec_plus (Zvec_mult_class l (consb f)) (Zvec_sum L))).
  rewrite Zvec_normsq_plus. assert (Zvec_normsq (Zvec_mult_class l (consb f)) = (Zvec_normsq (consb f))).
  destruct l. reflexivity. unfold Zvec_mult_class. rewrite <- normsq_mult_neg_1_same. reflexivity.
  rewrite H; clear H. rewrite IHL. rewrite Z.add_assoc.
  assert (Z.add (Z.mul 2 (Zvec_dot (Zvec_mult_class l (consb f)) (Zvec_sum L))) (Zvec_sum_normsq L) =
          Z.add (Zvec_sum_normsq L) (Z.mul 2 (Zvec_dot (Zvec_mult_class l (consb f)) (Zvec_sum L)))).
  apply Z.add_comm. repeat (rewrite <- Z.add_assoc).
  assert (Z.add (Z.mul 2 (Zvec_dot (Zvec_mult_class l (consb f)) (Zvec_sum L))) 
  (Z.add (Zvec_sum_normsq L) (Z.mul 2 (Zvec_foil (Zvec_zero (S n)) L))) = 
  (Z.add (Z.add (Z.mul 2 (Zvec_dot (Zvec_mult_class l (consb f)) (Zvec_sum L)))
  (Zvec_sum_normsq L)) (Z.mul 2 (Zvec_foil (Zvec_zero (S n)) L)))). apply Z.add_assoc.
  rewrite H0; clear H0. rewrite H; clear H. rewrite <- Z.add_assoc. rewrite <- Z.mul_add_distr_l.
  rewrite Zvec_foil_w_0. rewrite Zvec_dot_Zvec_zero. rewrite Zvec_plus_Zvec_zero. reflexivity. Qed.

Lemma Zvec_plus_assoc : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_plus (Zvec_plus v1 v2) v3 = Zvec_plus v1 (Zvec_plus v2 v3).
Proof.
  intros. set (P := fun n (v1 v2 v3 : Zvec n) => 
  Zvec_plus (Zvec_plus v1 v2) v3 = Zvec_plus v1 (Zvec_plus v2 v3)). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. rewrite H. rewrite Z.add_assoc. reflexivity. Qed.

Lemma Zvec_foil_append : forall {n : nat} (L1 L2 : list ((Zvec n)*bool)) (v : Zvec (S n)),
  Zvec_foil v (List.app L1 L2) = Z.add (Zvec_foil v L1) (Zvec_foil (Zvec_plus v (Zvec_sum L1)) L2).
Proof.
  intros n L1. induction L1; intros. simpl. rewrite Zvec_plus_Zvec_zero_r. reflexivity.
  destruct a as [f l]. simpl. rewrite IHL1. rewrite Zvec_plus_assoc. 
  rewrite Z.add_assoc. reflexivity. Qed.

Lemma Zvec_sum_sum_class : forall {n : nat} (w : Zvec (S n)) (L : list ((Zvec n)*bool)),
  Zvec_plus w (Zvec_sum L) = Zvec_sum_class w L.
Proof.
  intros. generalize dependent w; induction L; intros. simpl. apply Zvec_plus_Zvec_zero_r.
  destruct a as [f l]. simpl. rewrite <- Zvec_plus_assoc. apply IHL. Qed.

Lemma Zvec_sum_class_append : forall {n : nat} (w0: Zvec (S n)) (M1 M2: (list ((Zvec n)*bool))),
  Zvec_sum_class (Zvec_sum_class w0 M1) M2 = Zvec_sum_class w0 (List.app M1 M2).
Proof.
  intros n w0 M1. generalize dependent w0. induction M1; intros.
  { auto. } destruct a as [f l]. simpl. apply IHM1. Qed.

Lemma Zvec_dot_comm : forall {n : nat} (v1 v2 : Zvec n),
  Zvec_dot v1 v2 = Zvec_dot v2 v1.
Proof.
  intros. set (P := fun n (v1 v2 : Zvec n) => Zvec_dot v1 v2 = Zvec_dot v2 v1).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros. reflexivity.
  repeat (rewrite Zvec_dot_cons). rewrite H. rewrite Z.mul_comm. reflexivity. Qed.

Lemma Zvec_dot_Not_Zvec_zero : forall {n : nat} (v1 v2 : Zvec n),
  Zvec_dot v1 v2 <> Z0 -> v1 <> Zvec_zero n /\ v2 <> Zvec_zero n.
Proof.
  intros. split. unfold not; intros. subst. apply H. apply Zvec_dot_Zvec_zero.
  unfold not; intros. subst. rewrite Zvec_dot_comm in H. apply H. apply Zvec_dot_Zvec_zero.
Qed.

Lemma Zvec_cons_Not_Zvec_zero : forall {n : nat} (v1 : Zvec n) (h : Z),
  cons Z h n v1 <> Zvec_zero (S n) -> h <> Z0 \/ v1 <> Zvec_zero n.
Proof.
  intros n v1; induction v1; intros. unfold Zvec_zero in H. simpl in H. unfold not in H.
  left. destruct h. exfalso. apply H. reflexivity.
  assert (H0 := Zgt_pos_0 p). omega. assert (H0 := Zlt_neg_0 p). omega.
  destruct h0. right. unfold not. intros. rewrite H0 in H. apply H. unfold Zvec_zero. reflexivity.
  left. assert (H0 := Zgt_pos_0 p). omega. left. assert (H0 := Zlt_neg_0 p). omega. Qed.

Lemma Zvec_normsq_Not_Zvec_Zero : forall {n : nat} (v1 : Zvec n),
  v1 <> Zvec_zero n -> Z.gt (Zvec_normsq v1) Z0.
Proof.
  intros. induction v1. exfalso. apply H. reflexivity.
  apply Zvec_cons_Not_Zvec_zero in H. inversion H. destruct h; [exfalso; apply H0; reflexivity| |];
  try (rewrite Zvec_normsq_cons; assert (H1 := Zvec_normsq_not_neg v1)).
  assert (H2 : Z.lt Z0 (Z.pos p)). assert (H2 := Zgt_pos_0 p). omega.
  assert (H3 := Z.mul_pos_pos (Z.pos p) (Z.pos p) H2 H2). omega.
  assert (H3 := Z.mul_neg_neg (Z.neg p) (Z.neg p) (Zlt_neg_0 p) (Zlt_neg_0 p)). omega.
  apply IHv1 in H0. rewrite Zvec_normsq_cons. assert (H1 := Z.square_nonneg h). omega. Qed.

Lemma Zvec_sum_dot_append : forall {n : nat} (L1 L2 : list ((Zvec n)*bool)) (w : Zvec (S n)),
  Zvec_sum_dot w (List.app L1 L2) = Z.add (Zvec_sum_dot w L1) (Zvec_sum_dot w L2).
Proof.
  intros n L1; induction L1; intros. reflexivity. destruct a as [f l]. simpl. rewrite IHL1.
  repeat (rewrite Z.add_assoc). reflexivity. Qed.

Lemma Zfoil : forall (A B C D : Z),
  Z.mul (Z.add A B) (Z.add C D) = Z.add (Z.add (Z.add (Z.mul A C) (Z.mul A D)) (Z.mul B C)) (Z.mul B D).
Proof.
  intros. rewrite Z.mul_add_distr_r. repeat (rewrite Z.mul_add_distr_l). apply Z.add_assoc. Qed.

Lemma CSHH : forall (A B : Z),
  Z.le (Z.add (Z.mul A B) (Z.mul A B)) (Z.add (Z.mul A A) (Z.mul B B)).
Proof.
  intros. assert (Z.mul (Z.sub A B) (Z.sub A B) = Z.sub (Z.add (Z.mul A A) (Z.mul B B)) (Z.add (Z.mul A B) (Z.mul A B))).
  repeat rewrite <- Z.add_opp_r. rewrite Zfoil. rewrite Z.add_opp_r.
  rewrite Z.mul_opp_opp. assert (Z.mul (Z.opp B) A = Z.mul A (Z.opp B)). apply Z.mul_comm. rewrite H; clear H.
  repeat rewrite Z.mul_opp_r. repeat (rewrite Z.add_opp_r). omega.
  assert (Z.le Z0 (Z.mul (Z.sub A B) (Z.sub A B))). apply Z.square_nonneg. rewrite H in H0. omega. Qed.

(* This is trivialy true if the parity of negatives is odd *)
Lemma Cauchy_Schwarz_helper': forall (A B C D : Z),
  Z.le (Z.add (Z.mul (Z.mul (Z.mul A B) C) D) (Z.mul (Z.mul (Z.mul A B) C) D))
  (Z.add (Z.mul (Z.mul (Z.mul A A) D) D) (Z.mul (Z.mul (Z.mul B B) C) C)).
Proof.
  intros. assert (forall (A B C D : Z), Z.mul (Z.mul (Z.mul A B) C) D = Z.mul (Z.mul A D) (Z.mul B C)).
  intros. assert (Z.mul B0 C0 = Z.mul C0 B0). apply Z.mul_comm. rewrite H.
  rewrite <- Z.mul_assoc. rewrite <- Z.mul_assoc. assert (Z.mul B0 (Z.mul C0 D0) = Z.mul (Z.mul C0 D0) B0). apply Z.mul_comm.
  rewrite H0. rewrite Z.mul_assoc. assert (Z.mul C0 D0 = Z.mul D0 C0). apply Z.mul_comm. rewrite H1.
  repeat rewrite Z.mul_assoc. reflexivity.
  repeat rewrite H. apply CSHH. Qed.

Lemma Cauchy_Schwarz_helper : forall {n : nat} (v1 v2 : Zvec n) (A B : Z),
  Z.le (Z.add (Z.mul (Z.mul A B) (Zvec_dot v1 v2)) (Z.mul (Z.mul A B) (Zvec_dot v1 v2)))
  (Z.add (Z.mul (Z.mul A A) (Zvec_normsq v2)) (Z.mul (Z.mul B B) (Zvec_normsq v1))).
Proof.
  intros n v1 v2. set (P := fun n (v1 v2 : Zvec n) => forall (A B : Z),
    Z.le (Z.add (Z.mul (Z.mul A B) (Zvec_dot v1 v2)) (Z.mul (Z.mul A B) (Zvec_dot v1 v2)))
    (Z.add (Z.mul (Z.mul A A) (Zvec_normsq v2)) (Z.mul (Z.mul B B) (Zvec_normsq v1)))). change (P n v1 v2).
  apply mutual_induction; unfold P; clear P; intros. unfold Zvec_normsq, Zvec_dot; simpl. omega.
  repeat (rewrite Zvec_dot_cons). repeat (rewrite Zvec_normsq_cons). repeat (rewrite Z.mul_add_distr_l).
  repeat (rewrite Z.add_assoc). repeat (rewrite Z.mul_assoc).
  assert (forall (A B C D : Z), Z.add (Z.add (Z.add A B) C) D  = Z.add (Z.add A C) (Z.add B D)). intros. omega.
  repeat (rewrite H0); clear H0. assert (H0 := Cauchy_Schwarz_helper' A B h1 h2). assert (H1 := H A B). omega.
Qed.

Lemma Cauchy_Schwarz_inequality : forall {n : nat} (v1 v2 : Zvec n),
  Z.le (Z.mul (Zvec_dot v1 v2) (Zvec_dot v1 v2)) (Z.mul (Zvec_normsq v1) (Zvec_normsq v2)).
Proof.
  intros. set (P := fun n (v1 v2 : Zvec n) => Z.le (Z.mul (Zvec_dot v1 v2) (Zvec_dot v1 v2)) (Z.mul (Zvec_normsq v1) (Zvec_normsq v2))).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros. reflexivity.
  repeat (rewrite Zvec_dot_cons). repeat (rewrite Zvec_normsq_cons). repeat (rewrite Zfoil).
  assert (Z.mul (Z.mul h1 h2) (Z.mul h1 h2) = Z.mul (Z.mul (Z.mul h1 h1) h2) h2). rewrite <- Z.mul_assoc.
  assert (Z.mul h2 (Z.mul h1 h2) = Z.mul (Z.mul h1 h2) h2). apply Z.mul_comm. rewrite H0; clear H0.
  repeat (rewrite Z.mul_assoc). reflexivity. rewrite H0; clear H0. repeat (rewrite Z.mul_assoc).
  assert (Z.mul (Z.mul (Zvec_dot t1 t2) h1) h2 = Z.mul (Z.mul h1 h2) (Zvec_dot t1 t2)). rewrite Z.mul_comm.
  rewrite Z.mul_assoc. rewrite Z.mul_comm. apply Z.mul_assoc. rewrite H0; clear H0.
  assert (Z.mul (Z.mul (Zvec_normsq t1) h2) h2 = Z.mul (Z.mul h2 h2) (Zvec_normsq t1)). rewrite Z.mul_comm.
  rewrite Z.mul_assoc. rewrite Z.mul_comm. apply Z.mul_assoc. rewrite H0; clear H0.
  assert (forall (A B C D : Z), Z.add (Z.add (Z.add A B) C) D = Z.add A (Z.add (Z.add B C) D)). intros. omega.
  repeat (rewrite H0); clear H0. assert (H0 := Cauchy_Schwarz_helper t1 t2 h1 h2). omega. Qed.