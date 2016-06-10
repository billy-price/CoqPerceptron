Require Import Coq.Vectors.Vector.
Require Import QArith.

(*******************************************************************************************
    Helpful definitions and proofs about Rationals (Q)
 *******************************************************************************************)
Definition Qge_bool (a b : Q) : bool := Qle_bool b a.
Definition Qlt_bool (a b : Q) : bool := andb (Qle_bool a b) (negb (Qeq_bool a b)).
Definition Qgt_bool (a b : Q) : bool := Qlt_bool b a.
Definition Qge (a b : Q) : Prop := Qle b a.
Definition Qgt (a b : Q) : Prop := Qlt b a.

Lemma Qsquare_nonneg : forall (a : Q),
 0 <= a * a.
Proof.
  intros a. unfold Qle. simpl. rewrite Zmult_1_r. apply Z.square_nonneg. Qed.

Lemma Qopp_mult_distr_l : forall (a b : Q),
  Qopp (a * b) == (Qopp a) * b.
Proof.
  intros. unfold Qmult. simpl. unfold Qeq. simpl.
  rewrite <- (Zopp_mult_distr_l (Qnum a) (Qnum b)). reflexivity.
Qed.

Lemma Qopp_mult_distr_r : forall (a b : Q),
  Qopp (a * b) == a * (Qopp b).
Proof.
  intros. unfold Qmult. simpl. unfold Qeq. simpl.
  rewrite <- (Zopp_mult_distr_r (Qnum a) (Qnum b)). reflexivity.
Qed.

Lemma Qplus_diag_eq_mult_2 : forall (a : Q),
  Qplus a a == Qmult (2#1) a.
Proof.
  intros. unfold Qeq, Qmult, Qplus. simpl.
  rewrite Zplus_diag_eq_mult_2. repeat rewrite <- Zmult_assoc.
  rewrite (Zmult_assoc _ 2 _). rewrite (Zmult_comm _ 2).
  repeat rewrite Zmult_assoc. rewrite (Zmult_comm _ 2).
  repeat rewrite <- Zmult_assoc. rewrite (Zmult_assoc 2 _ _).
  simpl. reflexivity. Qed.

Lemma Qplus_0_l_eq : forall (a : Q),
  Qplus 0 a = a.
Proof.
  intros. unfold Qplus. simpl. rewrite Z.mul_1_r.
  destruct a. simpl. reflexivity. Qed.

Lemma Qplus_0_r_eq : forall (a : Q),
  Qplus a 0 = a.
Proof.
  intros. unfold Qplus. simpl. rewrite Z.mul_1_r.
  rewrite Z.add_0_r. rewrite Pos.mul_1_r. destruct a.
  reflexivity. Qed.

Lemma Qmult_1_l_eq : forall (a : Q),
  Qmult 1 a = a.
Proof.
  intros. unfold Qmult. destruct a. simpl.
  destruct Qnum; reflexivity. Qed.

Lemma Qmult_1_r_eq : forall (a : Q),
  Qmult a 1 = a.
Proof.
  intros. unfold Qmult. destruct a. simpl.
  rewrite Z.mul_1_r. rewrite Pos.mul_1_r. reflexivity. Qed.

(*****************************************************************************************
    Definitions and Fixpoints for operations on Qvecs
    (Also includes Fixpoints/Computation on Training Data: list ((Qvec n)*bool))
 *****************************************************************************************)

Definition Qvec := Vector.t Q.
Definition Qvec_plus {n:nat} (v1 v2 : Qvec n) := map2 Qplus v1 v2.
Definition Qvec_dot {n:nat} (v1 v2 : Qvec n) := fold_left Qplus 0 (map2 Qmult v1 v2).
Definition Qvec_normsq {n:nat} (v1 : Qvec n) := Qvec_dot v1 v1.
Definition Qvec_zero (n : nat) : Qvec n := const 0 n.

Definition class (i : Q) : bool := Qle_bool 0 i.
Definition correct_class (i : Q) (l : bool) : bool :=
  andb (Bool.eqb l (class i)) (negb (Qeq_bool i 0)).
Definition Qvec_mult_class {n:nat} (l :bool) (f : Qvec n) :=
  if l then f else map (Qmult (-1%Z#1)) f.
Definition consb {n : nat} (v : Qvec n) := cons _ 1 _ v.

Inductive Qvec_Eq : forall {n : nat},(Qvec n)->(Qvec n)->Prop :=
| QNil : Qvec_Eq (nil Q) (nil Q)
| QCons: forall {n : nat} (v1 v2 : Qvec n) (h1 h2 : Q),
         Qvec_Eq v1 v2 -> h1 == h2 -> Qvec_Eq (cons Q h1 n v1) (cons Q h2 n v2).
Notation "a === b" := (Qvec_Eq a b) (at level 70).

Fixpoint Qvec_sum_class {n : nat} (w : Qvec (S n)) (M : list ((Qvec n)*bool)) : Qvec (S n) :=
  match M with
  | List.nil => w
  | List.cons (f, l) M' => Qvec_sum_class (Qvec_plus w (Qvec_mult_class l (consb f))) M'
  end.

Fixpoint Qvec_sum {n : nat} (M : list ((Qvec n)*bool)) : Qvec (S n) :=
  match M with
  | List.nil => Qvec_zero (S n)
  | List.cons (f, l) M' => Qvec_plus (Qvec_mult_class l (consb f)) (Qvec_sum M')
  end.

Fixpoint min_element_product {n : nat} (w : Qvec (S n)) (T: list ((Qvec n)*bool)) : Q :=
  match T with
  | List.nil => 1 (* avoid divide by zero *)
  | List.cons (f, l) List.nil => Qvec_dot w (Qvec_mult_class l (consb f))
  | List.cons (f, l) T' =>
      if (Qle_bool (Qvec_dot w (Qvec_mult_class l (consb f))) (min_element_product w T'))
      then (Qvec_dot w (Qvec_mult_class l (consb f)))
      else (min_element_product w T')
  end.

Fixpoint max_element_normsq {n : nat} (T: list ((Qvec n)*bool)) : Q :=
  match T with
  | List.nil => 1
  | List.cons (f, l) List.nil => (Qvec_normsq (consb f))
  | List.cons (f, l) T' =>
      if (Qge_bool (Qvec_normsq (consb f)) (max_element_normsq T'))
      then (Qvec_normsq (consb f))
      else (max_element_normsq T')
  end.

Fixpoint Qvec_sum_normsq {n:nat} (L: list ((Qvec n)*bool)) : Q :=
  match L with
  | List.nil => 0
  | List.cons (f, l) L' => Qplus (Qvec_normsq (consb f)) (Qvec_sum_normsq L')
  end.

Fixpoint Qvec_sum_dot {n:nat} (w : Qvec (S n)) (L: list ((Qvec n)*bool)) : Q :=
  match L with
  | List.nil => 0
  | List.cons (f, l) L' => Qplus (Qvec_dot w (Qvec_mult_class l (consb f))) (Qvec_sum_dot w L')
  end.

Fixpoint Qvec_foil {n:nat} (w : Qvec (S n)) (L: list ((Qvec n)*bool)) : Q :=
  match L with
  | List.nil => 0
  | List.cons (f, l) L' => Qplus (Qvec_dot w (Qvec_mult_class l (consb f)))
                                 (Qvec_foil (Qvec_plus w (Qvec_mult_class l (consb f))) L')
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
  |O => fun _ => True
  |S n => fun v => exists a, exists v0, v = cons A a n v0 end v' with
| nil => I
| cons a _ v0 => ex_intro _ a (ex_intro _ v0 (refl_equal _))
end.

Lemma mutual_induction : forall {A B: Type} (P : forall {n : nat}, t A n -> t B n -> Prop),
  (P (nil A) (nil B)) -> (forall (h1 : A) (h2 : B) {n : nat} (t1 : t A n) (t2 : t B n),
  (P t1 t2) -> (P (cons A h1 n t1) (cons B h2 n t2))) ->
  forall {n : nat} (v1 : t A n) (v2 : t B n), P v1 v2.
Proof.
  intros. induction n. rewrite (Vector_0_is_nil v1).
  rewrite (Vector_0_is_nil v2). apply H.
  assert (H1 := Vector_S_is_cons v1). assert (H2 := Vector_S_is_cons v2).
  destruct H1 as [a [v1' H1]]. destruct H2 as [b [v2' H2]]. rewrite H1.
  rewrite H2. apply H0. apply IHn. Qed.

Lemma triple_induction : forall {A B C: Type} (P : forall {n : nat}, t A n -> t B n -> t C n-> Prop),
  (P (nil A) (nil B) (nil C)) ->
  (forall (h1 : A) (h2 : B) (h3 : C) {n : nat} (t1 : t A n) (t2 : t B n) ( t3 : t C n),
  (P t1 t2 t3) -> (P (cons A h1 n t1) (cons B h2 n t2) (cons C h3 n t3))) ->
  forall {n : nat} (v1 : t A n) (v2 : t B n) (v3 : t C n), P v1 v2 v3.
Proof.
  intros. induction n. rewrite (Vector_0_is_nil v1). rewrite (Vector_0_is_nil v2).
  rewrite (Vector_0_is_nil v3). apply H. assert (H1 := Vector_S_is_cons v1).
  assert (H2 := Vector_S_is_cons v2). assert (H3 := Vector_S_is_cons v3).
  destruct H1 as [a [v1' H1]]. destruct H2 as [b [v2' H2]].
  destruct H3 as [c [v3' H3]]. rewrite H1. rewrite H2. rewrite H3.
  apply H0. apply IHn. Qed.

 (****************************************************************************************
    Proofs about Arithmetic on Qvec, Fixpoints/Computations on Qvecs / Training Data.
  ****************************************************************************************)
Lemma Qvec_Eq_refl : forall {n : nat} (v : Qvec n),
  v === v.
Proof.
  intros. induction v. apply QNil.
  apply (QCons _ _ _ _ IHv eq_refl). Qed.

Lemma Qvec_Eq_symm : forall {n : nat} (v1 v2 : Qvec n),
  v1 === v2 <-> v2 === v1.
Proof.
  intros. split.  set (P := fun {n : nat} (v1 v2 : Qvec n) => v1 === v2 -> v2 === v1).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros.
  apply QNil. inversion H0; subst. apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6. subst. apply H in H5.
  apply QCons. apply H5. symmetry. apply H7. apply eq_nat_dec. apply eq_nat_dec.
  set (P := fun {n : nat} (v1 v2 : Qvec n) => v2 === v1 -> v1 === v2).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros.
  apply QNil. inversion H0; subst. apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6. subst. apply H in H5. apply QCons.
  apply H5. symmetry. apply H7. apply eq_nat_dec. apply eq_nat_dec. Qed.

Lemma fold_left_add_unfold : forall {n : nat} (v1 v2 : Qvec n) (A : Q),
 (fold_left Qplus A (map2 Qmult v1 v2)) == (Qplus A (fold_left Qplus 0 (map2 Qmult v1 v2))).
Proof.
  intros n v1 v2. set (P := fun {n : nat} (v1 v2 : Qvec n) => forall A : Q,
  Qeq (fold_left Qplus A (map2 Qmult v1 v2)) (Qplus A (fold_left Qplus 0 (map2 Qmult v1 v2)))).
  change (P n v1 v2). apply mutual_induction; unfold P; intros; clear P.
  simpl. symmetry. apply Qplus_0_r.
  simpl. rewrite (H (A + h1 * h2)). rewrite (H (0 + h1*h2)). rewrite Qplus_0_l.
  rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_consb_gt_0 : forall {n : nat} (f : Qvec n),
 Qgt (Qvec_normsq (consb f)) 0.
Proof.
  intros n f. unfold Qvec_normsq. unfold Qvec_dot. unfold consb. simpl.
  unfold Qgt. rewrite fold_left_add_unfold. rewrite Qmult_1_r. rewrite Qplus_0_l.
  induction f; simpl.
  { reflexivity. }
  rewrite fold_left_add_unfold. rewrite Qplus_0_l. rewrite (Qplus_comm (h*h) _).
  rewrite Qplus_assoc. apply (Qplus_lt_le_compat 0 _ 0 (h * h) IHf).
  apply Qsquare_nonneg. Qed.

Lemma Qvec_normsq_nonneg : forall {n : nat} (f : Qvec n),
 0 <= (Qvec_normsq f).
Proof.
  intros. induction f; unfold Qvec_normsq, Qvec_dot. unfold Qle. reflexivity.
  simpl. rewrite fold_left_add_unfold. fold (Qvec_dot f f). fold (Qvec_normsq f).
  rewrite Qplus_0_l. SearchAbout Qle.
  apply (Qplus_le_compat 0 (h*h) 0 _ (Qsquare_nonneg h) IHf). Qed.

Lemma Qvec_sum_normsq_nonneg : forall {n : nat} (L : list ((Qvec n)*bool)),
  0 <= (Qvec_sum_normsq L).
Proof.
  intros. induction L. unfold Qle. reflexivity.
  destruct a as [f l]. simpl. assert (H := Qvec_normsq_nonneg (consb f)).
  apply (Qplus_le_compat 0 _ 0 _ H IHL). Qed.

Lemma Qvec_normsq_Qvec_0 : forall (n : nat),
 Qvec_normsq (Qvec_zero n) == 0.
Proof.
  intros n. induction n; unfold Qvec_zero, Qvec_normsq, Qvec_dot. reflexivity.
  simpl. apply IHn. Qed.

Lemma normsq_mult_neg_1_same : forall {n : nat} (f : Qvec n),
  Qvec_normsq f == Qvec_normsq (map (Qmult (-1#1)) f).
Proof.
  intros. induction f. simpl. reflexivity.
  unfold Qvec_normsq, Qvec_dot. simpl. rewrite fold_left_add_unfold.
  rewrite (fold_left_add_unfold _ _ (0 + _)). fold (Qvec_dot f f). fold (Qvec_normsq f).
  fold (Qvec_dot (map (Qmult (-1#1)) f) (map (Qmult (-1#1)) f)).
  fold (Qvec_normsq (map (Qmult (-1#1)) f)). repeat rewrite Qplus_0_l.
  assert (Qopp 1 = (-1#1)). reflexivity. repeat rewrite <- H.
  rewrite <- Qopp_mult_distr_l. repeat rewrite Qmult_1_l.
  rewrite <- Qopp_mult_distr_l. rewrite <- Qopp_mult_distr_r. rewrite Qopp_involutive.
  rewrite IHf. rewrite <- H. reflexivity. Qed.

Lemma Qvec_dot_mult_neg_1 : forall {n:nat} (v1 v2 : Qvec n),
  Qvec_dot v1 (map (Qmult (-1#1)) v2) == Qmult (-1#1) (Qvec_dot v1 v2).
Proof.
  intros n v1 v2. set (P := fun (n : nat) (v1 v2 : t Q n) =>
  Qvec_dot v1 (map (Qmult (-1#1)) v2) == Qmult (-1#1) (Qvec_dot v1 v2)).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P.
  { unfold Qvec_dot. simpl. rewrite Qmult_0_r. reflexivity. }
  intros. unfold Qvec_dot. simpl. rewrite fold_left_add_unfold.
  rewrite (fold_left_add_unfold t1 t2 _). fold (Qvec_dot t1 t2). rewrite Qplus_0_l.
  rewrite Qplus_0_l. assert (-1#1 = Qopp 1). reflexivity. rewrite H0.
  rewrite <- Qopp_mult_distr_l. rewrite <- Qopp_mult_distr_r. rewrite Qmult_1_l.
  rewrite <- Qopp_mult_distr_l. rewrite Qmult_1_l. rewrite Qopp_plus.
  rewrite H0 in H. rewrite <- Qopp_mult_distr_l in H. rewrite Qmult_1_l in H.
  rewrite <- H. unfold Qvec_dot. reflexivity. Qed.

Lemma Qvec_dot_add_sub_mult_eq : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_dot v1 v2 == Qminus (Qvec_dot (Qvec_plus v1 v3) v2) (Qvec_dot v3 v2).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Qvec n) => Qvec_dot v1 v2 ==
  Qminus (Qvec_dot (Qvec_plus v1 v3) v2) (Qvec_dot v3 v2)). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros; unfold Qvec_dot.
  { reflexivity. }
  simpl. rewrite fold_left_add_unfold. fold (Qvec_dot t1 t2). rewrite Qplus_0_l.
  rewrite fold_left_add_unfold. fold (Qvec_dot (Qvec_plus t1 t3) t2).
  rewrite Qplus_0_l. rewrite fold_left_add_unfold. fold (Qvec_dot t3 t2).
  rewrite Qplus_0_l. unfold Qminus. rewrite Qopp_plus.
  rewrite <- Qplus_assoc. rewrite (Qplus_comm (Qopp _) (Qopp _)).
  rewrite (Qplus_assoc (Qvec_dot _ _) (Qopp _) (Qopp _)).
  rewrite (Qplus_comm (Qplus _ _) (Qopp _)).
  fold (Qminus (Qvec_dot (Qvec_plus t1 t3) t2) (Qvec_dot t3 t2)).
  rewrite <- H. rewrite Qplus_assoc. rewrite Qmult_plus_distr_l.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc (h3 * h2) _ _).
  rewrite Qplus_opp_r. rewrite Qplus_0_l. reflexivity. Qed.

Lemma Qvec_normsq_cons : forall {n : nat} (h : Q) (t : Qvec n),
  Qvec_normsq (cons Q h n t) == Qplus (Qmult h h) (Qvec_normsq t).
Proof.
  intros. unfold Qvec_normsq, Qvec_dot. simpl. rewrite fold_left_add_unfold.
  rewrite Qplus_0_l. reflexivity. Qed.

Lemma Qvec_dot_cons : forall {n : nat} (h1 h2 : Q) (t1 t2 : Qvec n),
  Qvec_dot (cons Q h1 n t1) (cons Q h2 n t2) == Qplus (Qmult h1 h2) (Qvec_dot t1 t2).
Proof.
  intros. unfold Qvec_dot. simpl. rewrite fold_left_add_unfold.
  rewrite Qplus_0_l. reflexivity. Qed.

Lemma Qvec_normsq_plus : forall {n: nat} (v1 v2 : Qvec n),
  Qvec_normsq (Qvec_plus v1 v2) == Qplus (Qplus (Qvec_normsq v1) (Qmult (2#1) (Qvec_dot v1 v2))) (Qvec_normsq v2).
Proof.
  intros.  set (P := fun {n} (v1 v2 : Qvec n) => Qvec_normsq (Qvec_plus v1 v2) ==
  Qplus (Qplus (Qvec_normsq v1) (Qmult (2#1) (Qvec_dot v1 v2))) (Qvec_normsq v2)).
  change (P n v1 v2). apply mutual_induction; unfold P; intros. reflexivity.
  unfold Qvec_plus. simpl. repeat rewrite Qvec_normsq_cons. rewrite Qvec_dot_cons.
  fold (Qvec_plus t1 t2). rewrite (Qmult_plus_distr_r (2#1) _ _).
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc _ (h2*h2) _). rewrite (Qplus_comm _ (h2*h2)).
  rewrite (Qplus_assoc _ ((2#1)*(h1*h2)) _). rewrite (Qplus_comm (Qvec_normsq t1) _).
  rewrite <- Qplus_assoc. repeat rewrite (Qplus_assoc (Qvec_normsq t1) _ _).
  rewrite (Qplus_comm (Qvec_normsq t1)). repeat rewrite <- Qplus_assoc.
  rewrite (Qplus_assoc (Qvec_normsq t1) _ _). rewrite <- H.
  repeat rewrite Qplus_assoc. rewrite Qmult_plus_distr_l. repeat rewrite Qmult_plus_distr_r.
  rewrite (Qmult_comm h2 h1). rewrite <- Qplus_diag_eq_mult_2.
  repeat rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_dot_Qvec_zero_l : forall {n : nat} (v : Qvec n),
  Qvec_dot (Qvec_zero n) v == 0.
Proof.
  intros. induction v; unfold Qvec_dot. reflexivity.
  simpl. rewrite fold_left_add_unfold. rewrite Qplus_0_l.
  rewrite Qmult_0_l. rewrite Qplus_0_l. apply IHv. Qed.

Lemma Qvec_dot_Qvec_zero_r : forall {n : nat} (v : Qvec n),
  Qvec_dot v (Qvec_zero n) == 0.
Proof.
  intros. induction v; unfold Qvec_dot. reflexivity.
  simpl. rewrite fold_left_add_unfold. rewrite Qplus_0_l.
  rewrite Qmult_0_r. rewrite Qplus_0_l. apply IHv. Qed.

Lemma Qvec_plus_Qvec_zero : forall {n : nat} (v : Qvec n),
  Qvec_plus (Qvec_zero n) v = v.
Proof.
  intros. induction v; unfold Qvec_plus. reflexivity.
  simpl. fold (Qvec_zero n). fold (Qvec_plus (Qvec_zero n) v).
  rewrite IHv. rewrite Qplus_0_l_eq. reflexivity. Qed.

Lemma Qvec_plus_Qvec_zero_r : forall {n : nat} (v : Qvec n),
  Qvec_plus v (Qvec_zero n) = v.
Proof.
  intros. induction v; unfold Qvec_plus. reflexivity.
  simpl. fold (Qvec_zero n). fold (Qvec_plus v (Qvec_zero n)).
  rewrite IHv. rewrite Qplus_0_r_eq. reflexivity. Qed.

Lemma Qvec_dot_dist_l : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_dot (Qvec_plus v1 v2) v3 == Qplus (Qvec_dot v1 v3) (Qvec_dot v2 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Qvec n) =>
  Qvec_dot (Qvec_plus v1 v2) v3 == Qplus (Qvec_dot v1 v3) (Qvec_dot v2 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; intros. reflexivity.
  simpl. repeat rewrite Qvec_dot_cons. rewrite H. rewrite Qmult_plus_distr_l.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc (Qvec_dot t1 t3) _ _).
  rewrite (Qplus_comm (Qvec_dot t1 t3) (h2*h3)). repeat rewrite Qplus_assoc.
  reflexivity. Qed.

Lemma Qvec_dot_dist_r : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_dot v1 (Qvec_plus v2 v3) == Qplus (Qvec_dot v1 v2) (Qvec_dot v1 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Qvec n) =>
  Qvec_dot v1 (Qvec_plus v2 v3) == Qplus (Qvec_dot v1 v2) (Qvec_dot v1 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. repeat rewrite Qvec_dot_cons. rewrite Qmult_plus_distr_r. rewrite H.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc (Qvec_dot t1 t2) _ _).
  rewrite (Qplus_comm (Qvec_dot t1 t2) (h1*h3)). repeat rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_plus_shuffle : forall {n: nat} (v1 v2 v3 : Qvec n),
  Qvec_plus (Qvec_plus v1 v2) v3 === Qvec_plus (Qvec_plus v1 v3) v2.
Proof.
  intros. set (P := fun n (v1 v2 v3 : Qvec n) => 
  Qvec_plus (Qvec_plus v1 v2) v3 === Qvec_plus (Qvec_plus v1 v3) v2). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros; simpl. apply QNil.
  apply QCons. apply H. rewrite <- Qplus_assoc. rewrite (Qplus_comm h2 h3).
  apply Qplus_assoc. Qed.

Lemma Qvec_plus_comm : forall {n : nat} (v1 v2 : Qvec n),
  Qvec_plus v1 v2 === Qvec_plus v2 v1.
Proof.
  intros. set (P := fun {n : nat} (v1 v2 : Qvec n) => Qvec_plus v1 v2 === Qvec_plus v2 v1).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros; simpl. apply QNil.
  apply QCons. apply H. apply Qplus_comm. Qed.

(********************************************************************************************
                               Not yet changed to Qvec
 ********************************************************************************************)

Lemma Qvec_foil_w_0 : forall {n : nat} (v1 v2 : Qvec (S n)) (L : list ((Qvec n)*bool)),
  Qplus (Qvec_dot v1 (Qvec_sum L)) (Qvec_foil v2 L) == Qvec_foil (Qvec_plus v2 v1) L.
Proof.
  intros; generalize dependent v1; generalize dependent v2; induction L; intros.
  simpl. rewrite Qvec_dot_Qvec_zero_r. reflexivity. destruct a as [f l].
  unfold Qvec_sum. fold (Qvec_sum L). unfold Qvec_foil.
  fold (Qvec_foil (Qvec_plus v2 (Qvec_mult_class l (consb f)))).
  fold (Qvec_foil (Qvec_plus (Qvec_plus v2 v1) (Qvec_mult_class l (consb f)))).
  rewrite Qvec_dot_dist_r. rewrite Qplus_assoc. assert (forall (A B C D : Q),
  Qplus (Qplus (Qplus A B) C) D == Qplus (Qplus A C) (Qplus B D)). intros.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc C B D). rewrite (Qplus_comm C B).
  repeat rewrite <- Qplus_assoc. reflexivity.
  rewrite H; clear H. rewrite IHL. rewrite <- Qvec_dot_dist_l.
  Admitted. (* Figure out how to use Qvec_eq in this proof *****
  rewrite Qvec_plus_shuffle. rewrite Zvec_plus_comm. reflexivity. Qed. *)

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
