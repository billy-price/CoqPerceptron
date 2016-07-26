Require Import Coq.Vectors.Vector.
Require Import QArith.
Require Import Setoid.

(*******************************************************************************************
    Helpful definitions and proofs about Rationals (Q)
 *******************************************************************************************)
Definition Qge_bool (a b : Q) : bool := Qle_bool b a.
Definition Qlt_bool (a b : Q) : bool := andb (Qle_bool a b) (negb (Qeq_bool a b)).
Definition Qgt_bool (a b : Q) : bool := Qlt_bool b a.

Lemma Qsquare_nonneg : forall (a : Q),
 0 <= a * a.
Proof.
  intros a. unfold Qle. simpl. rewrite Zmult_1_r. apply Z.square_nonneg. Qed.

Lemma Qsquare_gt_0 : forall (a : Q),
  (~a == 0) -> (a*a) > 0.
Proof.
  intros. destruct a. unfold Qlt. simpl. rewrite Z.mul_1_r. unfold Qeq in H.
  simpl in H. rewrite Z.mul_1_r in H. destruct Qnum. exfalso. apply H. reflexivity.
  apply Z.mul_pos_pos; reflexivity. apply Z.mul_neg_neg; reflexivity. Qed.

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

Lemma Qle_neq_lt : forall (a b : Q),
  a <= b -> ~ a == b -> a < b.
Proof.
  intros. apply Qle_lteq in H. inversion H.
  apply H1. exfalso. apply H0. apply H1. Qed.

(*****************************************************************************************
    Definitions and Fixpoints for operations on Qvecs
    (Also includes Fixpoints/Computation on Training Data: list ((Qvec n)*bool))
 *****************************************************************************************)

(** Hacking this to avoid changing everything. Always normalize/reduce after plus and mult **)
Definition Qplus (a b : Q) : Q := Qred (Qplus a b).
Infix "+" := Qplus : Q_scope.
Definition Qmult (a b : Q) : Q := Qred (Qmult a b).
Infix "*" := Qmult : Q_scope.

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
| nil _ => eq_refl
end.

Definition Vector_S_is_cons {A} {n} (v: t A (S n)) : exists a, exists v0, v = cons A a n v0 :=
match v as v' in t _ n1
  return match n1 return t A n1 -> Prop with
  |O => fun _ => True
  |S n => fun v => exists a, exists v0, v = cons A a n v0 end v' with
| nil _ => I
| cons _ a _ v0 => ex_intro _ a (ex_intro _ v0 (refl_equal _))
end.

Lemma Vector_S_is_cons' : forall {A : Type} {n : nat} (v : t A (S n)),
  v = cons A (hd v) n (tl v).
Proof.
  intros. assert (H := Vector_S_is_cons v). destruct H as [a [v' H]].
  rewrite H. simpl. reflexivity. Qed.

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

(*****************************************************************************************
                     Qvec_Eq. Rational Equality of Qvecs.
 *****************************************************************************************)
Inductive Qvec_Eq : forall {n : nat},(Qvec n)->(Qvec n)->Prop :=
| QNil : Qvec_Eq (nil Q) (nil Q)
| QCons: forall {n : nat} (v1 v2 : Qvec n) (h1 h2 : Q),
         Qvec_Eq v1 v2 -> h1 == h2 -> Qvec_Eq (cons Q h1 n v1) (cons Q h2 n v2).
Notation "a === b" := (Qvec_Eq a b) (at level 70).

Lemma Qvec_Eq_refl : forall {n : nat} (v : Qvec n),
  v === v.
Proof.
  intros. induction v. apply QNil.
  apply (QCons _ _ _ _ IHv eq_refl). Qed.

Lemma Qvec_Eq_symm : forall {n : nat} (v1 v2 : Qvec n),
  v1 === v2 -> v2 === v1.
Proof.
  intros n v1 v2. set (P := fun {n : nat} (v1 v2 : Qvec n) => v1 === v2 -> v2 === v1).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros.
  apply QNil. inversion H0; subst. apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6. subst. apply H in H5.
  apply QCons. apply H5. symmetry. apply H7. apply eq_nat_dec. apply eq_nat_dec. Qed.

Lemma Qvec_Eq_trans : forall {n : nat} (v1 v2 v3 : Qvec n),
  v1 === v2 -> v2 === v3 -> v1 === v3.
Proof.
  intros n v1 v2 v3. set (P := fun {n : nat} (v1 v2 v3 : Qvec n) =>
    v1 === v2 -> v2 === v3 -> v1 === v3). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros; simpl. apply QNil.
  inversion H0; subst. apply Eqdep_dec.inj_pair2_eq_dec in H4.
  apply Eqdep_dec.inj_pair2_eq_dec in H7. subst. inversion H1; subst.
  apply Eqdep_dec.inj_pair2_eq_dec in H4. apply Eqdep_dec.inj_pair2_eq_dec in H9.
  subst. apply QCons. apply H in H6. apply H6. apply H7.
  apply (Qeq_trans h1 h2 h3 H8 H10). apply eq_nat_dec. apply eq_nat_dec.
  apply eq_nat_dec. apply eq_nat_dec. Qed.

Instance Qvec_Setoid : forall {n : nat},
  Equivalence (Qvec_Eq (n := n)).
Proof.
  intros. split; red. apply Qvec_Eq_refl.
  apply Qvec_Eq_symm. apply Qvec_Eq_trans. Qed.

Theorem Qvec_Eq_dec : forall {n : nat} (v1 v2 : Qvec n),
  {v1 === v2} + {~ v1 === v2}.
Proof.
  intros. induction v1. rewrite (Vector_0_is_nil v2). left. apply QNil.
  assert (H := Vector_S_is_cons' v2). rewrite H. assert (H0 := IHv1 (tl v2)).
  inversion H0. assert (H2 := Qeq_dec h (hd v2)). inversion H2.
  left. apply (QCons _ _ _ _ H1 H3). right. unfold not. intros.
  apply H3. inversion H4. apply H11. right. unfold not. intros.
  apply H1. inversion H2. apply Eqdep_dec.inj_pair2_eq_dec in H5. rewrite <- H5.
  apply Eqdep_dec.inj_pair2_eq_dec in H8. rewrite <- H8. apply H7.
  apply eq_nat_dec. apply eq_nat_dec. Qed.

Theorem Qvec_not_eq_symm : forall {n : nat} (v1 v2 : Qvec n),
  ~ v1 === v2 -> ~ v2 === v1.
Proof.
  intros. unfold not. intros. apply H. apply (Qvec_Eq_symm _ _ H0). Qed.

(***************** Setoid Compatibility Results *****************)
Instance Qvec_plus_comp : forall {n : nat},
  Proper (Qvec_Eq==>Qvec_Eq==>Qvec_Eq) (Qvec_plus (n := n)).
Proof.
  intros. unfold Proper; unfold respectful. induction n; intros.
  rewrite(Vector_0_is_nil x). rewrite (Vector_0_is_nil x0).
  rewrite(Vector_0_is_nil y). rewrite (Vector_0_is_nil y0). reflexivity.
  assert (Hx := Vector_S_is_cons x). assert (Hx0 := Vector_S_is_cons x0).
  assert (Hy := Vector_S_is_cons y). assert (Hy0 := Vector_S_is_cons y0).
  destruct Hx as [hx [x' Hx]]. destruct Hx0 as [hx0 [x0' Hx0]].
  destruct Hy as [hy [y' Hy]]. destruct Hy0 as [hy0 [y0' Hy0]]. subst.
  inversion H0. inversion H. subst. apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6. apply Eqdep_dec.inj_pair2_eq_dec in H10.
  apply Eqdep_dec.inj_pair2_eq_dec in H13. subst. assert (HH := IHn _ _ H12 _ _ H5).
  simpl. apply QCons. apply HH. rewrite H14. rewrite H7. reflexivity.
  apply eq_nat_dec. apply eq_nat_dec. apply eq_nat_dec. apply eq_nat_dec. Qed.

Lemma fold_left_add_unfold : forall {n : nat} (v1 v2 : Qvec n) (A : Q),
 (fold_left Qplus A (map2 Qmult v1 v2)) == (Qplus A (fold_left Qplus 0 (map2 Qmult v1 v2))).
Proof.
  intros n v1 v2. set (P := fun {n : nat} (v1 v2 : Qvec n) => forall A : Q,
  Qeq (fold_left Qplus A (map2 Qmult v1 v2)) (Qplus A (fold_left Qplus 0 (map2 Qmult v1 v2)))).
  change (P n v1 v2). apply mutual_induction; unfold P; intros; clear P.
  simpl. unfold Qplus; rewrite Qplus_0_r. symmetry. apply Qred_correct.
  simpl. rewrite (H (A + h1 * h2)). rewrite (H (0 + h1*h2)).
  unfold Qplus. rewrite Qplus_0_l. repeat rewrite Qred_correct. rewrite Qplus_assoc.
  reflexivity. Qed.

Instance Qvec_dot_comp : forall {n : nat},
  Proper (Qvec_Eq==>Qvec_Eq==>Qeq) (Qvec_dot (n := n)).
Proof.
  intros. unfold Proper, respectful; intros. induction n.
  rewrite (Vector_0_is_nil x). rewrite (Vector_0_is_nil x0).
  rewrite (Vector_0_is_nil y). rewrite (Vector_0_is_nil y0). reflexivity.
  assert (Hx := Vector_S_is_cons x). assert (Hx0 := Vector_S_is_cons x0).
  assert (Hy := Vector_S_is_cons y). assert (Hy0 := Vector_S_is_cons y0).
  destruct Hx as [hx [x' Hx]]. destruct Hx0 as [hx0 [x0' Hx0]].
  destruct Hy as [hy [y' Hy]]. destruct Hy0 as [hy0 [y0' Hy0]]. subst.
  unfold Qvec_dot. simpl. rewrite fold_left_add_unfold. fold (Qvec_dot x' x0').
  rewrite fold_left_add_unfold. fold (Qvec_dot y' y0'). repeat rewrite Qplus_0_l.
  inversion H0. inversion H. subst. apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6. apply Eqdep_dec.inj_pair2_eq_dec in H10.
  apply Eqdep_dec.inj_pair2_eq_dec in H13. subst.
  assert (HH := IHn _ _ H12 _ _ H5). rewrite H7. rewrite H14. rewrite HH. reflexivity.
  apply eq_nat_dec. apply eq_nat_dec. apply eq_nat_dec. apply eq_nat_dec. Qed.

Instance Qvec_normsq_comp : forall {n : nat},
  Proper (Qvec_Eq==>Qeq) (Qvec_normsq (n := n)).
Proof.
  intros. unfold Proper, respectful, Qvec_normsq; intros.
  rewrite H. reflexivity. Qed.

Instance Qvec_mult_class_comp : forall {n : nat},
  Proper (eq==>Qvec_Eq==>Qvec_Eq) (Qvec_mult_class (n := n)).
Proof.
  intros. unfold Proper, respectful. intros x y Hxy v1 v2.
  set (P := fun {n : nat} (v1 v2 : Qvec n) => v1 === v2 ->
  Qvec_mult_class x v1 === Qvec_mult_class y v2). change (P n v1 v2). apply mutual_induction;
  unfold P; clear P; intros. rewrite Hxy. reflexivity. rewrite Hxy.
  inversion H0; subst. apply Eqdep_dec.inj_pair2_eq_dec in H3.
  apply Eqdep_dec.inj_pair2_eq_dec in H6. subst. apply H in H5. unfold Qvec_mult_class.
  destruct y. apply H0. simpl. simpl in H5. apply QCons. apply H5. rewrite H7. reflexivity.
  apply eq_nat_dec. apply eq_nat_dec. Qed.

Instance consb_comp : forall {n : nat},
  Proper (Qvec_Eq==>Qvec_Eq) (consb (n := n)).
Proof.
  intros. unfold Proper, respectful; intros. unfold consb.
  apply (QCons _ _ _ _ H eq_refl). Qed.

Instance Qvec_sum_class_comp : forall {n : nat},
  Proper (Qvec_Eq==>eq==>Qvec_Eq) (Qvec_sum_class (n := n)).
Proof.
  intros. unfold Proper, respectful; intros x y Hxy a L HL; subst.
  generalize dependent y. generalize dependent x. induction L; intros.
  simpl. apply Hxy. destruct a as [f l]. simpl.
  assert (H := Qvec_Eq_refl (Qvec_mult_class l (consb f))).
  apply (Qvec_plus_comp x y Hxy) in H. apply (IHL _ _ H). Qed.

Instance min_element_product_comp : forall {n : nat},
  Proper (Qvec_Eq==>eq==>Qeq) (min_element_product (n := n)).
Proof.
  intros. unfold Proper, respectful; intros x y Hxy a L HL; subst.
  generalize dependent y. generalize dependent x. induction L; intros.
  reflexivity. destruct a as [f l]. destruct L. simpl. rewrite Hxy.
  reflexivity. unfold min_element_product. fold (min_element_product y (p :: L)).
  fold (min_element_product x (p :: L)). assert (IHxy := IHL _ _ Hxy).
  repeat rewrite IHxy. repeat rewrite Hxy.
  destruct (Qle_bool (Qvec_dot y (Qvec_mult_class l (consb f))) (min_element_product y (p :: L))).
  rewrite Hxy. reflexivity. apply IHxy. Qed.

Instance Qvec_sum_dot_comp : forall {n : nat},
  Proper (Qvec_Eq==>eq==>Qeq) (Qvec_sum_dot (n := n)).
Proof.
  intros. unfold Proper, respectful; intros x y Hxy a L HL; subst; induction L; intros.
  reflexivity. destruct a as [f l]. simpl. rewrite IHL. rewrite Hxy. reflexivity. Qed.

Instance Qvec_foil_comp : forall {n : nat},
  Proper (Qvec_Eq==>eq==>Qeq) (Qvec_foil (n := n)).
Proof.
  intros. unfold Proper, respectful. intros x y H l L HL; subst. generalize dependent y.
  generalize dependent x. induction L; intros. reflexivity. destruct a as [f l].
  simpl. assert (H0 := Qvec_Eq_refl (Qvec_mult_class l (consb f))).
  apply (Qvec_plus_comp x y H) in H0. apply IHL in H0. rewrite H0.
  rewrite H. reflexivity. Qed.

(****************************************************************************************
    Proofs about Arithmetic on Qvec, Fixpoints/Computations on Qvecs / Training Data.
 ****************************************************************************************)
Lemma Qvec_normsq_nonneg : forall {n : nat} (f : Qvec n),
 0 <= (Qvec_normsq f).
Proof.
  intros. induction f; unfold Qvec_normsq, Qvec_dot. unfold Qle. reflexivity.
  simpl. rewrite fold_left_add_unfold. fold (Qvec_dot f f). fold (Qvec_normsq f).
  unfold Qplus, Qmult; repeat rewrite Qred_correct. rewrite Qplus_0_l.
  apply (Qplus_le_compat 0 _ 0). apply Qsquare_nonneg. apply IHf. Qed.

Lemma Qvec_consb_gt_0 : forall {n : nat} (f : Qvec n),
 Qvec_normsq (consb f) > 0.
Proof.
  intros n f. unfold Qvec_normsq. unfold Qvec_dot. unfold consb. simpl.
  rewrite fold_left_add_unfold. assert (0 + 1 * 1 == 1). unfold Qmult, Qplus;
  rewrite Qred_correct. simpl. apply Qplus_0_l. rewrite H; clear H.
  fold (Qvec_dot f f). fold (Qvec_normsq f). rewrite <- Qplus_0_r.
  unfold Qplus; rewrite Qred_correct. apply (Qplus_lt_le_compat 0 _ 0). reflexivity.
  apply Qvec_normsq_nonneg. Qed.

Lemma Qvec_sum_normsq_nonneg : forall {n : nat} (L : list ((Qvec n)*bool)),
  0 <= (Qvec_sum_normsq L).
Proof.
  intros. induction L. unfold Qle. reflexivity.
  destruct a as [f l]. simpl. assert (H := Qvec_normsq_nonneg (consb f)).
  unfold Qplus; rewrite Qred_correct. apply (Qplus_le_compat 0 _ 0 _ H IHL). Qed.

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
  unfold Qmult, Qplus; repeat rewrite Qred_correct.
  rewrite <- Qopp_mult_distr_l. repeat rewrite Qmult_1_l.
  rewrite <- Qopp_mult_distr_l. rewrite <- Qopp_mult_distr_r. rewrite Qopp_involutive.
  rewrite IHf. rewrite <- H. reflexivity. Qed.

Lemma Qvec_dot_mult_neg_1 : forall {n:nat} (v1 v2 : Qvec n),
  Qvec_dot v1 (map (Qmult (-1#1)) v2) == Qmult (-1#1) (Qvec_dot v1 v2).
Proof.
  intros n v1 v2. set (P := fun (n : nat) (v1 v2 : t Q n) =>
  Qvec_dot v1 (map (Qmult (-1#1)) v2) == Qmult (-1#1) (Qvec_dot v1 v2)).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P.
  { unfold Qvec_dot, Qmult, Qplus. simpl. reflexivity. }
  intros. unfold Qvec_dot. simpl. rewrite fold_left_add_unfold.
  rewrite (fold_left_add_unfold t1 t2 _). fold (Qvec_dot t1 t2).
  unfold Qplus, Qmult; repeat rewrite Qred_correct. rewrite Qplus_0_l.
  rewrite Qplus_0_l. assert (-1#1 = Qopp 1). reflexivity. rewrite H0.
  rewrite <- Qopp_mult_distr_l. rewrite <- Qopp_mult_distr_r. rewrite Qmult_1_l.
  rewrite <- Qopp_mult_distr_l. rewrite Qmult_1_l. rewrite Qopp_plus.
  rewrite H0 in H. unfold Qmult, Qplus in H. repeat rewrite Qred_correct in H.
  rewrite <- Qopp_mult_distr_l in H. rewrite Qmult_1_l in H.
  rewrite <- H. unfold Qvec_dot. reflexivity. Qed.

Lemma Qvec_dot_add_sub_mult_eq : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_dot v1 v2 == Qminus (Qvec_dot (Qvec_plus v1 v3) v2) (Qvec_dot v3 v2).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Qvec n) => Qvec_dot v1 v2 ==
  Qminus (Qvec_dot (Qvec_plus v1 v3) v2) (Qvec_dot v3 v2)). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros; unfold Qvec_dot.
  { reflexivity. }
  simpl. rewrite fold_left_add_unfold. fold (Qvec_dot t1 t2).
  unfold Qplus, Qmult; repeat rewrite Qred_correct. rewrite Qplus_0_l.
  rewrite fold_left_add_unfold. fold (Qvec_dot (Qvec_plus t1 t3) t2).
  rewrite Qplus_0_l. rewrite fold_left_add_unfold. fold (Qvec_dot t3 t2).
  rewrite Qplus_0_l. unfold Qminus, Qplus. repeat rewrite Qred_correct.
  rewrite Qopp_plus. rewrite <- Qplus_assoc. rewrite (Qplus_comm (Qopp _) (Qopp _)).
  rewrite (Qplus_assoc (Qvec_dot _ _) (Qopp _) (Qopp _)).
  rewrite (Qplus_comm (_ _ _) (Qopp _)).
  fold (Qminus (Qvec_dot (Qvec_plus t1 t3) t2) (Qvec_dot t3 t2)).
  rewrite <- H. rewrite Qplus_assoc. rewrite Qmult_plus_distr_l.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc (_ h3 h2) _ _).
  rewrite Qplus_opp_r. rewrite Qplus_0_l. reflexivity. Qed.

Lemma Qvec_normsq_cons : forall {n : nat} (h : Q) (t : Qvec n),
  Qvec_normsq (cons Q h n t) == Qplus (Qmult h h) (Qvec_normsq t).
Proof.
  intros. unfold Qvec_normsq, Qvec_dot. simpl. rewrite fold_left_add_unfold.
  unfold Qplus, Qmult; repeat rewrite Qred_correct. rewrite Qplus_0_l. reflexivity. Qed.

Lemma Qvec_dot_cons : forall {n : nat} (h1 h2 : Q) (t1 t2 : Qvec n),
  Qvec_dot (cons Q h1 n t1) (cons Q h2 n t2) == Qplus (Qmult h1 h2) (Qvec_dot t1 t2).
Proof.
  intros. unfold Qvec_dot. simpl. rewrite fold_left_add_unfold.
  unfold Qplus, Qmult; repeat rewrite Qred_correct. rewrite Qplus_0_l. reflexivity. Qed.

Lemma Qvec_normsq_plus : forall {n: nat} (v1 v2 : Qvec n),
  Qvec_normsq (Qvec_plus v1 v2) == Qplus (Qplus (Qvec_normsq v1) (Qmult (2#1) (Qvec_dot v1 v2))) (Qvec_normsq v2).
Proof.
  intros.  set (P := fun {n} (v1 v2 : Qvec n) => Qvec_normsq (Qvec_plus v1 v2) ==
  Qplus (Qplus (Qvec_normsq v1) (Qmult (2#1) (Qvec_dot v1 v2))) (Qvec_normsq v2)).
  change (P n v1 v2). apply mutual_induction; unfold P; intros. reflexivity.
  unfold Qvec_plus. simpl. repeat rewrite Qvec_normsq_cons. rewrite Qvec_dot_cons.
  fold (Qvec_plus t1 t2). unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite (Qmult_plus_distr_r (2#1)). repeat rewrite <- Qplus_assoc.
  rewrite (Qplus_assoc _  _ (Qvec_normsq t2)). rewrite (Qplus_comm (_ (2#1) (Qvec_dot t1 t2))).
  rewrite (Qplus_assoc (Qvec_normsq t1)). rewrite (Qplus_comm (Qvec_normsq t1) _).
  rewrite <- Qplus_assoc. repeat rewrite (Qplus_assoc (Qvec_normsq t1) _ _).
  rewrite (Qplus_comm (Qvec_normsq t1)). repeat rewrite <- Qplus_assoc.
  rewrite (Qplus_assoc (Qvec_normsq t1) _ _). unfold Qplus, Qmult in H;
  repeat rewrite Qred_correct in H; rewrite <- H. repeat rewrite Qplus_assoc.
  rewrite Qmult_plus_distr_l. repeat rewrite Qmult_plus_distr_r.
  rewrite (Qmult_comm h2 h1). rewrite <- Qplus_diag_eq_mult_2.
  repeat rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_dot_Qvec_zero_l : forall {n : nat} (v : Qvec n),
  Qvec_dot (Qvec_zero n) v == 0.
Proof.
  intros. induction v; unfold Qvec_dot. reflexivity.
  simpl. rewrite fold_left_add_unfold. unfold Qplus, Qmult;
  repeat rewrite Qred_correct; rewrite Qplus_0_l.
  rewrite Qmult_0_l. rewrite Qplus_0_l. apply IHv. Qed.

Lemma Qvec_dot_Qvec_zero_r : forall {n : nat} (v : Qvec n),
  Qvec_dot v (Qvec_zero n) == 0.
Proof.
  intros. induction v; unfold Qvec_dot. reflexivity.
  simpl. rewrite fold_left_add_unfold. unfold Qplus, Qmult;
  repeat rewrite Qred_correct; rewrite Qplus_0_l.
  rewrite Qmult_0_r. rewrite Qplus_0_l. apply IHv. Qed.

Lemma Qvec_plus_Qvec_zero : forall {n : nat} (v : Qvec n),
  Qvec_plus (Qvec_zero n) v === v.
Proof.
  intros. induction v; unfold Qvec_plus. reflexivity.
  simpl. fold (Qvec_zero n). fold (Qvec_plus (Qvec_zero n) v).
  apply QCons. apply IHv. unfold Qplus; rewrite Qred_correct;
  apply Qplus_0_l. Qed.

Lemma Qvec_plus_Qvec_zero_r : forall {n : nat} (v : Qvec n),
  Qvec_plus v (Qvec_zero n) === v.
Proof.
  intros. induction v; unfold Qvec_plus. reflexivity.
  simpl. fold (Qvec_zero n). fold (Qvec_plus v (Qvec_zero n)).
  apply QCons. apply IHv. unfold Qplus; rewrite Qred_correct;
  apply Qplus_0_r. Qed.

Lemma Qvec_dot_dist_l : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_dot (Qvec_plus v1 v2) v3 == Qplus (Qvec_dot v1 v3) (Qvec_dot v2 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Qvec n) =>
  Qvec_dot (Qvec_plus v1 v2) v3 == Qplus (Qvec_dot v1 v3) (Qvec_dot v2 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; intros. reflexivity.
  simpl. repeat rewrite Qvec_dot_cons. rewrite H. unfold Qplus, Qmult;
  repeat rewrite Qred_correct; rewrite Qmult_plus_distr_l.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc (Qvec_dot t1 t3) _ _).
  rewrite (Qplus_comm (Qvec_dot t1 t3) (QArith_base.Qmult h2 h3)).
  repeat rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_dot_dist_r : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_dot v1 (Qvec_plus v2 v3) == Qplus (Qvec_dot v1 v2) (Qvec_dot v1 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Qvec n) =>
  Qvec_dot v1 (Qvec_plus v2 v3) == Qplus (Qvec_dot v1 v2) (Qvec_dot v1 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. repeat rewrite Qvec_dot_cons. rewrite H. unfold Qplus, Qmult; repeat rewrite Qred_correct;
  rewrite Qmult_plus_distr_r. repeat rewrite <- Qplus_assoc.
  rewrite (Qplus_assoc (Qvec_dot t1 t2) _ _). rewrite (Qplus_comm (Qvec_dot t1 t2)
  (QArith_base.Qmult h1 h3)). repeat rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_plus_shuffle : forall {n: nat} (v1 v2 v3 : Qvec n),
  Qvec_plus (Qvec_plus v1 v2) v3 === Qvec_plus (Qvec_plus v1 v3) v2.
Proof.
  intros. set (P := fun n (v1 v2 v3 : Qvec n) => 
  Qvec_plus (Qvec_plus v1 v2) v3 === Qvec_plus (Qvec_plus v1 v3) v2). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros; simpl. apply QNil.
  apply QCons. apply H. unfold Qplus; repeat rewrite Qred_correct;
  rewrite <- Qplus_assoc. rewrite (Qplus_comm h2 h3). apply Qplus_assoc. Qed.

Lemma Qvec_plus_comm : forall {n : nat} (v1 v2 : Qvec n),
  Qvec_plus v1 v2 === Qvec_plus v2 v1.
Proof.
  intros. set (P := fun {n : nat} (v1 v2 : Qvec n) => Qvec_plus v1 v2 === Qvec_plus v2 v1).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros; simpl. apply QNil.
  apply QCons. apply H. unfold Qplus. rewrite Qplus_comm. reflexivity. Qed.

Lemma Qvec_foil_w_0 : forall {n : nat} (v1 v2 : Qvec (S n)) (L : list ((Qvec n)*bool)),
  Qplus (Qvec_dot v1 (Qvec_sum L)) (Qvec_foil v2 L) == Qvec_foil (Qvec_plus v2 v1) L.
Proof.
  intros; generalize dependent v1; generalize dependent v2; induction L; intros.
  simpl. rewrite Qvec_dot_Qvec_zero_r. reflexivity. destruct a as [f l].
  unfold Qvec_sum. fold (Qvec_sum L). unfold Qvec_foil.
  fold (Qvec_foil (Qvec_plus v2 (Qvec_mult_class l (consb f)))).
  fold (Qvec_foil (Qvec_plus (Qvec_plus v2 v1) (Qvec_mult_class l (consb f)))).
  rewrite Qvec_dot_dist_r. unfold Qplus; repeat rewrite Qred_correct.
  rewrite Qplus_assoc. assert (forall (A B C D : Q),
  QArith_base.Qplus (QArith_base.Qplus (QArith_base.Qplus A B) C) D == 
  QArith_base.Qplus (QArith_base.Qplus A C) (QArith_base.Qplus B D)). intros.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc C B D). rewrite (Qplus_comm C B).
  repeat rewrite <- Qplus_assoc. reflexivity.
  rewrite H; clear H. assert (H := IHL (Qvec_plus v2 (Qvec_mult_class l (consb f))) v1).
  unfold Qplus in H; repeat rewrite Qred_correct in H. rewrite H.
  assert (H0 := Qvec_dot_dist_l v1 v2 (Qvec_mult_class l (consb f))).
  unfold Qplus in H0; rewrite Qred_correct in H0. rewrite <- H0.
  rewrite Qvec_plus_shuffle. rewrite Qvec_plus_comm. reflexivity. Qed.

Lemma Qvec_dot_sum_eq : forall {n : nat} (w : Qvec (S n)) (L : list ((Qvec n)*bool)),
  Qvec_dot w (Qvec_sum L) == Qvec_sum_dot w L.
Proof.
  intros. induction L. simpl.
  rewrite Qvec_dot_Qvec_zero_r. apply Qeq_refl.
  destruct a as [f l].
  simpl. rewrite Qvec_dot_dist_r. rewrite IHL. reflexivity. Qed.

Lemma Qvec_foil_0_w : forall {n : nat} (v1 v2 : Qvec (S n)) (L : list ((Qvec n)*bool)),
  Qvec_foil v1 L == Qminus (Qvec_foil (Qvec_plus v1 v2) L) (Qvec_sum_dot v2 L).
Proof.
  intros. assert (H := Qvec_foil_w_0 v2 v1 L). rewrite <- (Qplus_inj_r _ _ (Qvec_sum_dot v2 L)).
  unfold Qminus. rewrite <- Qplus_assoc. rewrite (Qplus_comm (Qopp _) _). rewrite Qplus_opp_r.
  rewrite Qplus_0_r. rewrite <- H. rewrite Qvec_dot_sum_eq. unfold Qplus; rewrite Qred_correct.
  apply Qplus_comm. Qed.

Lemma Qvec_normsq_eq_sum_normsq_foil : forall {n: nat} (L : list ((Qvec n)*bool)),
  Qvec_normsq (Qvec_sum L) == Qplus (Qvec_sum_normsq L) (Qmult (2#1) (Qvec_foil (Qvec_zero (S n)) L)).
Proof.
  intros. induction L. simpl. unfold Qplus, Qmult; rewrite Qred_correct.
  rewrite Qmult_0_r. rewrite Qplus_0_l. apply Qvec_normsq_Qvec_0.
  destruct a as [f l]. unfold Qvec_normsq, Qvec_sum. fold (Qvec_sum L).
  unfold Qvec_sum_normsq. fold (Qvec_sum_normsq L). unfold Qvec_foil.
  fold (Qvec_foil (Qvec_plus (Qvec_zero (S n)) (Qvec_mult_class l (consb f))) L).
  fold (Qvec_normsq (Qvec_plus (Qvec_mult_class l (consb f)) (Qvec_sum L))).
  rewrite Qvec_normsq_plus. assert (Qvec_normsq (Qvec_mult_class l (consb f)) == Qvec_normsq (consb f)).
  destruct l. reflexivity. unfold Qvec_mult_class. rewrite <- normsq_mult_neg_1_same. reflexivity.
  rewrite H; clear H. rewrite IHL. unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite <- Qplus_assoc. rewrite (Qplus_assoc (QArith_base.Qmult (2#1) _) (Qvec_sum_normsq L) _).
  rewrite (Qplus_comm (QArith_base.Qmult (2#1) _) (Qvec_sum_normsq L)). repeat rewrite <- Qplus_assoc.
  rewrite Qvec_dot_Qvec_zero_l. repeat rewrite Qplus_0_l. rewrite <- Qmult_plus_distr_r.
  assert (H := Qvec_foil_w_0 (Qvec_mult_class l (consb f)) (Qvec_zero (S n)) L).
  unfold Qplus in H; rewrite Qred_correct in H. rewrite H. reflexivity. Qed.

Lemma Qvec_plus_assoc : forall {n : nat} (v1 v2 v3 : Qvec n),
  Qvec_plus (Qvec_plus v1 v2) v3 === Qvec_plus v1 (Qvec_plus v2 v3).
Proof.
  intros. set (P := fun n (v1 v2 v3 : Qvec n) => 
  Qvec_plus (Qvec_plus v1 v2) v3 === Qvec_plus v1 (Qvec_plus v2 v3)). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. apply QCons. apply H. symmetry. unfold Qplus; repeat rewrite Qred_correct;
  apply Qplus_assoc. Qed.

Lemma Qvec_foil_append : forall {n : nat} (L1 L2 : list ((Qvec n)*bool)) (v : Qvec (S n)),
  Qvec_foil v (List.app L1 L2) == Qplus (Qvec_foil v L1) (Qvec_foil (Qvec_plus v (Qvec_sum L1)) L2).
Proof.
  intros n L1. induction L1; intros. simpl. rewrite Qvec_plus_Qvec_zero_r. symmetry.
  unfold Qplus; rewrite Qplus_0_l; apply Qred_correct.
  destruct a as [f l]. simpl. rewrite IHL1. rewrite Qvec_plus_assoc.
  unfold Qplus; repeat rewrite Qred_correct; rewrite Qplus_assoc. reflexivity. Qed.

Lemma Qvec_sum_sum_class : forall {n : nat} (w : Qvec (S n)) (L : list ((Qvec n)*bool)),
  Qvec_plus w (Qvec_sum L) === Qvec_sum_class w L.
Proof.
  intros. generalize dependent w; induction L; intros. simpl.
  rewrite Qvec_plus_Qvec_zero_r. apply Qvec_Eq_refl.
  destruct a as [f l]. simpl. rewrite <- Qvec_plus_assoc. apply IHL. Qed.

Lemma Qvec_sum_class_append : forall {n : nat} (w0: Qvec (S n)) (M1 M2: (list ((Qvec n)*bool))),
  Qvec_sum_class (Qvec_sum_class w0 M1) M2 = Qvec_sum_class w0 (List.app M1 M2).
Proof.
  intros n w0 M1. generalize dependent w0. induction M1; intros.
  { reflexivity. } destruct a as [f l]. simpl. apply IHM1. Qed.

Lemma Qvec_dot_comm : forall {n : nat} (v1 v2 : Qvec n),
  Qvec_dot v1 v2 == Qvec_dot v2 v1.
Proof.
  intros. set (P := fun n (v1 v2 : Qvec n) => Qvec_dot v1 v2 == Qvec_dot v2 v1).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros. reflexivity.
  repeat (rewrite Zvec_dot_cons). repeat rewrite Qvec_dot_cons. rewrite H.
  unfold Qmult; rewrite Qmult_comm. reflexivity. Qed.

Lemma Qvec_dot_Not_Qvec_zero : forall {n : nat} (v1 v2 : Qvec n),
  (~ Qvec_dot v1 v2 == 0) -> (~ v1 === Qvec_zero n) /\ (~ v2 === Qvec_zero n).
Proof.
  intros. split. unfold not; intros. apply H. rewrite H0. apply Qvec_dot_Qvec_zero_l.
  unfold not; intros. apply H. rewrite H0. apply Qvec_dot_Qvec_zero_r. Qed.

Lemma Qvec_cons_Not_Qvec_zero : forall {n : nat} (v1 : Qvec n) (h : Q),
  (~ cons Q h n v1 === Qvec_zero (S n)) -> (~ h == 0) \/ (~ v1 === Qvec_zero n).
Proof.
  intros n v1; induction v1; intros. unfold Qvec_zero in H. simpl in H. left. unfold not.
  intros. apply H. apply (QCons _ _ _ _ QNil H0). assert (H0 := Qeq_dec h0 0). destruct H0.
  { right. unfold not. intros. apply H. unfold Qvec_zero, const. fold (const 0 (S n)).
  fold (Qvec_zero (S n)). apply QCons. apply H0. apply q. } left. apply n0. Qed.

Lemma Qvec_normsq_Not_Qvec_Zero : forall {n : nat} (v1 : Qvec n),
  (~ v1 === Qvec_zero n) -> Qvec_normsq v1 > 0.
Proof.
  intros. induction v1. exfalso. apply H. reflexivity.
  apply Qvec_cons_Not_Qvec_zero in H. inversion H. apply Qsquare_gt_0 in H0.
  unfold Qvec_normsq. rewrite Qvec_dot_cons. fold (Qvec_normsq v1).
  unfold Qplus, Qmult; repeat rewrite Qred_correct. rewrite <- Qplus_0_r.
  apply (Qplus_lt_le_compat 0 _ 0 _ H0). apply Qvec_normsq_nonneg.
  apply IHv1 in H0. unfold Qvec_normsq. rewrite Qvec_dot_cons.
  fold (Qvec_normsq v1). unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite Qplus_comm. apply (Qplus_lt_le_compat 0 _ 0 _ H0 (Qsquare_nonneg _)). Qed.

Lemma Qvec_sum_dot_append : forall {n : nat} (L1 L2 : list ((Qvec n)*bool)) (w : Qvec (S n)),
  Qvec_sum_dot w (List.app L1 L2) == Qplus (Qvec_sum_dot w L1) (Qvec_sum_dot w L2).
Proof.
  intros n L1; induction L1; intros. simpl. symmetry. unfold Qplus;
  rewrite Qplus_0_l; apply Qred_correct.
  destruct a as [f l]. simpl. rewrite IHL1. unfold Qplus; repeat rewrite Qred_correct. 
  repeat (rewrite Qplus_assoc). reflexivity. Qed.

Lemma Qfoil : forall (A B C D : Q),
 (A + B) * (C + D) == (A * C) + (A * D) + (B * C) + (B * D).
Proof.
  intros. unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite Qmult_plus_distr_l. repeat (rewrite Qmult_plus_distr_r).
  apply Qplus_assoc. Qed.

Lemma CSHH : forall (A B : Q),
  (A * B) + (A * B) <= (A * A) + (B * B).
Proof.
  intros. assert ((A - B) * (A - B) == (QArith_base.Qplus (A * A) (B * B)) - (QArith_base.Qplus (A * B) (A * B))).
  unfold Qminus. assert (H := Qfoil A (Qopp B) A (Qopp B)).
  unfold Qplus in H; repeat rewrite Qred_correct in H. rewrite H. unfold Qmult; repeat rewrite Qred_correct.
  repeat rewrite <- Qopp_mult_distr_r. repeat rewrite <- Qopp_mult_distr_l.
  rewrite Qopp_involutive. repeat rewrite <- Qplus_assoc.
  rewrite (Qplus_comm _ (_ B B)). rewrite (Qplus_assoc _ (_ B B) _). rewrite (Qplus_comm _ (_ B B)).
  repeat rewrite <- Qplus_assoc. rewrite <- Qopp_plus. rewrite (Qmult_comm B A). reflexivity. 
  assert (0 <= (A - B) * (A - B)). unfold Qmult; rewrite Qred_correct. apply Qsquare_nonneg.
  rewrite H in H0. apply (Qplus_le_l _ _ (A * B + A * B)) in H0. rewrite Qplus_0_l in H0.
  unfold Qminus in H0. rewrite <- Qplus_assoc in H0.
  rewrite (Qplus_comm _ (_ (A*B) (A*B))) in H0.
  unfold Qplus in H0 at 2. rewrite Qred_correct in H0. rewrite Qplus_opp_r in H0.
  rewrite Qplus_0_r in H0. unfold Qplus at 2. rewrite Qred_correct. apply H0. Qed.

(* This is trivialy true if the parity of negatives is odd *)
Lemma Cauchy_Schwarz_helper': forall (A B C D : Q),
  A*B*C*D + A*B*C*D <= A*A*D*D + B*B*C*C.
Proof.
  intros. assert (forall (A B C D : Q), A*B*C*D == A*D*(B*C)). intros.
  unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite (Qmult_comm B0 C0). rewrite <- Qmult_assoc. rewrite <- Qmult_assoc.
  rewrite (Qmult_comm B0 (_ C0 D0)). rewrite Qmult_assoc. rewrite (Qmult_comm C0 D0).
  repeat rewrite Qmult_assoc. reflexivity. repeat rewrite H. apply CSHH. Qed.

Lemma Cauchy_Schwarz_helper : forall {n : nat} (v1 v2 : Qvec n) (A B : Q),
  A*B*(Qvec_dot v1 v2) + A*B*(Qvec_dot v1 v2) <= A*A*(Qvec_normsq v2) + B*B*(Qvec_normsq v1).
Proof.
  intros n v1 v2. set (P := fun n (v1 v2 : Qvec n) => forall (A B : Q),
  A*B*(Qvec_dot v1 v2) + A*B*(Qvec_dot v1 v2) <= A*A*(Qvec_normsq v2) + B*B*(Qvec_normsq v1)).
  change (P n v1 v2). apply mutual_induction; unfold P; clear P; intros.
  unfold Qvec_normsq, Qvec_dot; simpl. unfold Qmult; repeat rewrite Qred_correct.
  repeat rewrite Qmult_0_r. apply Qle_refl. repeat (rewrite Qvec_dot_cons). repeat (rewrite Qvec_normsq_cons).
  unfold Qplus, Qmult; repeat rewrite Qred_correct.
  repeat (rewrite Qmult_plus_distr_r). repeat (rewrite Qplus_assoc). repeat (rewrite Qmult_assoc).
  assert (forall (A B C D : Q), (QArith_base.Qplus (QArith_base.Qplus (QArith_base.Qplus A B) C) D) == 
  (QArith_base.Qplus (QArith_base.Qplus A C) (QArith_base.Qplus B D))). intros.
  repeat rewrite <- Qplus_assoc. rewrite (Qplus_assoc B0 C D). rewrite (Qplus_comm B0 C).
  rewrite <- Qplus_assoc. reflexivity. unfold Qplus in H0. repeat rewrite H0; clear H0.
  assert (H0 := Cauchy_Schwarz_helper' A B h1 h2). apply Qplus_le_compat.
  unfold Qplus, Qmult in H0; repeat rewrite Qred_correct in H0; apply H0.
  assert (H1 := H A B). unfold Qplus, Qmult in H1; repeat rewrite Qred_correct in H1; apply H1. Qed.

Lemma Cauchy_Schwarz_inequality : forall {n : nat} (v1 v2 : Qvec n),
  (Qvec_dot v1 v2)*(Qvec_dot v1 v2) <= (Qvec_normsq v1)*(Qvec_normsq v2).
Proof.
  intros. set (P := fun n (v1 v2 : Qvec n) =>
  (Qvec_dot v1 v2)*(Qvec_dot v1 v2) <= (Qvec_normsq v1)*(Qvec_normsq v2)). change (P n v1 v2).
  apply mutual_induction; unfold P; clear P; intros. apply Qle_refl.
  repeat (rewrite Qvec_dot_cons). repeat (rewrite Qvec_normsq_cons). repeat (rewrite Qfoil).
  unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite <- Qmult_assoc. rewrite (Qmult_comm h2 (QArith_base.Qmult h1 h2)). repeat rewrite Qmult_assoc.
  repeat rewrite <- Qplus_assoc. apply Qplus_le_r.
  repeat rewrite Qplus_assoc. apply Qplus_le_compat.
  { repeat rewrite <- Qmult_assoc. rewrite (Qmult_comm _ (QArith_base.Qmult h1 h2)).
    rewrite (Qmult_comm _ (QArith_base.Qmult h2 h2)). repeat rewrite Qmult_assoc.
    assert (H0 := Cauchy_Schwarz_helper t1 t2 h1 h2). unfold Qplus, Qmult in H0;
    repeat rewrite Qred_correct in H0. apply H0.
  } unfold Qmult in H; repeat rewrite Qred_correct in H; apply H. Qed.