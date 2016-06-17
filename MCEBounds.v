Require Import QArith.
Require Import Omega.
Require Import QvecArith PerceptronDef.
Require Import TerminationRefinement. (* needs inner_perceptron_MCE_sum_m_w *)

Fixpoint inject_nat (n : nat) : Q :=
match n with
| O => 0
| S n' => 1 + (inject_nat n')
end.

Lemma Qnat_le : forall (A B : nat),
  (A <= B)%nat -> (inject_nat A) <= (inject_nat B).
Proof.
  intros. induction H. apply Qle_refl. simpl. rewrite <- Qplus_0_l.
  apply (Qplus_le_compat 0 1 (inject_nat A) (inject_nat m)).
  unfold Qle. simpl. omega. apply IHle. Qed.

Lemma Qnat_lt : forall (A B : nat),
  (A < B)%nat -> (inject_nat A) < (inject_nat B).
Proof.
  intros. induction H. simpl. rewrite <- Qplus_0_l. apply Qplus_lt_le_compat.
  reflexivity. rewrite Qplus_0_l. apply Qle_refl. simpl. rewrite <- Qplus_0_l.
  apply Qplus_lt_le_compat. reflexivity. apply Qlt_le_weak. apply IHle. Qed.

Lemma Qnat_le_0 : forall (A : nat),
  0 <= (inject_nat A).
Proof.
  intros. induction A. apply Qle_refl. simpl. apply (Qplus_le_compat 0 _ 0).
  apply Qlt_le_weak. reflexivity. apply IHA. Qed.

Lemma Square_preserves_le : forall (A B : Q),
  0 <= A -> 0 <= B ->
  A <= B -> A*A <= B*B.
Proof.
  intros. unfold Qle in H, H0, H1. unfold Qle. simpl. simpl in H, H0, H1.
  rewrite Z.mul_1_r in H, H0. assert (forall (A B C D : Z), (A*B*(C*D) = (A*C)*(B*D))%Z).
  intros. repeat rewrite <- Z.mul_assoc. rewrite (Z.mul_assoc B0 C D).
  rewrite (Z.mul_comm B0 C). rewrite (Z.mul_assoc C B0 D). reflexivity.
  repeat rewrite Pos2Z.inj_mul. rewrite H2. rewrite (H2 (Qnum B) _ _ _).
  apply (Zmult_le_compat _ _ _ _ H1 H1); apply (Z.mul_nonneg_nonneg _ _ H (Zle_0_pos _)). Qed.
(*
 (****************************************************************************************
    Prove that ZtoNat holds a few properties for proving we can transform from
    Z.le to <=
  ****************************************************************************************)
Lemma ZtoNat_le : forall (A B : Z),
  Z.le A B -> (Z.to_nat A) <= (Z.to_nat B).
Proof.
  intros. destruct A; destruct B; try (apply Z2Nat.inj_le; omega; fail).
  assert (Z.gt (Z.pos p) Z0). apply Zgt_pos_0. omega.
  apply Z2Nat.inj_le. assert (Z.gt (Z.pos p) Z0). apply Zgt_pos_0. omega.
  assert (Z.gt (Z.pos p0) Z0). apply Zgt_pos_0. omega. apply H.
  assert (H0 := Zgt_pos_0 p). assert (H1 := Zlt_neg_0 p0). omega. reflexivity.
  simpl. assert (H0 := Zgt_pos_0 p). omega. reflexivity. Qed.

Lemma ZtoNat_plus_le : forall (A B : Z),
  Z.to_nat (Z.add A B) <= (Z.to_nat A) + (Z.to_nat B).
Proof.
  intros. destruct A; destruct B; try (reflexivity).
  simpl. omega. rewrite Z2Nat.inj_add. omega. assert (H:= Zgt_pos_0 p). omega.
  assert (H:= Zgt_pos_0 p0). omega.
  assert (Z.le (Z.add (Z.pos p) (Z.neg p0)) (Z.add (Z.pos p) Z0)). apply Zplus_le_compat_l.
  assert (H := Zlt_neg_0 p0). omega. apply ZtoNat_le in H. rewrite H. simpl. omega.
  assert (Z.le (Z.add (Z.neg p) (Z.pos p0)) (Z.add Z0 (Z.pos p0))). apply Zplus_le_compat_r.
  assert (H := Zlt_neg_0 p). omega. apply ZtoNat_le in H. rewrite H. simpl. omega. Qed.

 (****************************************************************************************
    Simple Arithmetic Facts used in Lower/Upper Bound
  ****************************************************************************************)
Lemma square_preserves_le : forall (A B : nat),
  A <= B -> A*A <= B*B.
Proof.
  intros; induction H. omega.
  simpl. rewrite mult_succ_r. omega. Qed.

Lemma mult_preserves_le : forall (A B C : nat),
  B <= C -> A*B <= A*C.
Proof.
  intros A; induction A; intros. omega.
  simpl. assert (H0 := IHA B C). omega. Qed. *)

 (****************************************************************************************
  Show that any element in MCE must be in T. Therefore properties of elements of T holds
  for elements of MCE.
  ****************************************************************************************)
Lemma In_inner_perceptron_MCE_In_T : forall {n : nat} (T : list ((Qvec n)*bool)) 
      (w0 : Qvec (S n)) (L : list ((Qvec n)*bool)) (w : Qvec (S n)) (f : Qvec n) (l : bool),
  inner_perceptron_MCE T w0 = Some (L, w) -> List.In (f, l) L -> List.In (f, l) T.
Proof.
  intros n T. induction T; intros. inversion H.
  destruct a as [f' l']. simpl in H. destruct (correct_class (Qvec_dot w0 (consb f')) l').
  apply IHT with w0 L w f l in H. right. apply H. apply H0.
  destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l' (consb f')))) eqn:H1.
  destruct p as [L' w']. inversion H; subst; clear H.
  inversion H0. left. apply H. right. apply IHT with _ _ _ f l in H1. apply H1. apply H.
  inversion H; subst; clear H. inversion H0. left. apply H. inversion H. Qed.

Lemma In_MCE_In_T : forall {n : nat} (E : nat ) (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)) (f : Qvec n) (l : bool),
  List.In (f, l) (MCE E T w0) -> List.In (f, l) T.
Proof.
  intros n E. induction E; intros. inversion H.
  simpl in H. destruct (inner_perceptron_MCE T w0) eqn: H0. destruct p as [L w'].
  apply List.in_app_or in H. inversion H.
  apply In_inner_perceptron_MCE_In_T with _ _ _ _ f l in H0. apply H0. apply H1.
  apply IHE in H1. apply H1. inversion H. Qed.

 (****************************************************************************************
                This section Proves the lower bound A*k^2 of length (MCE ...)
  ****************************************************************************************)
Definition limit_A {n : nat} (T : list ((Qvec n)*bool)) (wStar: Qvec (S n)) : Q :=
  Qmult (min_element_product wStar T) (min_element_product wStar T).

Lemma correct_class_w_dot_f_pos : forall {n : nat} (w : Qvec (S n)) (f : Qvec n) (l : bool),
 correct_class (Qvec_dot w (consb f)) l = true ->
 (Qvec_dot w (Qvec_mult_class l (consb f))) > 0.
Proof.
  intros. destruct l; unfold correct_class in H. simpl.
  destruct (class (Qvec_dot w (consb f))) eqn:H0. simpl in H.
  unfold class in H0. apply Bool.negb_true_iff in H.
  apply Qle_bool_imp_le in H0. apply Qeq_bool_neq in H.
  apply (Qle_neq_lt _ _ H0). unfold not. intros. apply H.
  symmetry. apply H1. inversion H.
  destruct (class (Qvec_dot w (consb f))) eqn:H0. inversion H. simpl in H.
  unfold class in H0. simpl in H0.
  assert (0 > (Qvec_dot w (consb f))). apply Qnot_le_lt. unfold not. intros.
  apply Qle_bool_iff in H1. rewrite H0 in H1. inversion H1.
  unfold Qvec_mult_class. rewrite Qvec_dot_mult_neg_1.
  unfold Qlt. simpl. unfold Qlt in H1. simpl in H1.
  destruct (Qnum (Qvec_dot w (consb f))); try inversion H1.
  rewrite Z.mul_1_r. rewrite Z.mul_1_r in H1.
  apply Z.sgn_pos_iff. reflexivity. Qed.

Lemma correct_class_T_limit_A_pos : forall {n : nat} (T : list ((Qvec n)*bool)) (w : Qvec (S n)),
  correctly_classifiedP T w -> (limit_A T w) > 0.
Proof.
  intros n T; induction T; intros. reflexivity.
  inversion H; subst.
  unfold limit_A, min_element_product. fold (min_element_product w T).
  destruct T. apply correct_class_w_dot_f_pos in H4.
  apply Qsquare_gt_0. unfold not. intros. apply Qlt_not_le in H4. apply H4.
  rewrite H0. apply Qle_refl.
  destruct (Qle_bool (Qvec_dot w (Qvec_mult_class l (consb f)))).
  apply correct_class_w_dot_f_pos in H4.
  apply Qsquare_gt_0. unfold not. intros. apply Qlt_not_le in H4. apply H4.
  rewrite H0. apply Qle_refl. apply IHT in H2.
  unfold limit_A in H2. apply H2. Qed.

Lemma correct_class_T_min_element_product : forall {n : nat} (T : list ((Qvec n)*bool)) (w : Qvec (S n)),
  correctly_classifiedP T w -> 0 < (min_element_product w T).
Proof.
  intros. induction T. simpl. reflexivity. inversion H; subst. apply IHT in H2.
  apply correct_class_w_dot_f_pos in H4. destruct T. simpl. apply H4.
  unfold min_element_product. fold (min_element_product w (List.cons p T)).
  destruct (Qle_bool _ _); assumption. Qed.

Lemma correct_class_T_Qvec_normsq_wstar : forall {n : nat} (T : list ((Qvec n)*bool)) (w : Qvec (S n)),
  correctly_classifiedP T w -> (Qvec_normsq w) > 0 \/ T = List.nil.
Proof.
  intros n T; induction T; intros. right. reflexivity. inversion H; subst. apply IHT in H2.
  inversion H2. left. apply H0. subst. left. apply correct_class_w_dot_f_pos in H4.
  inversion H; subst. apply correct_class_w_dot_f_pos in H7. apply Qlt_not_eq in H7.
  apply Qnot_eq_sym in H7. apply Qvec_dot_Not_Qvec_zero in H7. destruct H7 as [Hw Hlf].
  apply (Qvec_normsq_Not_Qvec_Zero w Hw). Qed.

Lemma correct_class_T_Qvec_sum_dot_inner_perceptron_MCE : forall {n : nat} 
                                   (T M: list ((Qvec n)*bool)) (wstar w0 w : Qvec (S n)),
  correctly_classifiedP T wstar -> inner_perceptron_MCE T w0 = Some (M, w) -> 0 <= Qvec_sum_dot wstar M.
Proof.
  intros n T M wstar; generalize dependent M; induction T; intros. inversion H0. destruct a as [f l].
  simpl in H0. inversion H; subst. destruct (correct_class (Qvec_dot w0 (consb f)) l). apply (IHT _ _ _ H5 H0).
  destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))) eqn:H1. destruct p as [M' w'].
  inversion H0; subst. simpl. apply IHT in H1. apply correct_class_w_dot_f_pos in H6.
  apply Qlt_le_weak in H6. apply (Qplus_le_compat 0 _ 0 _ H6 H1). apply H5.
  inversion H0; subst. simpl. apply correct_class_w_dot_f_pos in H6. apply Qlt_le_weak.
  rewrite Qplus_0_r. apply H6. Qed.

Lemma correct_class_T_Qvec_sum_dot_MCE : forall {n : nat} (E : nat) (T : list ((Qvec n)*bool)) (w w0 : Qvec (S n)),
  correctly_classifiedP T w -> 0 <= Qvec_sum_dot w (MCE E T w0).
Proof.
  intros n E; induction E; intros. apply Qle_refl. unfold MCE. destruct (inner_perceptron_MCE T w0) eqn:H0.
  destruct p as [L w']. fold (MCE E T w'). rewrite Qvec_sum_dot_append.
  apply correct_class_T_Qvec_sum_dot_inner_perceptron_MCE with (wstar := w) in H0.
  apply IHE with (w0 := w') in H. apply (Qplus_le_compat 0 _ 0 _ H0 H). apply H. apply Qle_refl. Qed.

Lemma Constant_le_element_le_sum_min_product : forall {n : nat} (L : list ((Qvec n)*bool)) (w : Qvec (S n)) (A : Q),
  0 < A ->
  (forall (f : Qvec n) (l : bool), List.In (f, l) L -> 
   A <= (Qvec_dot w (Qvec_mult_class l (consb f)))) ->
   (0 <= (Qvec_sum_dot w L)) /\
  A * (inject_nat (length L)) <= (Qvec_sum_dot w L).
Proof.
  intros n L; induction L; intros. simpl. split; [|rewrite Qmult_0_r]; apply Qle_refl.
  destruct a as [f l]. simpl. rewrite Qmult_plus_distr_r. rewrite Qmult_1_r.
  assert (H1 := H0 f l). assert (H2 : forall f l, List.In (f, l) L ->
  A <= (Qvec_dot w (Qvec_mult_class l (consb f)))). intros.
  assert (H3 : List.In (f0, l0) (List.cons (f, l) L)). right. apply H2. apply (H0 _ _ H3).
  assert (H3 := IHL w A H H2). assert (List.In (f, l) (List.cons (f, l) L)). left. reflexivity.
  apply H1 in H4. split. apply (Qplus_le_compat 0 _ 0 _). apply Qlt_le_weak in H.
  apply (Qle_trans 0 A _ H H4). apply H3. apply Qplus_le_compat. apply H4. apply H3. Qed.

Lemma Element_T_le_limit_A : forall {n : nat} (T : list ((Qvec n)*bool)) (w : Qvec (S n)) (f : Qvec n) (l : bool),
 List.In (f, l) T -> min_element_product w T <= Qvec_dot w (Qvec_mult_class l (consb f)).
Proof.
  intros n T w; induction T; intros. inversion H. destruct a as [f' l']. inversion H. inversion H0; subst.
  unfold min_element_product. fold (min_element_product w T). destruct T. apply Qle_refl.
  destruct (Qle_bool _ _) eqn:H1. apply Qle_refl.
  assert (~ (Qvec_dot w (Qvec_mult_class l (consb f))) <= (min_element_product w (p :: T))).
  unfold not. intros. apply Qle_bool_iff in H2. rewrite H1 in H2. inversion H2.
  apply Qnot_le_lt in H2. apply Qlt_le_weak in H2. apply H2. apply IHT in H0.
  destruct T. inversion H. inversion H1; subst; apply Qle_refl. inversion H1.
  unfold min_element_product. fold (min_element_product w (p :: T)).
  destruct (Qle_bool _ _) eqn:H1. apply Qle_bool_iff in H1. apply (Qle_trans _ _ _ H1 H0).
  apply H0. Qed.

Lemma linearly_separable_lower_bound : forall {n : nat} (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)),
  linearly_separable T -> (exists (A B : Q), forall (E : nat),
  ~(A == 0) /\ ~(B == 0) /\
  A* (inject_nat (length (MCE E T w0)))*(inject_nat (length (MCE E T w0))) <=
  B*(Qvec_normsq (Qvec_sum (MCE E T w0)))).
Proof.
  intros. unfold linearly_separable in H. destruct H as [wstar H]. assert (H0 := H). assert (H1 := H).
  apply correct_class_T_limit_A_pos in H. apply correct_class_T_Qvec_normsq_wstar in H0.
  exists (limit_A T wstar). inversion H0. exists (Qvec_normsq wstar).
  intros E. split. apply Qlt_not_le in H. unfold not. intros. apply H. rewrite H3. apply Qle_refl. split.
  apply Qlt_not_le in H2. unfold not. intros. apply H2. rewrite H3. apply Qle_refl.
  { apply (Qle_trans _ ((Qvec_dot wstar (Qvec_sum (MCE E T w0)))*(Qvec_dot wstar (Qvec_sum (MCE E T w0)))) _).
    { rewrite Qvec_dot_sum_eq. assert (H3 := H1). apply correct_class_T_min_element_product in H3.
      unfold limit_A. repeat rewrite <- Qmult_assoc. rewrite (Qmult_assoc _ (inject_nat _) (inject_nat _)).
      rewrite (Qmult_comm (min_element_product _ _) (inject_nat _)). repeat rewrite <- Qmult_assoc.
      rewrite Qmult_assoc. apply Square_preserves_le. rewrite <- (Qmult_0_l (inject_nat (length (MCE E T w0)))).
      apply Qlt_le_weak in H3. apply (Qmult_le_compat_r _ _ _ H3 (Qnat_le_0 _)).
      apply (correct_class_T_Qvec_sum_dot_MCE _ _ _ _ H1).
      apply Constant_le_element_le_sum_min_product. apply H3.
      intros. apply In_MCE_In_T in H4. apply (Element_T_le_limit_A _ wstar _ _ H4).
    } apply Cauchy_Schwarz_inequality.
  } exists 1. intros E. split. apply Qlt_not_le in H. unfold not. intros. apply H. rewrite H3. 
  apply Qle_refl. split. apply Q_apart_0_1. subst. unfold limit_A. simpl.
  repeat rewrite (Qmult_1_l). destruct E; simpl; rewrite Qmult_0_l; apply Qvec_normsq_nonneg. Qed.

 (****************************************************************************************
        This section will contains the proof of upper bound B*k on length (MCE ...)
  ****************************************************************************************)
Definition limit_B {n : nat} (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)): Z :=
  Z.sub (max_element_normsq T) (Z.mul (Zpos 2) (min_element_product w0 T)).

Lemma not_correct_z_mu_neg: forall {n:nat} (f : Zvec n) (l:bool) (w: Zvec (S n)),
  correct_class (Zvec_dot w (consb f)) l = false -> 
  (Z.le ((Zvec_dot w (Zvec_mult_class l (consb f)))) 0).
Proof.
  intros. unfold correct_class in H. destruct l.
  destruct (class (Zvec_dot w (consb f))) eqn:H0. simpl in H.
  apply Bool.negb_false_iff in H. apply Z.eqb_eq in H.
  unfold Zvec_mult_class. omega. unfold class in H0.
  assert (H2 := Zge_cases (Zvec_dot w (consb f)) Z0). rewrite H0 in H2.
  unfold Zvec_mult_class. omega. destruct (class (Zvec_dot w (consb f))) eqn:H0.
  unfold class in H0. assert (H1 := Zge_cases (Zvec_dot w (consb f)) Z0). rewrite H0 in H1.
  unfold Zvec_mult_class. rewrite Zvec_dot_mult_neg_1. omega.
  simpl in H. unfold Zvec_mult_class. rewrite Zvec_dot_mult_neg_1.
  apply Bool.negb_false_iff in H. apply Z.eqb_eq in H. omega.
Qed.

Lemma inner_perceptron_MCE_mu_neg: forall {n:nat} (T L: (list ((Zvec n)*bool))) (w0 w: Zvec (S n)),
  inner_perceptron_MCE T w0 = Some (L, w) -> (Z.le (Z.mul (Z.pos 2) (min_element_product w0 T)) 0).
Proof.
  intros n T; induction T; intros. inversion H.
  destruct a as [f l]. simpl in H.
  destruct (correct_class (Zvec_dot w0 (consb f)) l) eqn:H0.
  { apply IHT in H. destruct T. simpl in H. omega.
    unfold min_element_product. fold (min_element_product w0 (List.cons p T)).
    destruct (Z.leb (Zvec_dot w0 (Zvec_mult_class l (consb f))) (min_element_product w0 (List.cons p T))) eqn:H1.
    assert (H2 := (Zle_cases (Zvec_dot w0 (Zvec_mult_class l (consb f))) (min_element_product w0 (List.cons p T)))).
    rewrite H1 in H2. omega. apply H.
  } apply not_correct_z_mu_neg in H0.
    destruct T. simpl. destruct (Zvec_dot w0 (Zvec_mult_class l (consb f))).
    reflexivity. assert (Z.pos p~0 = Z.mul (Z.pos 2) (Z.pos p)). reflexivity. omega.
    assert (Z.neg p~0 = Z.mul (Z.pos 2) (Z.neg p)). reflexivity. omega.
    unfold min_element_product. fold (min_element_product w0 (List.cons p T)).
    assert (H2 := (Zle_cases (Zvec_dot w0 (Zvec_mult_class l (consb f))) (min_element_product w0 (List.cons p T)))).
    destruct (Z.leb (Zvec_dot w0 (Zvec_mult_class l (consb f))) (min_element_product w0 (List.cons p T))) eqn:H1; omega.
Qed.

Theorem mu_neg_or_pos: forall {n:nat} (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  (Z.le (Z.mul (Z.pos 2) (min_element_product w0 T)) 0) 
  \/ (forall (E : nat), length(MCE E T w0) = 0).
Proof.
  intros. induction T. right; intros. destruct E; reflexivity.
  inversion IHT. left. destruct a as [f l]. destruct T. simpl in H. omega.
  unfold min_element_product. fold (min_element_product w0 (List.cons p T)).
  destruct (Z.leb (Zvec_dot w0 (Zvec_mult_class l (consb f))) (min_element_product w0 (List.cons p T))) eqn:H0.
  assert (H1 := Zle_cases (Zvec_dot w0 (Zvec_mult_class l (consb f))) (min_element_product w0 (List.cons p T))).
  rewrite H0 in H1. omega. apply H. destruct (inner_perceptron_MCE (List.cons a T) w0) eqn:H0.
  destruct p as [L w]. apply inner_perceptron_MCE_mu_neg in H0. left. apply H0.
  right. intros. destruct E. reflexivity. unfold MCE. rewrite H0. reflexivity.
Qed.

Theorem max_element_normsq_pos : forall {n : nat} (T : (list ((Zvec n)*bool))),
  Z.gt (max_element_normsq T) Z0.
Proof.
  intros. induction T. simpl. omega.
  destruct a as [f l].
  destruct T.
  { simpl. apply Zvec_consb_gt_0.
  } unfold max_element_normsq. fold (max_element_normsq (List.cons p T)).
  assert (H := Zge_cases (Zvec_normsq (consb f)) (max_element_normsq (List.cons p T))).
  destruct (Z.geb (Zvec_normsq (consb f)) (max_element_normsq (List.cons p T))).
  apply Zvec_consb_gt_0. apply IHT. Qed.

Theorem limit_B_pos_or_MCE_nil : forall {n : nat} (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  Z.gt (limit_B T w0) Z0 \/ (forall (E : nat), length (MCE E T w0) = 0).
Proof.
  intros n w T. assert (H := mu_neg_or_pos w T). inversion H.
  left. assert (H1 := max_element_normsq_pos T). unfold limit_B. omega.
  right. apply H0.
Qed.

Lemma MCE_zvec_sum_normsq_expand : forall {n : nat} (E : nat) (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
  Zvec_normsq (Zvec_sum (MCE E T w0)) = Z.add (Zvec_sum_normsq (MCE E T w0))
  (Z.mul 2 (Z.sub (Zvec_foil w0 (MCE E T w0)) (Zvec_sum_dot w0 (MCE E T w0)))).
Proof.
  intros. assert (H := Zvec_normsq_eq_sum_normsq_foil (MCE E T w0)).
  rewrite H; clear H. rewrite Zvec_foil_0_w with _ w0 (MCE E T w0).
  rewrite Zvec_plus_Zvec_zero. reflexivity. Qed.

Lemma Zvec_foil_inner_perceptron_MCE_w0_le_0 : forall {n : nat} (T M : list ((Zvec n)*bool)) (w0 w: Zvec (S n)),
  inner_perceptron_MCE T w0 = Some (M, w) -> Z.le (Zvec_foil w0 M) Z0.
Proof.
  intros n T; induction T; intros. inversion H. destruct a as [f l].
  inversion H. destruct (correct_class (Zvec_dot w0 (consb f)) l) eqn:H2.
  apply (IHT _ _ _ H1). destruct (inner_perceptron_MCE T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H3.
  { destruct p as [M' w']. inversion H1; subst. simpl. apply IHT in H3.
    apply not_correct_z_mu_neg in H2. omega.
  } simpl in H1. inversion H1; subst. simpl. rewrite <- Zplus_0_r_reverse.
  apply (not_correct_z_mu_neg _ _ _ H2). Qed.

Lemma Zvec_foil_MCE_w0_le_0 : forall {n : nat} (E : nat) (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
  Z.le (Zvec_foil w0 (MCE E T w0)) Z0.
Proof.
  intros n E. induction E; intros. reflexivity.
  simpl. destruct (inner_perceptron_MCE T w0) eqn:H.
  { destruct p as [M w]. rewrite Zvec_foil_append. assert (H0 := H). apply Zvec_foil_inner_perceptron_MCE_w0_le_0 in H.
    apply inner_perceptron_MCE_sum_m_w in H0. rewrite Zvec_sum_sum_class. rewrite <- H0.
    assert (H1 := IHE T w). omega.
  } reflexivity. Qed. 

Lemma Constant_le_element_le_sum : forall {n : nat} (L : list ((Zvec n)*bool)) (w : Zvec (S n)) (A : Z),
  Z.lt Z0 A ->
  (forall (f : Zvec n) (l : bool), List.In (f, l) L -> 
  Z.le (Z.add (Zvec_normsq (consb f)) (Z.mul (Z.neg 2) (Zvec_dot w (Zvec_mult_class l (consb f))))) A) ->
  Z.to_nat (Z.add (Zvec_sum_normsq L) (Z.mul (Z.neg 2) (Zvec_sum_dot w L))) <= (Z.to_nat A) * (length L).
Proof.
  intros n L. induction L; intros. simpl. omega. destruct a as [f l].
  unfold Zvec_sum_normsq. fold (Zvec_sum_normsq L). unfold Zvec_sum_dot.
  fold (Zvec_sum_dot w L). rewrite Z.mul_add_distr_l. rewrite Z.add_assoc.
  assert (forall (A B C D : Z), Z.add (Z.add (Z.add A B) C) D = Z.add (Z.add A C) (Z.add B D)).
  intros. rewrite Z.add_assoc. omega. rewrite H1; clear H1.
  SearchAbout Z.to_nat. assert (length (List.cons (f, l) L) = S (length L)). reflexivity.
  rewrite H1; clear H1. rewrite mult_succ_r. rewrite ZtoNat_plus_le.
  assert (H1 := H0 f l). assert (List.In (f, l) (List.cons (f, l) L)). left. reflexivity.
  apply H1 in H2. apply ZtoNat_le in H2.
  assert (Z.to_nat (Zvec_sum_normsq L + -2 * Zvec_sum_dot w L) <= Z.to_nat A * length L).
  apply IHL. apply H. intros. assert (List.In (f0, l0) (List.cons (f, l) L)). right. apply H3.
  apply (H0 _ _ H4). omega. Qed.

Lemma Element_T_le_limit_B : forall {n : nat} (T : list ((Zvec n)*bool)) (w : Zvec (S n)) (f : Zvec n) (l : bool),
 List.In (f, l) T -> Z.le (Z.add (Zvec_normsq (consb f))
 (Z.mul (Z.neg 2) (Zvec_dot w (Zvec_mult_class l (consb f))))) (limit_B T w).
Proof.
  intros n T. induction T; intros. inversion H. unfold limit_B.
  assert (forall (A B : Z), Z.sub A (Z.mul 2 B) = Z.add A (Z.mul (Z.neg 2) B)). intros. omega. rewrite H0. clear H0. inversion H.
  { subst. unfold max_element_normsq, min_element_product. fold (max_element_normsq T).
    fold (min_element_product w T). destruct T. reflexivity.
    destruct (Z.geb (Zvec_normsq (consb f)) (max_element_normsq (List.cons p T))) eqn:H0.
    destruct (Z.leb (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))) eqn:H1. reflexivity.
    assert (H2 := Zle_cases (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))).
    rewrite H1 in H2. omega.
    assert (H1 := Zge_cases (Zvec_normsq (consb f)) (max_element_normsq (List.cons p T))). rewrite H0 in H1.
    destruct (Z.leb (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))) eqn:H2. omega.
    assert (H3 := Zle_cases (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))).
    rewrite H2 in H3. omega.
  } apply IHT with (w := w) in H0. destruct a as [f' l']. subst.
  unfold max_element_normsq, min_element_product. fold (max_element_normsq T). fold (min_element_product w T).
  destruct T. inversion H. inversion H1; subst. reflexivity. inversion H1.
  destruct (Z.geb (Zvec_normsq (consb f')) (max_element_normsq (List.cons p T))) eqn:H1.
  assert (H2 := Zge_cases (Zvec_normsq (consb f')) (max_element_normsq (List.cons p T))). rewrite H1 in H2.
  unfold limit_B in H0.
  destruct (Z.leb (Zvec_dot w (Zvec_mult_class l' (consb f'))) (min_element_product w (List.cons p T))) eqn:H3.
  assert (H4 := Zle_cases (Zvec_dot w (Zvec_mult_class l' (consb f'))) (min_element_product w (List.cons p T))).
  rewrite H3 in H4. omega. omega.
  unfold limit_B in H0.
  destruct (Z.leb (Zvec_dot w (Zvec_mult_class l' (consb f'))) (min_element_product w (List.cons p T))) eqn:H3.
  assert (H4 := Zle_cases (Zvec_dot w (Zvec_mult_class l' (consb f'))) (min_element_product w (List.cons p T))).
  rewrite H3 in H4. omega. omega. Qed.

(* The upper bound of errors does not require T to be linearly seperable *)
Lemma MCE_upper_bound : forall {n : nat} (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
 exists (B : nat), forall (E : nat),
 B <> 0 /\
 (Z.to_nat (Zvec_normsq (Zvec_sum (MCE E T w0)))) <= B * (List.length (MCE E T w0)).
Proof.
  intros. assert (H := mu_neg_or_pos w0 T). inversion H.
  { exists (Z.to_nat (limit_B T w0)). intros E.
    assert (H1: Z.gt (limit_B T w0) Z0). unfold limit_B. assert (H1 := max_element_normsq_pos T). omega. split.
    {
      destruct (limit_B T w0); try (inversion H1; fail). simpl. assert (H2 := Pos2Nat.is_succ p).
      destruct H2 as [n0 H2]. rewrite H2. omega.
    } unfold limit_B. assert (Z.sub (max_element_normsq T) (Z.mul (Z.pos 2) (min_element_product w0 T)) =
      (Z.add (max_element_normsq T) (Z.mul (Z.neg 2) (min_element_product w0 T)))). omega. rewrite H2.
      rewrite MCE_zvec_sum_normsq_expand. assert (Z.le (Z.add (Zvec_sum_normsq (MCE E T w0))
      (Z.mul 2 (Z.sub (Zvec_foil w0 (MCE E T w0)) (Zvec_sum_dot w0 (MCE E T w0)))))
      (Z.add (Zvec_sum_normsq (MCE E T w0)) (Z.mul (Z.neg 2) (Zvec_sum_dot w0 (MCE E T w0))))).
      assert (H3 := Zvec_foil_MCE_w0_le_0 E T w0). omega. apply ZtoNat_le in H3. rewrite H3.
      apply Constant_le_element_le_sum. unfold limit_B in H1. omega.
      intros. apply In_MCE_In_T in H4. apply Element_T_le_limit_B with (w:= w0) in H4.
      unfold limit_B in H4. assert (forall (A B:Z), Z.add A (Z.mul (Z.neg 2) B) = Z.sub A (Z.mul 2 B)). intros. omega.
      rewrite <- H5 in H4. apply H4.
  } exists 1. intros E. rewrite H0. simpl. assert (H1 := H0 E). split. omega.
  destruct (MCE E T w0). simpl. rewrite Zvec_normsq_zvec_zero. simpl. reflexivity. inversion H1.
Qed.

 (****************************************************************************************
    Combine Upper and Lower Bound into single Lemma.
  ****************************************************************************************)
Lemma linearly_separable_bound: forall {n : nat} (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
  linearly_separable T -> (exists (A B C : nat), forall (E : nat),
  A <> 0 /\ B <> 0 /\ C <> 0 /\
  A * (List.length (MCE E T w0)) * (List.length (MCE E T w0)) <= B * (Z.to_nat (Zvec_normsq (Zvec_sum (MCE E T w0)))) <=
  C * (List.length (MCE E T w0))).
Proof.
  intros. apply (linearly_separable_lower_bound T w0) in H. destruct H as [A [B H]].
  assert (H0 := MCE_upper_bound T w0). destruct H0 as [C H0].
  exists A. exists B. exists (B*C). intros.
  split. apply (H E). split. apply (H E). split.
  assert (B <> 0). apply (H E). assert (C <> 0). apply (H0 E). destruct B. omega. destruct C. omega. simpl.
  unfold not. intro. inversion H3. split. apply H. assert (H1 := H0 E). inversion H1.
  apply mult_preserves_le with (A := B) in H3. rewrite mult_assoc in H3. apply H3. Qed.
