Require Import QArith.
Require Import Omega.
Require Import QvecArith PerceptronDef.
Require Import TerminationRefinement. (* needs inner_perceptron_MCE_sum_m_w *)

(************************************************************************************************************
         Defines an injection from natural numbers to rationals and proves some basic properties.
 ************************************************************************************************************)

Fixpoint inject_nat (n : nat) : Q :=
match n with
| O => 0
| S n' => 1 + (inject_nat n')
end.

Lemma Qnat_le : forall (A B : nat),
  (A <= B)%nat -> (inject_nat A) <= (inject_nat B).
Proof.
  intros. induction H. apply Qle_refl. simpl. rewrite <- Qplus_0_l.
  unfold Qplus; rewrite Qred_correct.
  apply (Qplus_le_compat 0 1 (inject_nat A) (inject_nat m)).
  unfold Qle. simpl. omega. apply IHle. Qed.

Lemma Qnat_lt : forall (A B : nat),
  (A < B)%nat -> (inject_nat A) < (inject_nat B).
Proof.
  intros. induction H. simpl. rewrite <- Qplus_0_l at 1. unfold Qplus; rewrite Qred_correct.
  apply Qplus_lt_le_compat. reflexivity. apply Qle_refl. simpl. rewrite <- Qplus_0_l.
  unfold Qplus; rewrite Qred_correct. apply Qplus_lt_le_compat. reflexivity.
  apply Qlt_le_weak. apply IHle. Qed.

Lemma Qnat_le_0 : forall (A : nat),
  0 <= (inject_nat A).
Proof.
  intros. induction A. apply Qle_refl. simpl. unfold Qplus; rewrite Qred_correct.
  apply (Qplus_le_compat 0 _ 0). apply Qlt_le_weak. reflexivity. apply IHA. Qed.

Lemma Square_preserves_le : forall (A B : Q),
  0 <= A -> 0 <= B ->
  A <= B -> A*A <= B*B.
Proof.
  intros. unfold Qle in H, H0, H1. unfold Qmult; repeat rewrite Qred_correct.
  unfold Qle. simpl. simpl in H, H0, H1.
  rewrite Z.mul_1_r in H, H0. assert (forall (A B C D : Z), (A*B*(C*D) = (A*C)*(B*D))%Z).
  intros. repeat rewrite <- Z.mul_assoc. rewrite (Z.mul_assoc B0 C D).
  rewrite (Z.mul_comm B0 C). rewrite (Z.mul_assoc C B0 D). reflexivity.
  repeat rewrite Pos2Z.inj_mul. rewrite H2. rewrite (H2 (Qnum B) _ _ _).
  apply (Zmult_le_compat _ _ _ _ H1 H1); apply (Z.mul_nonneg_nonneg _ _ H (Zle_0_pos _)). Qed.

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
  unfold Qvec_mult_class. rewrite Qvec_dot_mult_neg_1. unfold Qmult; rewrite Qred_correct.
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
  destruct T. apply correct_class_w_dot_f_pos in H4. unfold Qmult; rewrite Qred_correct.
  apply Qsquare_gt_0. unfold not. intros. apply Qlt_not_le in H4. apply H4.
  rewrite H0. apply Qle_refl.
  destruct (Qle_bool (Qvec_dot w (Qvec_mult_class l (consb f)))).
  apply correct_class_w_dot_f_pos in H4. unfold Qmult; rewrite Qred_correct.
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
  apply Qlt_le_weak in H6. unfold Qplus; rewrite Qred_correct. apply (Qplus_le_compat 0 _ 0 _ H6 H1).
  apply H5. inversion H0; subst. simpl. apply correct_class_w_dot_f_pos in H6. apply Qlt_le_weak.
  unfold Qplus; rewrite Qred_correct. rewrite Qplus_0_r. apply H6. Qed.

Lemma correct_class_T_Qvec_sum_dot_MCE : forall {n : nat} (E : nat) (T : list ((Qvec n)*bool)) (w w0 : Qvec (S n)),
  correctly_classifiedP T w -> 0 <= Qvec_sum_dot w (MCE E T w0).
Proof.
  intros n E; induction E; intros. apply Qle_refl. unfold MCE. destruct (inner_perceptron_MCE T w0) eqn:H0.
  destruct p as [L w']. fold (MCE E T w'). rewrite Qvec_sum_dot_append.
  apply correct_class_T_Qvec_sum_dot_inner_perceptron_MCE with (wstar := w) in H0.
  apply IHE with (w0 := w') in H. unfold Qplus; rewrite Qred_correct.
  apply (Qplus_le_compat 0 _ 0 _ H0 H). apply H. apply Qle_refl. Qed.

Lemma Constant_le_element_le_sum_min_product : forall {n : nat} (L : list ((Qvec n)*bool)) (w : Qvec (S n)) (A : Q),
  0 < A ->
  (forall (f : Qvec n) (l : bool), List.In (f, l) L -> 
   A <= (Qvec_dot w (Qvec_mult_class l (consb f)))) ->
   (0 <= (Qvec_sum_dot w L)) /\
  A * (inject_nat (length L)) <= (Qvec_sum_dot w L).
Proof.
  intros n L; induction L; intros. simpl. split; [|unfold Qmult; rewrite Qmult_0_r]; apply Qle_refl.
  destruct a as [f l]. simpl. unfold Qplus, Qmult; repeat rewrite Qred_correct.
  rewrite Qmult_plus_distr_r. rewrite Qmult_1_r.
  assert (H1 := H0 f l). assert (H2 : forall f l, List.In (f, l) L ->
  A <= (Qvec_dot w (Qvec_mult_class l (consb f)))). intros.
  assert (H3 : List.In (f0, l0) (List.cons (f, l) L)). right. apply H2. apply (H0 _ _ H3).
  assert (H3 := IHL w A H H2). assert (List.In (f, l) (List.cons (f, l) L)). left. reflexivity.
  apply H1 in H4. split. apply (Qplus_le_compat 0 _ 0 _). apply Qlt_le_weak in H.
  apply (Qle_trans 0 A _ H H4). apply H3. apply Qplus_le_compat. apply H4.
  unfold Qmult in H3; rewrite Qred_correct in H3; apply H3. Qed.

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
  0 < A /\ 0 < B /\
  A*(inject_nat (length (MCE E T w0)))*(inject_nat (length (MCE E T w0))) <=
  B*(Qvec_normsq (Qvec_sum (MCE E T w0)))).
Proof.
  intros. unfold linearly_separable in H. destruct H as [wstar H]. assert (H0 := H). assert (H1 := H).
  apply correct_class_T_limit_A_pos in H. apply correct_class_T_Qvec_normsq_wstar in H0.
  exists (limit_A T wstar). inversion H0. exists (Qvec_normsq wstar).
  intros E. split. apply H. split. apply H2.
  { apply (Qle_trans _ ((Qvec_dot wstar (Qvec_sum (MCE E T w0)))*(Qvec_dot wstar (Qvec_sum (MCE E T w0)))) _).
    { rewrite Qvec_dot_sum_eq. assert (H3 := H1). apply correct_class_T_min_element_product in H3.
      unfold limit_A. unfold Qmult; repeat rewrite Qred_correct. repeat rewrite <- Qmult_assoc.
      rewrite (Qmult_assoc _ (inject_nat _) (inject_nat _)).
      rewrite (Qmult_comm (min_element_product _ _) (inject_nat _)). repeat rewrite <- Qmult_assoc.
      rewrite Qmult_assoc. assert (H4 := Square_preserves_le (QArith_base.Qmult (min_element_product wstar T)
      (inject_nat (length (MCE E T w0)))) (Qvec_sum_dot wstar (MCE E T w0))). unfold Qmult in H4;
      repeat rewrite Qred_correct in H4. apply H4.
      rewrite <- (Qmult_0_l (inject_nat (length (MCE E T w0)))).
      apply Qlt_le_weak in H3. apply (Qmult_le_compat_r _ _ _ H3 (Qnat_le_0 _)).
      apply (correct_class_T_Qvec_sum_dot_MCE _ _ _ _ H1).
      rewrite <- (Qred_correct (QArith_base.Qmult (min_element_product _ _) _)).
      apply Constant_le_element_le_sum_min_product. apply H3.
      intros. apply In_MCE_In_T in H5. apply (Element_T_le_limit_A _ wstar _ _ H5).
    } apply Cauchy_Schwarz_inequality.
  } exists 1. intros E. split. apply H. split. reflexivity. subst. unfold limit_A. simpl.
  unfold Qmult at 3. simpl. unfold Qmult; repeat rewrite Qred_correct.
  repeat rewrite (Qmult_1_l). destruct E; simpl; rewrite Qmult_0_l; apply Qvec_normsq_nonneg. Qed.

 (****************************************************************************************
        This section will contains the proof of upper bound B*k on length (MCE ...)
  ****************************************************************************************)
Definition limit_B {n : nat} (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)): Q :=
  Qminus (max_element_normsq T) (Qmult (2#1) (min_element_product w0 T)).

Lemma not_correct_z_mu_neg: forall {n:nat} (f : Qvec n) (l:bool) (w: Qvec (S n)),
  correct_class (Qvec_dot w (consb f)) l = false -> 
  ((Qvec_dot w (Qvec_mult_class l (consb f)))) <= 0.
Proof.
  intros. unfold correct_class in H. destruct l.
  destruct (class (Qvec_dot w (consb f))) eqn:H0. simpl in H.
  apply Bool.negb_false_iff in H. apply Qeq_bool_iff in H.
  unfold Qvec_mult_class. rewrite H. apply Qle_refl.
  unfold class in H0. simpl. apply Qnot_lt_le. unfold not. intros.
  apply Qlt_le_weak in H1. apply Qle_bool_iff in H1. rewrite H0 in H1.
  inversion H1. apply andb_false_iff in H. unfold Qvec_mult_class.
  rewrite Qvec_dot_mult_neg_1. inversion H. apply eqb_false_iff in H0.
  assert (class (Qvec_dot w (consb f)) <> false). unfold not. intros.
  apply H0. symmetry. apply H1. apply not_false_is_true in H1.
  unfold class in H1. apply Qle_bool_iff in H1. unfold Qmult; rewrite Qred_correct.
  unfold Qle. unfold Qle in H1.
  simpl. simpl in H1. destruct (Qnum (Qvec_dot w (consb f))). reflexivity.
  rewrite Z.mul_1_r in H1. rewrite Z.mul_1_r. apply Zlt_le_weak. apply Zlt_neg_0.
  rewrite Z.mul_1_r in H1. assert (H2 := Zlt_neg_0 p). exfalso.
  apply Zle_not_lt in H1. apply H1. apply H2.
  apply Bool.negb_false_iff in H0. apply Qeq_bool_iff in H0. rewrite H0.
  unfold Qmult; rewrite Qred_correct. rewrite Qmult_0_r. apply Qle_refl. Qed.

Lemma inner_perceptron_MCE_mu_neg: forall {n:nat} (T L: (list ((Qvec n)*bool))) (w0 w: Qvec (S n)),
  inner_perceptron_MCE T w0 = Some (L, w) -> (Qmult (2#1) (min_element_product w0 T)) <= 0.
Proof.
  intros n T; induction T; intros; unfold Qmult; repeat rewrite Qred_correct. inversion H.
  destruct a as [f l]. simpl in H.
  destruct (correct_class (Qvec_dot w0 (consb f)) l) eqn:H0.
  { apply IHT in H. destruct T. simpl in H. unfold Qmult in H. rewrite Qmult_1_r in H.
    unfold Qle in H. simpl in H. omega. unfold min_element_product.
    fold (min_element_product w0 (List.cons p T)). destruct (Qle_bool _ _) eqn:H1.
    apply Qle_bool_iff in H1. apply Qmult_le_l with (z := 2#1) in H1. unfold Qmult in H.
    rewrite Qred_correct in H. apply (Qle_trans _ _ _ H1 H). reflexivity. unfold Qmult in H;
    rewrite Qred_correct in H; apply H.
  } apply not_correct_z_mu_neg in H0.
    destruct T. simpl. apply Qmult_le_l with (z := 2#1) in H0. rewrite Qmult_0_r in H0.
    apply H0. reflexivity. unfold min_element_product. fold (min_element_product w0 (List.cons p T)).
    destruct (Qle_bool _ _) eqn:H1. apply Qmult_le_l with (z := 2#1) in H0. rewrite Qmult_0_r in H0.
    apply H0. reflexivity.
    assert (Qvec_dot w0 (Qvec_mult_class l (consb f)) > (min_element_product w0 (p :: T))).
    apply Qnot_le_lt. unfold not. intros. apply Qle_bool_iff in H2. rewrite H1 in H2. inversion H2.
    apply Qlt_le_weak in H2. rewrite <- (Qmult_0_r (2#1)). apply Qmult_le_l. reflexivity.
    apply (Qle_trans _ _ _ H2 H0). Qed.

Theorem mu_neg_or_pos: forall {n:nat} (w0 : Qvec (S n)) (T : (list ((Qvec n)*bool))),
  (2#1)*(min_element_product w0 T) <= 0
  \/ (forall (E : nat), length (MCE E T w0) = 0%nat).
Proof.
  intros. induction T. right; intros. destruct E; reflexivity.
  inversion IHT. left. destruct a as [f l]. destruct T. simpl in H.
  unfold Qle in H. simpl in H. omega. unfold min_element_product.
  fold (min_element_product w0 (List.cons p T)). destruct (Qle_bool _ _) eqn:H0.
  apply Qle_bool_iff in H0. apply Qmult_le_l with (z := 2#1) in H0.
  unfold Qmult; rewrite Qred_correct; unfold  Qmult in H; rewrite Qred_correct in H.
  apply (Qle_trans _ _ _ H0 H). reflexivity. apply H.
  destruct (inner_perceptron_MCE (a :: T) w0) eqn:H0. destruct p as [L w].
  apply inner_perceptron_MCE_mu_neg in H0. left. apply H0.
  right. intros. destruct E. reflexivity. unfold MCE. rewrite H0. reflexivity. Qed.

Theorem max_element_normsq_pos : forall {n : nat} (T : (list ((Qvec n)*bool))),
  max_element_normsq T > 0.
Proof.
  intros. induction T. simpl. reflexivity.
  destruct a as [f l].
  destruct T.
  { simpl. apply Qvec_consb_gt_0.
  } unfold max_element_normsq. fold (max_element_normsq (List.cons p T)).
  destruct Qge_bool; [apply Qvec_consb_gt_0 | apply IHT ]. Qed.

Theorem limit_B_pos_or_MCE_nil : forall {n : nat} (w0 : Qvec (S n)) (T : (list ((Qvec n)*bool))),
  limit_B T w0 > 0 \/ (forall (E : nat), length (MCE E T w0) = 0%nat).
Proof.
  intros n w T. assert (H := mu_neg_or_pos w T). inversion H.
  left. assert (H1 := max_element_normsq_pos T). unfold limit_B.
  apply Qopp_le_compat in H0. assert (0 = - 0). reflexivity. rewrite <- H2 in H0.
  unfold Qminus. apply (Qplus_lt_le_compat 0 _ 0 _ H1 H0).
  right. apply H0. Qed.

Lemma MCE_Qvec_sum_normsq_expand : forall {n : nat} (E : nat) (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)),
  Qvec_normsq (Qvec_sum (MCE E T w0)) == (Qvec_sum_normsq (MCE E T w0)) + 
                              (2#1)*((Qvec_foil w0 (MCE E T w0)) - (Qvec_sum_dot w0 (MCE E T w0))).
Proof.
  intros. assert (H := Qvec_normsq_eq_sum_normsq_foil (MCE E T w0)).
  rewrite H; clear H. assert (H := Qvec_foil_0_w (Qvec_zero (S n)) w0 (MCE E T w0)).
  rewrite Qvec_plus_Qvec_zero in H. rewrite H. reflexivity. Qed.

Lemma Qvec_foil_inner_perceptron_MCE_w0_le_0 : forall {n : nat} (T M : list ((Qvec n)*bool)) (w0 w: Qvec (S n)),
  inner_perceptron_MCE T w0 = Some (M, w) -> Qvec_foil w0 M <= 0.
Proof.
  intros n T; induction T; intros. inversion H. destruct a as [f l].
  inversion H. destruct (correct_class (Qvec_dot w0 (consb f)) l) eqn:H2.
  apply (IHT _ _ _ H1). destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))) eqn:H3.
  { destruct p as [M' w']. inversion H1; subst. simpl. apply IHT in H3.
    apply not_correct_z_mu_neg in H2. unfold Qplus; rewrite Qred_correct.
    apply (Qplus_le_compat _ 0 _ 0 H2 H3).
  } simpl in H1. inversion H1; subst. simpl. unfold Qplus; rewrite Qred_correct.
  rewrite Qplus_0_r. apply (not_correct_z_mu_neg _ _ _ H2). Qed.

Lemma Qvec_foil_MCE_w0_le_0 : forall {n : nat} (E : nat) (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)),
  Qvec_foil w0 (MCE E T w0) <= 0.
Proof.
  intros n E. induction E; intros. apply Qle_refl.
  simpl. destruct (inner_perceptron_MCE T w0) eqn:H.
  { destruct p as [M w]. rewrite Qvec_foil_append. assert (H0 := H).
    apply Qvec_foil_inner_perceptron_MCE_w0_le_0 in H.
    apply inner_perceptron_MCE_sum_m_w in H0. rewrite Qvec_sum_sum_class. rewrite <- H0.
    assert (H1 := IHE T w). unfold Qplus; rewrite Qred_correct; apply (Qplus_le_compat _ 0 _ 0 H H1).
  } apply Qle_refl. Qed. 

Lemma Constant_le_element_le_sum : forall {n : nat} (L : list ((Qvec n)*bool)) (w : Qvec (S n)) (A : Q),
  0 < A ->
  (forall (f : Qvec n) (l : bool), List.In (f, l) L ->
  (Qvec_normsq (consb f)) + ((-2#1)*(Qvec_dot w (Qvec_mult_class l (consb f)))) <= A) ->
  (Qvec_sum_normsq L) + ((-2#1)*(Qvec_sum_dot w L)) <= A * (inject_nat (length L)).
Proof.
  intros n L. induction L; intros. simpl. unfold Qmult; rewrite Qred_correct;
  repeat rewrite Qmult_0_r. apply Qle_refl.
  destruct a as [f l]. unfold Qvec_sum_normsq. fold (Qvec_sum_normsq L).
  unfold Qvec_sum_dot. fold (Qvec_sum_dot w L). simpl. unfold Qplus, Qmult; repeat rewrite Qred_correct.
  repeat rewrite Qmult_plus_distr_r. rewrite Qmult_1_r. repeat rewrite <- Qplus_assoc.
  rewrite (Qplus_assoc (Qvec_sum_normsq L) _ _).
  rewrite (Qplus_comm (Qvec_sum_normsq L) _). repeat rewrite <- Qplus_assoc. rewrite Qplus_assoc.
  apply Qplus_le_compat. assert (H1 := H0 f l). unfold Qplus, Qmult in H1; repeat rewrite Qred_correct in H1;
  apply H1. left. reflexivity. assert (H1 := IHL w A H). unfold Qplus, Qmult in H1;
  repeat rewrite Qred_correct in H1. apply H1. intros. apply H0. right. apply H2. Qed.

Lemma Qmult_neg_le : forall (x y z : Q),
  z < 0 -> x <= y -> z * y <= z * x.
Proof.
  intros. unfold Qmult; repeat rewrite Qred_correct.
  unfold Qle. unfold Qle in H0. simpl. unfold Qlt in H.
  simpl in H. rewrite Z.mul_1_r in H. destruct x, y, z. simpl.
  simpl in H0. simpl in H. repeat rewrite (Pos.mul_comm Qden1 _).
  repeat rewrite Pos2Z.inj_mul. repeat rewrite Z.mul_assoc.
  apply Zmult_le_compat_r. repeat rewrite <- Z.mul_assoc.
  apply Z.mul_le_mono_nonpos_l. apply (Zlt_le_weak _ _ H).
  apply H0. apply Zle_0_pos. Qed.

Lemma Element_T_le_limit_B : forall {n : nat} (T : list ((Qvec n)*bool)) (w : Qvec (S n)) (f : Qvec n) (l : bool),
 List.In (f, l) T ->
       (Qvec_normsq (consb f)) + ((-2#1)*(Qvec_dot w (Qvec_mult_class l (consb f)))) <= (limit_B T w).
Proof.
  intros n T. induction T; intros. inversion H. unfold limit_B.
  unfold Qminus. unfold Qmult at 2. rewrite <- Qred_opp. rewrite Qopp_mult_distr_l.
  fold (Qmult (Qopp (2#1)) (min_element_product w (a :: T))).
  assert (- (2#1) = (-2#1)). reflexivity. repeat rewrite H0; clear H0. inversion H.
  { subst. unfold max_element_normsq, min_element_product. fold (max_element_normsq T).
    fold (min_element_product w T). destruct T. unfold Qplus; rewrite Qred_correct. apply Qle_refl.
    unfold Qge_bool. destruct (Qle_bool (max_element_normsq _) _) eqn:H0.
    destruct (Qle_bool (Qvec_dot _ _) _) eqn:H1. unfold Qplus; rewrite Qred_correct; apply Qle_refl.
    assert (min_element_product w (p :: T) < Qvec_dot w (Qvec_mult_class l (consb f))).
    apply Qnot_le_lt. unfold not. intros. apply Qle_bool_iff in H2. rewrite H1 in H2. inversion H2.
    unfold Qplus. rewrite Qred_correct. apply Qplus_le_compat. apply Qle_refl. apply Qlt_le_weak in H2.
    apply Qmult_neg_le. reflexivity. apply H2.
    assert (Qvec_normsq (consb f) <= max_element_normsq (p :: T)).
    apply Qlt_le_weak. apply Qnot_le_lt. unfold not. intros.
    apply Qle_bool_iff in H1. rewrite H0 in H1. inversion H1. unfold Qplus; rewrite Qred_correct.
    apply (Qplus_le_compat _ _ _ _ H1). clear H0. clear H1.
    destruct (Qle_bool (Qvec_dot w _) _) eqn:H2. apply Qle_refl.
    apply Qmult_neg_le. reflexivity. apply Qlt_le_weak. apply Qnot_le_lt.
    red. intros. apply Qle_bool_iff in H0. rewrite H2 in H0. inversion H0.
  } apply IHT with (w := w) in H0. destruct a as [f' l'].
  unfold max_element_normsq, min_element_product. fold (max_element_normsq T). fold (min_element_product w T).
  destruct T. inversion H. inversion H1; subst. unfold Qplus; rewrite Qred_correct. apply Qle_refl. inversion H1.
  unfold Qge_bool. destruct (Qle_bool (max_element_normsq _) _) eqn:H1. apply Qle_bool_iff in H1.
  destruct (Qle_bool (Qvec_dot w _) _) eqn:H2. unfold Qopp; simpl. apply Qle_bool_iff in H2.
  unfold limit_B in H0. apply (Qle_trans _ _ _ H0). apply (Qplus_le_compat _ _ _ _ H1).
  unfold Qmult. rewrite <- Qred_opp.
  rewrite Qopp_mult_distr_l. apply Qmult_neg_le. reflexivity. apply H2.
  apply (Qle_trans _ _ _ H0). unfold limit_B. unfold Qminus. unfold Qmult.
  rewrite <- Qred_opp. rewrite Qopp_mult_distr_l.
  apply (Qplus_le_compat _ _ _ _ H1). assert (-(2#1) = -2#1). reflexivity. rewrite H3.
  apply Qle_refl. apply (Qle_trans _ _ _ H0). unfold limit_B. unfold Qminus.
  unfold Qmult. rewrite <- Qred_opp. rewrite Qopp_mult_distr_l. apply Qplus_le_compat. apply Qle_refl.
  apply Qmult_neg_le. reflexivity. clear H1. destruct (Qle_bool (Qvec_dot w _) _) eqn:H1.
  apply Qle_bool_iff in H1. apply H1. apply Qle_refl. Qed.

(* The upper bound of errors does not require T to be linearly seperable *)
Lemma MCE_upper_bound : forall {n : nat} (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)),
 exists (B : Q), forall (E : nat),
 0 < B /\
 Qvec_normsq (Qvec_sum (MCE E T w0)) <= B * inject_nat (length (MCE E T w0)).
Proof.
  intros. assert (H := limit_B_pos_or_MCE_nil w0 T). inversion H.
  { exists (limit_B T w0). intros E. split. apply H0.
    unfold limit_B, Qminus. unfold Qmult. rewrite <- Qred_opp.
    rewrite Qopp_mult_distr_l. assert (-(2#1) = (-2#1)). reflexivity.
    rewrite H1; clear H1. rewrite MCE_Qvec_sum_normsq_expand.
    assert ((Qvec_sum_normsq (MCE E T w0)) + (2#1)*((Qvec_foil w0 (MCE E T w0)) - (Qvec_sum_dot w0 (MCE E T w0)))
                                       <= (Qvec_sum_normsq (MCE E T w0)) + (-2#1)*(Qvec_sum_dot w0 (MCE E T w0))).
    unfold Qminus. unfold Qmult, Qplus; repeat rewrite Qred_correct.
    rewrite Qmult_plus_distr_r. assert (H3 := Qvec_foil_MCE_w0_le_0 E T w0).
    apply Qplus_le_compat. apply Qle_refl. rewrite <- (Qplus_0_l (_ (-2#1) (Qvec_sum_dot _ _))).
    apply Qplus_le_compat. rewrite <- (Qmult_0_r (2#1)). apply Qmult_le_l. reflexivity. apply H3.
    rewrite <- Qopp_mult_distr_r. rewrite Qopp_mult_distr_l. rewrite <- Qred_correct.
    fold (Qmult (Qopp (2#1)) (Qvec_sum_dot w0 (MCE E T w0))). rewrite <- (Qred_correct (_ (-2#1) _)) .
    fold (Qmult (-2#1) (Qvec_sum_dot w0 (MCE E T w0))). apply Qmult_neg_le; [reflexivity | apply Qle_refl].
    apply (Qle_trans _ _ _ H1). apply Constant_le_element_le_sum. unfold limit_B, Qminus in H0.
    unfold Qmult in H0. rewrite <- Qred_opp in H0.
    rewrite Qopp_mult_distr_l in H0. apply H0. intros. apply In_MCE_In_T in H2.
    apply Element_T_le_limit_B with (w:= w0) in H2. unfold limit_B in H2. unfold Qminus in H2.
    unfold Qmult in H2. rewrite <- Qred_opp in H2. rewrite Qopp_mult_distr_l in H2. apply H2.
  } exists 1. intros E. split. reflexivity. rewrite H0. simpl. assert (H1 := H0 E). unfold Qmult.
  rewrite Qmult_0_r. destruct (MCE E T w0); simpl. rewrite Qvec_normsq_Qvec_0. apply Qle_refl. inversion H1. Qed.

 (****************************************************************************************
    Combine Upper and Lower Bound into single Lemma.
  ****************************************************************************************)
Lemma linearly_separable_bound: forall {n : nat} (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)),
  linearly_separable T -> (exists (A B C : Q), forall (E : nat),
  0 < A /\ 0 < B /\ 0 < C /\
  A * (inject_nat (length (MCE E T w0))) *(inject_nat (length (MCE E T w0))) <=
  B * Qvec_normsq (Qvec_sum (MCE E T w0)) <=
  C * (inject_nat (length (MCE E T w0)))).
Proof.
  intros. apply (linearly_separable_lower_bound T w0) in H. destruct H as [A [B H]].
  assert (H0 := MCE_upper_bound T w0). destruct H0 as [C H0].
  exists A. exists B. exists (B*C). intros. split. apply (H E). split. apply (H E). split.
  rewrite <- (Qmult_0_l C). unfold Qmult; rewrite Qred_correct. apply Qmult_lt_r. apply (H0 E). apply (H E).
  split. apply H. unfold Qmult; repeat rewrite Qred_correct. rewrite (Qmult_comm B _). rewrite <- Qmult_assoc.
  rewrite (Qmult_comm _ (_ C _)). apply Qmult_le_compat_r. assert (H1 := H0 E).
  unfold Qmult in H1; rewrite Qred_correct in H1. apply H1. apply Qlt_le_weak. apply (H E). Qed.