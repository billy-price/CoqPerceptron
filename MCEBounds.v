Require Import ZArith.
Require Import Omega.
Require Import ZvecArith PerceptronDef.
Require Import TerminationRefinement. (* needs inner_perceptron_MCE_sum_m_w *)

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
  simpl. assert (H0 := IHA B C). omega. Qed.

 (****************************************************************************************
  Show that any element in MCE must be in T. Therefore properties of elements of T holds
  for elements of MCE.
  ****************************************************************************************)
Lemma In_inner_perceptron_MCE_In_T : forall {n : nat} (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)) (L : list ((Zvec n)*bool)) (w : Zvec (S n)) (f : Zvec n) (l : bool),
  inner_perceptron_MCE T w0 = Some (L, w) -> List.In (f, l) L -> List.In (f, l) T.
Proof.
  intros n T. induction T; intros. inversion H.
  destruct a as [f' l']. simpl in H. destruct (correct_class (Zvec_dot w0 (consb f')) l').
  apply IHT with w0 L w f l in H. right. apply H. apply H0.
  destruct (inner_perceptron_MCE T (Zvec_plus w0 (Zvec_mult_class l' (consb f')))) eqn:H1.
  destruct p as [L' w']. inversion H; subst; clear H.
  inversion H0. left. apply H. right. apply IHT with _ _ _ f l in H1. apply H1. apply H.
  inversion H; subst; clear H. inversion H0. left. apply H. inversion H. Qed.

Lemma In_MCE_In_T : forall {n : nat} (E : nat ) (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)) (f : Zvec n) (l : bool),
  List.In (f, l) (MCE E T w0) -> List.In (f, l) T.
Proof.
  intros n E. induction E; intros. inversion H.
  simpl in H. destruct (inner_perceptron_MCE T w0) eqn: H0. destruct p as [L w'].
  apply List.in_app_or in H. inversion H.
  apply In_inner_perceptron_MCE_In_T with _ _ _ _ f l in H0. apply H0. apply H1.
  apply IHE in H1. apply H1.
  inversion H. Qed.

 (****************************************************************************************
                This section Proves the lower bound A*k^2 of length (MCE ...)
  ****************************************************************************************)
Definition limit_A {n : nat} (T : list ((Zvec n)*bool)) (wStar: Zvec (S n)) : Z :=
  Zmult (min_element_product wStar T) (min_element_product wStar T).

Lemma correct_class_w_dot_f_pos : forall {n : nat} (w : Zvec (S n)) (f : Zvec n) (l : bool),
 correct_class (Zvec_dot w (consb f)) l = true ->
 Z.gt (Zvec_dot w (Zvec_mult_class l (consb f))) Z0.
Proof.
  intros. destruct l; unfold correct_class in H. simpl.
  destruct (class (Zvec_dot w (consb f))) eqn:H0. simpl in H.
  unfold class in H0. apply Bool.negb_true_iff in H.
  assert (H1 := Zge_cases (Zvec_dot w (consb f)) 0). rewrite H0 in H1.
  rewrite Z.eqb_neq in H. omega. inversion H.
  destruct (class (Zvec_dot w (consb f))) eqn:H0. inversion H. simpl in H.
  unfold class in H0. simpl in H0. assert (H1 := Zge_cases (Zvec_dot w (consb f)) Z0).
  rewrite H0 in H1. unfold Zvec_mult_class. rewrite Zvec_dot_mult_neg_1. omega. Qed.

Lemma correct_class_T_limit_A_pos : forall {n : nat} (T : list ((Zvec n)*bool)) (w : Zvec (S n)),
  correctly_classifiedP T w -> Z.gt (limit_A T w) Z0.
Proof.
  intros n T; induction T; intros. reflexivity.
  inversion H; subst.
  unfold limit_A, min_element_product. fold (min_element_product w T).
  destruct T. apply correct_class_w_dot_f_pos in H4. destruct (Zvec_dot w (Zvec_mult_class l (consb f))); inversion H4.
  reflexivity. destruct (Z.leb (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))) eqn:H0.
  apply correct_class_w_dot_f_pos in H4. destruct (Zvec_dot w (Zvec_mult_class l (consb f))); inversion H4. reflexivity.
  fold (limit_A (List.cons p T) w). apply (IHT w H2).
Qed.

Lemma correct_class_T_min_element_product : forall {n : nat} (T : list ((Zvec n)*bool)) (w : Zvec (S n)),
  correctly_classifiedP T w -> Z.lt Z0 (min_element_product w T).
Proof.
  intros. induction T. simpl. omega. inversion H; subst. apply IHT in H2. apply correct_class_w_dot_f_pos in H4.
  destruct T. simpl. omega. unfold min_element_product. fold (min_element_product w (List.cons p T)).
  destruct (Z.leb _ _); omega. Qed.

Lemma correct_class_T_Zvec_normsq_wstar : forall {n : nat} (T : list ((Zvec n)*bool)) (w : Zvec (S n)),
  correctly_classifiedP T w -> Z.gt (Zvec_normsq w) Z0 \/ T = List.nil.
Proof.
  intros n T; induction T; intros. right. reflexivity. inversion H; subst. apply IHT in H2.
  inversion H2. left. apply H0. subst. left. apply correct_class_w_dot_f_pos in H4.
  assert (Zvec_dot w (Zvec_mult_class l (consb f)) <> Z0). omega. apply Zvec_dot_Not_Zvec_zero in H0.
  destruct H0 as [H0 H1]. apply (Zvec_normsq_Not_Zvec_Zero w H0). Qed.

Lemma correct_class_T_Zvec_sum_dot_inner_perceptron_MCE : forall {n : nat} (T M: list ((Zvec n)*bool)) (wstar w0 w : Zvec (S n)),
  correctly_classifiedP T wstar -> inner_perceptron_MCE T w0 = Some (M, w) -> Z.le Z0 (Zvec_sum_dot wstar M).
Proof.
  intros n T M wstar; generalize dependent M; induction T; intros. inversion H0. destruct a as [f l].
  simpl in H0. inversion H; subst. destruct (correct_class (Zvec_dot w0 (consb f)) l). apply (IHT _ _ _ H5 H0).
  destruct (inner_perceptron_MCE T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H1. destruct p as [M' w']. inversion H0; subst.
  simpl. apply IHT in H1. apply correct_class_w_dot_f_pos in H6. omega. apply H5. inversion H0; subst.
  simpl. apply correct_class_w_dot_f_pos in H6. omega. Qed.

Lemma correct_class_T_Zvec_sum_dot_MCE : forall {n : nat} (E : nat) (T : list ((Zvec n)*bool)) (w w0 : Zvec (S n)),
  correctly_classifiedP T w -> Z.le Z0 (Zvec_sum_dot w (MCE E T w0)).
Proof.
  intros n E; induction E; intros. reflexivity. unfold MCE. destruct (inner_perceptron_MCE T w0) eqn:H0.
  destruct p as [L w']. fold (MCE E T w'). rewrite Zvec_sum_dot_append.
  apply correct_class_T_Zvec_sum_dot_inner_perceptron_MCE with (wstar := w) in H0. apply IHE with (w0 := w') in H. omega.
  apply H. reflexivity. Qed.

Lemma Constant_le_element_le_sum_min_product : forall {n : nat} (L : list ((Zvec n)*bool)) (w : Zvec (S n)) (A : Z),
  Z.lt Z0 A ->
  (forall (f : Zvec n) (l : bool), List.In (f, l) L -> 
   Z.le A (Zvec_dot w (Zvec_mult_class l (consb f)))) ->
   (Z.le Z0 (Zvec_sum_dot w L)) /\
  (Z.to_nat A) * (length L) <= (Z.to_nat (Zvec_sum_dot w L)).
Proof.
  intros n L; induction L; intros. simpl. split; omega. destruct a as [f l]. simpl. rewrite mult_succ_r.
  assert (H1 := H0 f l). assert (H2 : forall f l, List.In (f, l) L -> Z.le A (Zvec_dot w (Zvec_mult_class l (consb f)))).
  intros. assert (H3 : List.In (f0, l0) (List.cons (f, l) L)). right. apply H2. apply (H0 _ _ H3). assert (H3 := IHL w A H H2).
  assert (List.In (f, l) (List.cons (f, l) L)). left. reflexivity. apply H1 in H4. split. omega.
  rewrite Z2Nat.inj_add;[|omega|omega]. apply ZtoNat_le in H4. omega. Qed.

Lemma Element_T_le_limit_A : forall {n : nat} (T : list ((Zvec n)*bool)) (w : Zvec (S n)) (f : Zvec n) (l : bool),
 List.In (f, l) T -> Z.le (min_element_product w T) (Zvec_dot w (Zvec_mult_class l (consb f))).
Proof.
  intros n T w; induction T; intros. inversion H. destruct a as [f' l']. inversion H. inversion H0; subst.
  unfold min_element_product. fold (min_element_product w T). destruct T. omega.
  destruct (Z.leb (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))) eqn:H1. omega.
  assert (H2 := Zle_cases (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w (List.cons p T))).
  rewrite H1 in H2. omega. apply IHT in H0. unfold min_element_product. fold (min_element_product w T).
  destruct T. inversion H; inversion H1; subst. omega.
  destruct (Z.leb (Zvec_dot w (Zvec_mult_class l' (consb f'))) (min_element_product w (List.cons p T))) eqn:H1.
  assert (H2 := Zle_cases (Zvec_dot w (Zvec_mult_class l' (consb f'))) (min_element_product w (List.cons p T))).
  rewrite H1 in H2. omega. omega. Qed.

Lemma linearly_separable_lower_bound : forall {n : nat} (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
  linearly_separable T -> (exists (A B : nat), forall (E : nat),
  A <> 0 /\ B <> 0 /\
  A*(List.length (MCE E T w0))*(List.length (MCE E T w0)) <=
  B*(Z.to_nat (Zvec_normsq (Zvec_sum (MCE E T w0))))).
Proof.
  intros. unfold linearly_separable in H. destruct H as [wstar H]. assert (H0 := H). assert (H1 := H).
  apply correct_class_T_limit_A_pos in H. apply correct_class_T_Zvec_normsq_wstar in H0.
  exists (Z.to_nat (limit_A T wstar)). inversion H0. exists (Z.to_nat (Zvec_normsq wstar)).
  intros E. split. destruct (limit_A T wstar); try (inversion H; fail). simpl. assert (H3 := Pos2Nat.is_pos p).
  omega. split. destruct (Zvec_normsq wstar); try (inversion H2; fail). simpl. assert (H3 := Pos2Nat.is_pos p). omega.
  { rewrite <- (Z2Nat.inj_mul _ _ (Zvec_normsq_not_neg wstar) (Zvec_normsq_not_neg (Zvec_sum (MCE E T w0)))).
    assert (H3 := Cauchy_Schwarz_inequality wstar (Zvec_sum (MCE E T w0))). apply ZtoNat_le in H3. rewrite <- H3; clear H3.
    repeat rewrite Zvec_dot_sum_eq. assert (H3 := H1). apply (correct_class_T_Zvec_sum_dot_MCE E T _ w0) in H1.
    rewrite (Z2Nat.inj_mul _ _ H1 H1). unfold limit_A. apply correct_class_T_min_element_product in H3.
    rewrite (Z2Nat.inj_mul _ _);[|omega|omega]. assert (forall (A B : nat), A*A*B*B = (A*B)*(A*B)). intros. rewrite mult_assoc.
    rewrite mult_comm. rewrite mult_assoc. rewrite mult_assoc. assert (B*A = A*B). apply mult_comm. rewrite H4; clear H4. omega.
    rewrite H4; clear H4. assert (H4 := square_preserves_le ((Z.to_nat (min_element_product wstar T))*(length (MCE E T w0)))
    (Z.to_nat (Zvec_sum_dot wstar (MCE E T w0)))). apply H4; clear H4. apply Constant_le_element_le_sum_min_product. apply H3.
    intros. apply In_MCE_In_T in H4. apply Element_T_le_limit_A with (w := wstar) in H4. apply H4.
  } exists 1. intros E. split. destruct (limit_A T wstar); try (inversion H; fail). simpl. assert (H3 := Pos2Nat.is_pos p).
  omega. split. omega. destruct E. simpl. omega. rewrite H2. simpl. omega.
Qed.
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
