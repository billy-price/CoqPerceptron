Require Import QArith Qround QvecArith PerceptronDef.
Require Import TerminationRefinement MCEBounds PerceptronSound.
Require Import Omega.

Definition Qfloor_nat (q : Q) : nat := Z.to_nat (Qfloor q).

Lemma AB_limit : forall (A B C: Q),
  0 < A -> 0 < B -> 0 < C -> C > B / A -> A * C *C > B * C.
Proof.
  intros. unfold Qdiv in H2. apply (Qmult_lt_l _ _ A H) in H2.
  rewrite (Qmult_comm B _) in H2. rewrite Qmult_assoc in H2.
  rewrite Qmult_inv_r in H2. rewrite Qmult_1_l in H2.
  apply (Qmult_lt_r _ _ C H1) in H2. unfold Qmult;
  repeat rewrite Qred_correct. apply H2. unfold not. intros.
  apply Qlt_not_le in H. apply H. rewrite H3. apply Qle_refl. Qed.

Lemma Qfloor_lt' : forall (x : Q),
  x < 1 + inject_Z (Qfloor x).
Proof.
  intros. assert (1 = inject_Z 1%Z). reflexivity. rewrite H.
  unfold Qplus; rewrite Qred_correct.
  rewrite <- inject_Z_plus. rewrite Zplus_comm. apply Qlt_floor. Qed.

Lemma Nat_Z_inj : forall (n : nat),
  inject_nat n == inject_Z (Z.of_nat n).
Proof.
  intros. induction n. reflexivity. simpl.
  rewrite Zpos_P_of_succ_nat. rewrite <- Z.add_1_l.
  rewrite inject_Z_plus. rewrite IHn. unfold Qplus.
  rewrite Qred_correct. reflexivity. Qed.

Lemma Z_pos_nat_inj : forall (x : Z),
  (0 <= x -> Z.of_nat (Z.to_nat x) = x)%Z.
Proof.
  intros. induction x. reflexivity. simpl.
  apply positive_nat_Z. assert (H3 := Zlt_neg_0 p). omega. Qed.

 (****************************************************************************************
    Show that MCEBounds -> MCE reaches a fixed point.
  ****************************************************************************************)
Lemma linearly_separable_MCE : forall {n : nat} (w0 : Qvec (S n)) (T : list ((Qvec n)*bool)),
  linearly_separable T -> exists (E0 : nat),
  MCE E0 T w0 = MCE (S E0) T w0.
Proof.
  intros. apply (linearly_separable_bound T w0) in H. simpl in H.  destruct H as [A [B [C H]]].
  exists (S (Qfloor_nat (C / A))).
  assert (H0 := (H (S (Qfloor_nat (C / A))))).
  assert (H1 := (MCE_progress (S (Qfloor_nat (C / A))) w0 T)).
  inversion H1.
  {
    destruct H0 as [HA [HB [HC HAC]]].
    unfold MCE in H2. inversion H2.
    { fold (MCE (S (Qfloor_nat (C / A))) T w0) in H3.
      fold (MCE (S (Qfloor_nat (C / A))) T w0) in H2. rewrite <- H3 in HAC.
      assert (0 < inject_nat (S (Qfloor_nat (C / A)))). simpl.
      unfold Qplus; rewrite Qred_correct.
      apply (Qplus_lt_le_compat 0 _ 0 _). reflexivity. apply Qnat_le_0.
      assert (C / A < inject_nat (S (Qfloor_nat (C / A)))). simpl.
      rewrite Nat_Z_inj. unfold Qfloor_nat. rewrite Z_pos_nat_inj.
      apply Qfloor_lt'. assert (0%Z = Qfloor 0). reflexivity.
      rewrite H4. apply Qfloor_resp_le. apply Qlt_le_weak.
      unfold Qdiv. rewrite <- (Qmult_0_l (/ A)). apply Qmult_lt_r.
      apply Qinv_lt_0_compat. apply HA. apply HC.
      assert (HCA := (AB_limit A C (inject_nat (S (Qfloor_nat (C / A)))) HA HC H0 H4)).
      clear - HAC HCA. apply Qlt_not_le in HCA. exfalso. apply HCA.
      destruct HAC as [HleA HleC]. apply (Qle_trans _ _ _ HleA HleC).
    }
    fold (MCE (S (Qfloor_nat (C / A))) T w0) in H2. fold (MCE (S (Qfloor_nat (C / A))) T w0) in H0.
    rewrite <- H0 in HAC. assert (HCA := (AB_limit A C (inject_nat (S m)) HA HC)). exfalso.
    apply Qlt_not_le in HCA. apply HCA. destruct HAC as [HleA HleC]. apply (Qle_trans _ _ _ HleA HleC).
    simpl. unfold Qplus; rewrite Qred_correct.
    apply (Qplus_lt_le_compat 0 _ 0 _). reflexivity. apply Qnat_le_0.
    assert (C / A < inject_nat (S (Qfloor_nat (C / A)))).
    simpl. rewrite Nat_Z_inj. unfold Qfloor_nat. rewrite Z_pos_nat_inj.
    apply Qfloor_lt'. assert (0%Z = Qfloor 0). reflexivity.
    rewrite H4. apply Qfloor_resp_le. apply Qlt_le_weak.
    unfold Qdiv. rewrite <- (Qmult_0_l (/ A)). apply Qmult_lt_r.
    apply Qinv_lt_0_compat. apply HA. apply HC. apply (Qlt_trans _ _ _ H4).
    apply Qnat_lt. apply le_lt_n_Sm. apply H3.
  } apply H2. Qed.

 (****************************************************************************************
    Show that perceptron_MCE reaches a fixed point. (MCE fixed point + termination refinement)
  ****************************************************************************************)
Theorem linearly_separable_perceptron_MCE : forall {n : nat} (w0 : Qvec (S n)) (T : (list ((Qvec n)*bool))),
  linearly_separable T ->
  exists (E0 : nat) M (w : (Qvec (S n))), forall E, (E >= E0)%nat -> perceptron_MCE E T w0 = Some (M, w).
Proof.
  intros. apply linearly_separable_MCE with w0 T in H. destruct H as [E0 H].
  exists (S E0). exists (MCE E0 T w0). exists (Qvec_sum_class w0 (MCE E0 T w0)). intros E.
  intros H1. apply MCE_eq_perceptron_MCE in H. apply perceptron_MCE_done with (S E0). omega. apply H. Qed.

 (****************************************************************************************
  (Show that perceptron reaches a fixed point (converges)
    perceptron_MCE reaches a fixed point + termination refinement
 ****************************************************************************************)
Theorem linearly_separable_perceptron : forall {n : nat} (w0 : Qvec (S n)) (T : (list ((Qvec n)*bool))),
  linearly_separable T <->
  exists (E0 : nat) (w : (Qvec (S n))), forall E, (E >= E0)%nat -> perceptron E T w0 = Some w.
Proof.
  split; intros. apply linearly_separable_perceptron_MCE with w0 T in H.
  destruct H as [E0 [M [w H]]]. exists E0. exists w. intros. apply H in H0.
  apply perceptron_MCE_perceptron. exists M. auto.
  destruct H as [E0 [w H]].
  apply (perceptron_linearly_separable (S E0) w0 w).
  apply H. auto. Qed.

(*******************************************************************************************
  Show that Average Perceptron reaches a fixed point (converges)
    linearly_separable_perceptron + termination refinement
 *******************************************************************************************)
Theorem linearly_separable_average_perceptron : forall {n : nat} (w0 : Qvec (S n)) (T : (list ((Qvec n)*bool))),
    linearly_separable T <->
    exists (E0 : nat) (w : (Qvec (S n))), forall E, (E >= E0)%nat -> average_perceptron E T w0 = Some w.
Proof.
  split; intros. apply linearly_separable_perceptron with w0 T in H.
  destruct H as [E0 [w H]].
  assert (forall E, (E >= E0)%nat -> exists w, average_perceptron E T w0 = Some w).
  { intros. apply H in H0. apply perceptron_average_perceptron. exists w. auto. }
  clear H. exists E0. assert (E0 >= E0)%nat. omega. apply H0 in H.
  destruct H as [? H]. exists x. clear -H.
  intros. eapply average_perceptron_done. apply H0. apply H.
  destruct H as [E0 [w H]]. assert (E0 >= E0)%nat. omega.
  apply H in H0. assert (exists w, perceptron E0 T w0 = Some w).
  apply perceptron_average_perceptron. exists w. apply H0.
  destruct H1 as [? H1]. apply (perceptron_linearly_separable E0 w0 x).
  apply H1.
Qed.

Print Assumptions linearly_separable_perceptron.