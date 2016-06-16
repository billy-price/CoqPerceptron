Require Import QvecArith PerceptronDef.

 (***************************************************************************************************
    inner_perceptron_MCE <-> inner_perceptron. Equivalent w / None Return values
  ***************************************************************************************************)
Theorem inner_perceptron_MCE_inner_perceptron_None : forall {n : nat} T (w0: Qvec (S n)),
  inner_perceptron_MCE T w0 = None <-> inner_perceptron T w0 = None.
Proof.
  split; generalize dependent w0; induction T; intros w0 H.
  reflexivity. destruct a as [f l].
  inversion H. unfold inner_perceptron. destruct (correct_class (Qvec_dot w0 (consb f)) l) eqn: H2.
  fold (inner_perceptron T w0). apply IHT in H1. apply H1.
  destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))).  destruct p.
  inversion H1. inversion H1. reflexivity. destruct a as [f l].
  inversion H. unfold inner_perceptron_MCE. destruct (correct_class (Qvec_dot w0 (consb f)) l).
  fold (inner_perceptron_MCE T w0). apply IHT in H1. apply H1.
  destruct (inner_perceptron T (Qvec_plus w0 (Qvec_mult_class l (consb f)))).
  inversion H1. inversion H1. Qed.

Theorem inner_perceptron_MCE_inner_perceptron : forall {n : nat} T (w0 w : Qvec (S n)),
  (exists M, inner_perceptron_MCE T w0 = Some (M, w)) <-> inner_perceptron T w0 = Some w.
Proof.
  split; generalize dependent w0; generalize dependent w;
  induction T; intros; [destruct H as [M H]|destruct H as [M H]| |].
  { inversion H. } (* base case T = nil *)
  destruct a as [f l]. inversion H. unfold inner_perceptron.
  destruct (correct_class (Qvec_dot w0 (consb f)) l) eqn:H2.
  fold (inner_perceptron T w0). apply IHT. exists M. apply H1.
  fold (inner_perceptron T (Qvec_plus w0 (Qvec_mult_class l (consb f)))).
  destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))) eqn:H3.
  destruct p as [L w'].
  assert (H4: inner_perceptron T (Qvec_plus w0 (Qvec_mult_class l (consb f))) = Some w').
  apply IHT. exists L. apply H3. rewrite H4. inversion H1; subst; auto.
  apply inner_perceptron_MCE_inner_perceptron_None in H3.
  rewrite H3. inversion H1; subst; auto.
  { inversion H. } (* base case T = nil *)
  destruct a as [f l]. inversion H. unfold inner_perceptron_MCE.
  destruct (correct_class (Qvec_dot w0 (consb f)) l) eqn: H6.
  fold (inner_perceptron_MCE T w0). apply IHT with w w0 in H1. apply H1.
  destruct (inner_perceptron T (Qvec_plus w0 (Qvec_mult_class l (consb f)))) eqn:H2.
  inversion H1; subst. fold (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))).
  apply IHT in H2. destruct H2 as [M H2]. rewrite H2. exists (List.cons (f, l) M). auto.
  fold (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))).
  apply inner_perceptron_MCE_inner_perceptron_None in H2.
  rewrite H2. exists (List.cons (f,l) List.nil). inversion H1; subst. auto. Qed.

 (***************************************************************************************************
    Links return values of MCE, Perceptron_MCE and perceptron.
  ***************************************************************************************************)
Lemma Perceptron_MCE_MCE : forall {n : nat} (E : nat) (T M : list ((Qvec n)*bool)) (w0 w : Qvec (S n)),
  perceptron_MCE E T w0 = Some (M, w) -> MCE E T w0 = M.
Proof.
  intros n E. induction E; intros.
  { inversion H. } (* base case *)
  inversion H. unfold MCE. destruct (inner_perceptron_MCE T w0).
  destruct p as [L w']. fold (MCE E T w'). destruct (perceptron_MCE E T w') eqn:H2.
  destruct p as [L' w'']. apply IHE in H2. rewrite H2.
  inversion H1; subst; clear H1; auto. inversion H1.
  inversion H1; subst; clear H1; auto. Qed.

Theorem perceptron_MCE_perceptron : forall {n : nat} (E : nat) T (w0 w : Qvec (S n)),
  (exists M, perceptron_MCE E T w0 = Some (M, w)) <-> perceptron E T w0 = Some w.
Proof.
  split; generalize dependent T; generalize dependent w0;
  generalize dependent w; induction E; intros;
  [destruct H as [M H]| destruct H as [M H]| |].
  { inversion H. } (* base case E = 0 *)
  inversion H. unfold perceptron. destruct (inner_perceptron_MCE T w0) eqn:H2.
  destruct p as [L w']. assert (H3: inner_perceptron T w0 = Some w').
  apply inner_perceptron_MCE_inner_perceptron. exists L. apply H2. rewrite H3.
  fold (perceptron E T w'). destruct (perceptron_MCE E T w') eqn:H4.
  apply IHE. destruct p as [L' w'']. exists L'. inversion H1; subst.
  apply H4. inversion H1. apply inner_perceptron_MCE_inner_perceptron_None in H2. rewrite H2.
  inversion H1; subst. auto.
  { inversion H. } (* base case E = 0 *)
  inversion H. destruct (inner_perceptron T w0) eqn:H2. apply IHE in H1.
  destruct H1 as [M H1]. unfold perceptron_MCE. apply inner_perceptron_MCE_inner_perceptron in H2.
  destruct H2 as [M' H2]. rewrite H2. fold (perceptron_MCE E T q). rewrite H1. exists (List.app M' M).
  auto. inversion H1; subst; clear H1. apply inner_perceptron_MCE_inner_perceptron_None in H2.
  unfold perceptron_MCE. rewrite H2. exists List.nil. auto. Qed.

 (***************************************************************************************************
    Show that w = Sum of Misclassified Errors
  ***************************************************************************************************)
Lemma inner_perceptron_MCE_sum_m_w : forall {n : nat} (T M: (list ((Qvec n)*bool))) (w0 w: Qvec (S n)),
  inner_perceptron_MCE T w0 = Some (M, w) -> w = Qvec_sum_class w0 M.
Proof.
  intros n T. induction T; intros.
  { inversion H. } (* base case T = nil *)
  destruct a as [f l]. inversion H. destruct (correct_class (Qvec_dot w0 (consb f)) l).
  apply IHT in H1. apply H1.
  destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f)))) eqn:H3;
  [destruct p as [M' w']; apply IHT in H3|]; inversion H1; subst; clear H1;
  [rewrite <- H4|]; reflexivity. Qed.

Lemma perceptron_MCE_sum_m_w : forall {n : nat} (E : nat) (T M: (list ((Qvec n)*bool))) (w0 w: Qvec (S n)),
  perceptron_MCE E T w0 = Some (M, w) -> w = Qvec_sum_class w0 M.
Proof.
  intros n E. induction E; intros.
  { inversion H. } (* base case *)
  inversion H. destruct (inner_perceptron_MCE T w0) eqn:H2. destruct p as [M' w'].
  apply inner_perceptron_MCE_sum_m_w in H2. destruct (perceptron_MCE E T w') eqn: H3.
  destruct p as [M'' W'']. inversion H1; subst; clear H1. apply IHE in H3.
  rewrite Qvec_sum_class_append in H3. apply H3. inversion H1.
  inversion H1; subst; clear H1. reflexivity. Qed.

 (***************************************************************************************************
    If Perceptron_MCE E T w0 = Some (M, w) then that is a fix point (ie No amount of additional
    fuel will change the output.
  ***************************************************************************************************)
Theorem perceptron_MCE_S : forall {n : nat} (E : nat) (w w0 : Qvec (S n)) (T M : list ((Qvec n)*bool)),
  perceptron_MCE E T w0 = Some (M, w) -> perceptron_MCE (S E) T w0 = Some (M, w).
Proof.
  intros n E. induction E; intros.
  { inversion H. } (* Base Case E = 0 *)
  simpl in H. simpl.
  destruct (inner_perceptron_MCE T w0). destruct p as [L w'].
  destruct (perceptron_MCE E T w') eqn: H1. destruct p as [L' w''].
  apply IHE in H1. simpl in H1.
  destruct (inner_perceptron_MCE T w'). destruct p as [L'' w'''].
  destruct (perceptron_MCE E T w'''). destruct p as [L''' w''''].
  inversion H1; subst; clear H1. apply H. inversion H1.
  inversion H1; subst; clear H1. apply H. inversion H. apply H. Qed.

Lemma perceptron_MCE_done : forall {n : nat} (E0 E : nat) (w w0 : Qvec (S n)) (T M : list ((Qvec n)*bool)),
  E >= E0 -> perceptron_MCE E0 T w0 = Some (M, w) -> perceptron_MCE E T w0 = Some (M, w).
Proof.
  intros. induction H. apply H0.
  apply perceptron_MCE_S in IHle. apply IHle. Qed.

 (***************************************************************************************************
    inner_perceptron_MCE = Some (List.nil, _) is an invalid state. Useful for Proofs about MCE
  ***************************************************************************************************)
Lemma inner_perceptron_MCE_nil_false : forall {n: nat} (w0 w: Qvec (S n)) (T : list ((Qvec n)*bool)),
  inner_perceptron_MCE T w0 = Some (List.nil, w) -> False.
Proof.
  intros n w0 w T. revert w w0. induction T; intros; inversion H.
  destruct a as [f l].
  destruct (correct_class (Qvec_dot w0 (consb f)) l).
    apply IHT in H1; inversion H1.
    destruct (inner_perceptron_MCE T (Qvec_plus w0 (Qvec_mult_class l (consb f))));
    [destruct p as [L w']| ]; inversion H1. Qed.

 (***************************************************************************************************
    If MCE E T w0 = MCE (S E) T w0 then that is a fix point. (Has Converged to a single value).
  ***************************************************************************************************)
Lemma MCE_S : forall {n : nat} (E : nat) (T : list ((Qvec n)*bool)) (w0 : Qvec (S n)),
  MCE E T w0 = MCE (S E) T w0 -> MCE (S E) T w0 = MCE (S (S E)) T w0.
Proof.
  intros n E. induction E; intros.
  rewrite <- H. simpl. simpl in H.
  destruct (inner_perceptron_MCE T w0) eqn:H0. destruct p as [L w].
    destruct L; [apply inner_perceptron_MCE_nil_false in H0; inversion H0 | inversion H].
    reflexivity.
  unfold MCE in H. destruct (inner_perceptron_MCE T w0) eqn:H1. destruct p as [L w].
  fold (MCE E T w) in H. fold (MCE (S E) T w) in H.
  apply List.app_inv_head in H. apply IHE in H.
  unfold MCE. rewrite H1. fold (MCE (S E) T w). fold (MCE (S (S E)) T w).
  rewrite H. reflexivity.
  simpl. rewrite H1. reflexivity. Qed.

Lemma MCE_done : forall {n : nat} (E0 E : nat) (w0 : Qvec (S n)) (T : list ((Qvec n)*bool)),
  E >= E0 -> MCE E0 T w0 = MCE (S E0) T w0 -> MCE E0 T w0 = MCE E T w0.
Proof.
  intros. revert dependent w0. revert dependent T. induction H; intros.
  reflexivity. assert (H1 := H0).
  apply IHle in H0. rewrite H1.
  simpl. destruct (inner_perceptron_MCE T w0) eqn:H2. destruct p as [L w].
  assert (H3: (MCE E0 T w) = (MCE (S E0) T w)).
    destruct E0. simpl in H1. rewrite H2 in H1.
    destruct L. apply inner_perceptron_MCE_nil_false in H2. inversion H2. inversion H1.
    unfold MCE in H1. rewrite H2 in H1. fold (MCE E0 T w) in H1.
    fold (MCE (S E0) T w) in H1. apply List.app_inv_head in H1.
    apply MCE_S in H1. apply H1.
  apply IHle in H3. rewrite H3. reflexivity. reflexivity. Qed.

 (***************************************************************************************************
    If MCE has reached a fix point then perceptron_MCE on the same arguments will too.
  ***************************************************************************************************)
Lemma MCE_eq_perceptron_MCE : forall {n : nat} (E : nat) (w0 : Qvec (S n)) (T : list ((Qvec n)*bool)),
 MCE E T w0 = MCE (S E) T w0 ->
 perceptron_MCE (S E) T w0 = Some ((MCE E T w0), Qvec_sum_class w0 (MCE E T w0)).
Proof.
  intros n E. induction E; intros.
  simpl in H. destruct (inner_perceptron_MCE T w0) eqn:H1.
    destruct p as [L w']. destruct L.
      apply inner_perceptron_MCE_nil_false in H1; inversion H1.
      inversion H.
    simpl; rewrite H1. auto.
  unfold MCE in H. destruct (inner_perceptron_MCE T w0) eqn:H1.
  destruct p as [L w']. fold (MCE E T w') in H.
  fold (MCE (S E) T w') in H. apply List.app_inv_head in H.
  apply IHE in H. simpl. rewrite H1. simpl in H. rewrite H.
  apply inner_perceptron_MCE_sum_m_w in H1. rewrite H1.
  rewrite Qvec_sum_class_append. auto.
  simpl. rewrite H1. auto. Qed.

 (***************************************************************************************************
    Show that MCE either misclassifies at least E elements after E iterations or is at a fixed point.
  ***************************************************************************************************)
Lemma MCE_eq_length : forall {n : nat} (E1 E2 : nat) (w0 : Qvec (S n)) (T : list ((Qvec n)*bool)),
  length (MCE E1 T w0) = length (MCE E2 T w0) -> (MCE E1 T w0) = (MCE E2 T w0).
Proof.
  intros n E1. induction E1; intros.
{ simpl. simpl in H. destruct (MCE E2 T w0). auto. inversion H. } (* Base Case *)
  simpl in H. destruct (inner_perceptron_MCE T w0) eqn:H1.
  { destruct p as [L w]. destruct E2. simpl in H.
    { destruct L. apply inner_perceptron_MCE_nil_false in H1. inversion H1. inversion H. }
    simpl in H. rewrite H1 in H. rewrite List.app_length in H. rewrite List.app_length in H.
    assert (forall (a b c : nat), a + b = a + c -> b = c). intros. omega.
    apply H0 in H. apply IHE1 in H. simpl. rewrite H1. rewrite H. auto.
  }
  simpl in H. destruct E2; simpl; rewrite H1; auto. Qed.

Lemma MCE_progress : forall {n : nat} (E : nat) (w0 : Qvec (S n)) (T : list ((Qvec n)*bool)),
  length (MCE E T w0) >= E \/ MCE E T w0 = MCE (S E) T w0.
Proof.
  intros n E. induction E; intros.
  { left. auto. }
  assert (H := (IHE w0 T)).
  inversion H.
  { unfold MCE. destruct (inner_perceptron_MCE T w0) eqn:H1. destruct p as [L w].
      fold (MCE E T w). fold (MCE (S E) T w).
      destruct L. apply inner_perceptron_MCE_nil_false in H1; inversion H1.
      assert (H2 := (IHE w T)). inversion H2.
      { left. inversion H3. rewrite List.app_length.
        repeat (rewrite <- H4). simpl. omega.
        rewrite List.app_length. rewrite <- H4. simpl. omega.
      } right. rewrite H3. reflexivity.
    right. reflexivity.
  } right. apply MCE_S in H0. apply H0. Qed.