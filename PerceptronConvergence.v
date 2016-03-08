Require Import ZvecArith PerceptronDef.
Require Import TerminationRefinement MCEBounds.

Lemma mult_lt_preserve : forall (A B C: nat),
 A * C > B * C -> A > B.
Proof.
  intros A B C. induction C; intros. omega.
  repeat (rewrite Mult.mult_succ_r in H).
  simpl in H.
  omega. Qed.

Lemma mult_div_gt : forall (A B: nat),
  A <> 0 -> A * (NPeano.div B A) + A > B.
Proof.
  intros. destruct (NPeano.div B A) eqn:H1.
  apply NPeano.Nat.div_small_iff in H1. omega. omega.
  assert (H2 := (NPeano.Nat.div_mod B A) H).
  rewrite H2. rewrite H1. assert (HB: 0 <= B). omega.
  assert (HA : 0 < A). omega.
  assert (H3 := (NPeano.mod_bound_pos B A) HB HA). omega. Qed.

Lemma AB_limit : forall (A B C: nat),
  A <> 0 -> B <> 0 -> C > (NPeano.div B A) -> A * C * C > B * C.
Proof.
  intros. induction H1.
  { repeat (rewrite Mult.mult_succ_r). assert (H1 := (mult_div_gt A B) H).
    induction H1. destruct (NPeano.div B A). omega.
    repeat (rewrite Mult.mult_succ_r). simpl. omega.
    destruct (NPeano.div B A). omega.
    simpl. omega.
  } repeat (rewrite Mult.mult_succ_r).
  rewrite Mult.mult_plus_distr_r.
  assert (H2 := IHle). apply mult_lt_preserve in H2. omega. Qed.

 (****************************************************************************************
    Show that MCEBounds -> MCE reaches a fixed point.
  ****************************************************************************************)
Lemma linearly_separable_MCE : forall {n : nat} (w0 : Zvec (S n)) (T : list ((Zvec n)*bool)),
  linearly_separable T -> exists (E0 : nat),
  MCE E0 T w0 = MCE (S E0) T w0.
Proof.
  intros. apply (linearly_separable_bound T w0) in H. destruct H as [A [B [C H]]].
  exists (S (NPeano.div C A)).
  assert (H0 := (H (S (NPeano.div C A)))).
  assert (H1 := (MCE_progress (S (NPeano.div C A)) w0 T)).
  inversion H1.
  { unfold MCE in H2. inversion H2.
    { fold (MCE (S (NPeano.div C A)) T w0) in H4.
      fold (MCE (S (NPeano.div C A)) T w0) in H2. rewrite <- H4 in H0.
      assert (H3 := (AB_limit A C (S (NPeano.div C A)))).
      clear - H0 H3.
      omega.
    } 
    fold (MCE (S (NPeano.div C A)) T w0) in H2. fold (MCE (S (NPeano.div C A)) T w0) in H3.
    rewrite <- H3 in H0.
    assert (H5 := (AB_limit A C (S m))). clear -H0 H4 H5. omega.
  } apply H2. Qed.

 (****************************************************************************************
    Show that perceptron_MCE reaches a fixed point. (MCE fixed point + termination refinement)
  ****************************************************************************************)
Theorem linearly_separable_perceptron_MCE : forall {n : nat} (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  linearly_separable T -> exists (E0 : nat) M (w : (Zvec (S n))), forall E, E > E0 -> perceptron_MCE E T w0 = Some (M, w).
Proof.
  intros. apply linearly_separable_MCE with w0 T in H. destruct H as [E0 H].
  exists E0. exists (MCE E0 T w0). exists (Zvec_sum_class w0 (MCE E0 T w0)). intros E.
  intros H1. apply MCE_eq_perceptron_MCE in H. apply perceptron_MCE_done with (S E0). omega. apply H. Qed.

 (****************************************************************************************
  (Show that perceptron reaches a fixed point (converges)
    perceptron_MCE reaches a fixed point + termination refinement
 ****************************************************************************************)
Theorem linearly_separable_perceptron : forall {n : nat} (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  linearly_separable T -> exists (E0 : nat) (w : (Zvec (S n))), forall E, E > E0 -> perceptron E T w0 = Some w.
Proof.
  intros. apply linearly_separable_perceptron_MCE with w0 T in H.
  destruct H as [E0 [M [w H]]]. exists E0. exists w. intros. apply H in H0.
  apply perceptron_MCE_perceptron. exists M. auto. Qed.

Print Assumptions linearly_separable_perceptron.