Require Import ZvecArith PerceptronDef.

Lemma inner_perceptron_correct_class: forall {n: nat} (w : Zvec (S n)) (f : Zvec n) (l : bool) (T : (list ((Zvec n)*bool))),
 inner_perceptron ((f, l):: T) w = None -> correct_class (Zvec_dot w (consb f)) l = true.
Proof.
  intros n w f l T H. inversion H.
  destruct (correct_class (Zvec_dot w (consb f)) l) eqn:H2.
    reflexivity.
    destruct (inner_perceptron T (Zvec_plus w (Zvec_mult_class l (consb f)))); inversion H1. Qed.

Lemma inner_perceptron_correct_cons : forall {n: nat} (w : Zvec (S n)) (f : Zvec n) (l : bool) (T : (list ((Zvec n)*bool))),
 inner_perceptron ((f, l) :: T) w = None -> inner_perceptron T w = None.
Proof.
  intros n w f l T H. assert (H1 := H). apply inner_perceptron_correct_class in H1.
  inversion H. rewrite H1 in H2. rewrite H1. reflexivity. Qed.

Theorem inner_perceptron_correct_classified : forall {n : nat} (T : (list ((Zvec n)*bool))) (w : Zvec (S n)),
  inner_perceptron T w = None -> correctly_classifiedP T w.
Proof.
  intros n T w H. induction T.
  { constructor. } (* base case T = nil *)
  destruct a. constructor.
  apply IHT. apply inner_perceptron_correct_cons in H. apply H.
  apply inner_perceptron_correct_class in H. apply H. Qed.

Theorem correct_classified_inner_perceptron : forall {n : nat} (T : (list ((Zvec n)*bool))) (w : Zvec (S n)),
  correctly_classifiedP T w -> inner_perceptron T w = None.
Proof.
  intros n T w H. induction H.
  { reflexivity. } (* base case CCnil *)
  unfold inner_perceptron.
  destruct (correct_class (Zvec_dot w (consb f)) l).
    fold (inner_perceptron T' w). apply IHcorrectly_classifiedP.
    inversion H0. Qed.

Theorem inner_perceptron_not_correct_classified : forall {n : nat} (T : (list ((Zvec n)*bool))) (w w0: Zvec (S n)),
 inner_perceptron T w0 = Some w -> ~(correctly_classifiedP T w0).
Proof.
  intros n T w w0 H. unfold not. intros H0. induction H0.
  { inversion H. } (* base case T = nil *)
  apply IHcorrectly_classifiedP. inversion H.
  destruct (correct_class (Zvec_dot w0 (consb f)) l).
    reflexivity.
    inversion H1. Qed.

Theorem not_correct_classified_inner_perceptron: forall {n : nat} (T : (list ((Zvec n)*bool))) (w w0: Zvec (S n)),
  ~(correctly_classifiedP T w0) -> exists w, inner_perceptron T w0 = Some w.
Proof.
  intros n T w w0 H. unfold not in H. induction T.
  { exfalso. apply H. constructor. }
  destruct a as [x l]. unfold inner_perceptron.
  destruct (correct_class (Zvec_dot w0 (consb x)) l) eqn:H2.
    fold (inner_perceptron T w0). apply IHT. intros H1. apply H. constructor. apply H1. apply H2.
    fold (inner_perceptron T (Zvec_plus w0 (Zvec_mult_class l (consb x)))).
    destruct (inner_perceptron T (Zvec_plus w0 (Zvec_mult_class l (consb x)))).
    exists z. reflexivity. exists (Zvec_plus w0 (Zvec_mult_class l (consb x))). reflexivity. Qed.

(***********************************************************************************************
   Soundness Proof (ie. If the Perceptron Converges to Some W then W is a linear separater of T)
   and its contrapositive. (ie If T is not linear separable then Perceptron will never
   converge on Some w (always returns None).
 ***********************************************************************************************)

Theorem perceptron_linearly_separable : forall {n : nat } (E: nat) (w0 w : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  perceptron E T w0 = Some w -> linearly_separable T.
Proof.
  intros n E. induction E; intros w0 w T H.
  { inversion H. } (* base case E = 0 *)
  unfold perceptron in H. 
  fold (perceptron E T w0) in IHE.
  destruct (inner_perceptron T w0) eqn: H1.
    fold (perceptron E T z) in H. apply IHE in H. apply H.
    apply inner_perceptron_correct_classified in H1. unfold linearly_separable.
      exists w0. apply H1. Qed.

Theorem not_linearly_seperable_perceptron : forall {n : nat} (E : nat) (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  ~(linearly_separable T) -> perceptron E T w0 = None.
Proof.
  intros n E. induction E; intros w0 T H.
  { reflexivity. } (* base case E = 0 *)
  unfold perceptron.
  destruct (inner_perceptron T w0) eqn: H1.
  fold (perceptron E T z). apply (IHE z) in H. apply H.
  unfold not in H. exfalso. apply H. apply inner_perceptron_correct_classified in H1.
  unfold linearly_separable. exists w0. apply H1. Qed.