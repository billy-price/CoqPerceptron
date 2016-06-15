Require Import QvecArith PerceptronDef.

Lemma inner_perceptron_correct_class: forall {n: nat} (w : Qvec (S n)) (f : Qvec n) (l : bool) (T : (list ((Qvec n)*bool))),
 inner_perceptron ((f, l):: T) w = None -> correct_class (Qvec_dot w (consb f)) l = true.
Proof.
  intros n w f l T H. inversion H.
  destruct (correct_class (Qvec_dot w (consb f)) l) eqn:H2.
    reflexivity.
    destruct (inner_perceptron T (Qvec_plus w (Qvec_mult_class l (consb f)))); inversion H1. Qed.

Lemma inner_perceptron_correct_cons : forall {n: nat} (w : Qvec (S n)) (f : Qvec n) (l : bool) (T : (list ((Qvec n)*bool))),
 inner_perceptron ((f, l) :: T) w = None -> inner_perceptron T w = None.
Proof.
  intros n w f l T H. assert (H1 := H). apply inner_perceptron_correct_class in H1.
  inversion H. rewrite H1 in H2. rewrite H1. reflexivity. Qed.

Theorem inner_perceptron_correct_classified : forall {n : nat} (T : (list ((Qvec n)*bool))) (w : Qvec (S n)),
  inner_perceptron T w = None -> correctly_classifiedP T w.
Proof.
  intros n T w H. induction T.
  { constructor. } (* base case T = nil *)
  destruct a. constructor.
  apply IHT. apply inner_perceptron_correct_cons in H. apply H.
  apply inner_perceptron_correct_class in H. apply H. Qed.

Theorem correct_classified_inner_perceptron : forall {n : nat} (T : (list ((Qvec n)*bool))) (w : Qvec (S n)),
  correctly_classifiedP T w -> inner_perceptron T w = None.
Proof.
  intros n T w H. induction H.
  { reflexivity. } (* base case CCnil *)
  unfold inner_perceptron.
  destruct (correct_class (Qvec_dot w (consb f)) l).
    fold (inner_perceptron T' w). apply IHcorrectly_classifiedP.
    inversion H0. Qed.

Theorem inner_perceptron_not_correct_classified : forall {n : nat} (T : (list ((Qvec n)*bool))) (w w0: Qvec (S n)),
 inner_perceptron T w0 = Some w -> ~(correctly_classifiedP T w0).
Proof.
  intros n T w w0 H. unfold not. intros H0. induction H0.
  { inversion H. } (* base case T = nil *)
  apply IHcorrectly_classifiedP. inversion H.
  destruct (correct_class (Qvec_dot w0 (consb f)) l).
    reflexivity.
    inversion H1. Qed.

Theorem not_correct_classified_inner_perceptron: forall {n : nat} (T : (list ((Qvec n)*bool))) (w w0: Qvec (S n)),
  ~(correctly_classifiedP T w0) -> exists w, inner_perceptron T w0 = Some w.
Proof.
  intros n T w w0 H. unfold not in H. induction T.
  { exfalso. apply H. constructor. }
  destruct a as [x l]. unfold inner_perceptron.
  destruct (correct_class (Qvec_dot w0 (consb x)) l) eqn:H2.
    fold (inner_perceptron T w0). apply IHT. intros H1. apply H. constructor. apply H1. apply H2.
    fold (inner_perceptron T (Qvec_plus w0 (Qvec_mult_class l (consb x)))).
    destruct (inner_perceptron T (Qvec_plus w0 (Qvec_mult_class l (consb x)))).
    exists q. reflexivity. exists (Qvec_plus w0 (Qvec_mult_class l (consb x))). reflexivity. Qed.

(***********************************************************************************************
   Soundness Proof (ie. If the Perceptron Converges to Some W then W is a linear separater of T)
   and its contrapositive. (ie If T is not linear separable then Perceptron will never
   converge on Some w (always returns None).
 ***********************************************************************************************)

Theorem perceptron_linearly_separable : forall {n : nat } (E: nat) (w0 w : Qvec (S n)) (T : (list ((Qvec n)*bool))),
  perceptron E T w0 = Some w -> linearly_separable T.
Proof.
  intros n E. induction E; intros w0 w T H.
  { inversion H. } (* base case E = 0 *)
  unfold perceptron in H. 
  fold (perceptron E T w0) in IHE.
  destruct (inner_perceptron T w0) eqn: H1.
    fold (perceptron E T q) in H. apply IHE in H. apply H.
    apply inner_perceptron_correct_classified in H1. unfold linearly_separable.
      exists w0. apply H1. Qed.

Theorem not_linearly_seperable_perceptron : forall {n : nat} (E : nat) (w0 : Qvec (S n)) (T : (list ((Qvec n)*bool))),
  ~(linearly_separable T) -> perceptron E T w0 = None.
Proof.
  intros n E. induction E; intros w0 T H.
  { reflexivity. } (* base case E = 0 *)
  unfold perceptron.
  destruct (inner_perceptron T w0) eqn: H1.
  fold (perceptron E T q). apply (IHE q) in H. apply H.
  unfold not in H. exfalso. apply H. apply inner_perceptron_correct_classified in H1.
  unfold linearly_separable. exists w0. apply H1. Qed. 