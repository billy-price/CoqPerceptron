Require Import Coq.Vectors.Vector.
Require Import ZArith.
Require Import Omega.

Definition Zvec := Vector.t Z. 
Definition Zvec_plus {n:nat} (v1 v2 : Zvec n) := map2 Zplus v1 v2.
Definition Zvec_dot {n:nat} (v1 v2 : Zvec n) := fold_left Zplus Z0 (map2 Zmult v1 v2).
Definition Zvec_normsq {n:nat} (v1 : Zvec n) := Zvec_dot v1 v1.
Definition Zvec_mult_class {n:nat} (l :bool) (f : Zvec n) := if l then f else map (Zmult (Zneg 1)) f.
Definition class (i : Z) : bool := Z.geb i Z0.
Definition correct_class (i : Z) (l : bool) : bool :=
  andb (Bool.eqb l (class i)) (negb (Z.eqb i Z0)).
Definition consb {n : nat} (v : Zvec n) := cons _ (Zpos 1) _ v.
Definition Zvec_zero (n : nat) : Zvec n := const Z0 n.

(************************************************************************************************
   W should be a vector of size 1 more than a feature vector.
   consb ensures that a feature vector becomes <1, x1, x2, ..., xn>
   to handle the bias term stored in the 0th index of W.
 ************************************************************************************************)
Fixpoint Zvec_sum_class {n : nat} (w : Zvec (S n)) (M : list ((Zvec n)*bool)) : Zvec (S n) :=
  match M with
  | List.nil => w
  | List.cons (f, l) M' => Zvec_sum_class (Zvec_plus w (Zvec_mult_class l (consb f))) M'
  end.

Fixpoint Zvec_sum {n : nat} (M : list ((Zvec n)*bool)) : Zvec (S n) :=
  match M with
  | List.nil => Zvec_zero (S n)
  | List.cons (f, l) M' => Zvec_plus (Zvec_mult_class l (consb f)) (Zvec_sum M')
  end.
 
Fixpoint min_element_product {n : nat} (w : Zvec (S n)) (T: list ((Zvec n)*bool)) : Z :=
  match T with
  | List.nil => (Zpos 1) (* avoid divide by zero *)
  | List.cons (f, l) List.nil => Zvec_dot w (Zvec_mult_class l (consb f))
  | List.cons (f, l) T' =>
      if (Z.leb (Zvec_dot w (Zvec_mult_class l (consb f))) (min_element_product w T'))
      then (Zvec_dot w (Zvec_mult_class l (consb f)))
      else (min_element_product w T')
  end.

Fixpoint max_element_normsq {n : nat} (T: list ((Zvec n)*bool)) : Z :=
  match T with
  | List.nil => (Zpos 1)
  | List.cons (f, l) List.nil => (Zvec_normsq (consb f))
  | List.cons (f, l) T' =>
      if (Z.geb (Zvec_normsq (consb f)) (max_element_normsq T'))
      then (Zvec_normsq (consb f))
      else (max_element_normsq T')
  end.

Fixpoint Zvec_sum_normsq {n:nat} (L: list ((Zvec n)*bool)) : Z :=
  match L with
  | List.nil => Z0
  | List.cons (f, l) L' => Z.add (Zvec_normsq (consb f)) (Zvec_sum_normsq L')
  end.

Fixpoint Zvec_sum_dot {n:nat} (w : Zvec (S n)) (L: list ((Zvec n)*bool)) : Z :=
  match L with
  | List.nil => Z0
  | List.cons (f, l) L' => Z.add (Zvec_dot w (Zvec_mult_class l (consb f))) (Zvec_sum_dot w L')
  end.

Fixpoint Zvec_foil {n:nat} (w : Zvec (S n)) (L: list ((Zvec n)*bool)) : Z :=
  match L with
  | List.nil => Z0
  | List.cons (f, l) L' => Z.add (Zvec_dot w (Zvec_mult_class l (consb f)))
                                 (Zvec_foil (Zvec_plus w (Zvec_mult_class l (consb f))) L')
  end.

Fixpoint inner_perceptron {n:nat} (T: list ((Zvec n)*bool)) (w:Zvec (S n)) : option (Zvec (S n)) := 
  match T with
  | List.nil => None
  | List.cons (f, l) T' =>
      match correct_class (Zvec_dot w (consb f)) l with 
      | true => inner_perceptron T' w
      | false =>
         match inner_perceptron T' (Zvec_plus w (Zvec_mult_class l (consb f))) with
         | None => Some (Zvec_plus w (Zvec_mult_class l (consb f)))
         | Some w' => Some w'
         end
      end
  end. 

Fixpoint perceptron {n:nat} (E:nat) (T: list ((Zvec n)*bool)) (w : Zvec (S n)) : option (Zvec (S n)) :=
  match E with
  | 0 => None
  | S E' => 
      match (inner_perceptron T w) with
      | None => Some w
      | Some w' => perceptron E' T w'
      end
  end.

Definition wZero := (cons Z (Z0) 2 (cons Z (Z0) 1 (cons Z (Z0) 0 (nil Z)))).
Definition wop := (cons Z (Zneg 1) 2 (cons Z (Z0) 1 (cons Z (Zpos 2) 0 (nil Z)))).
Definition x1 := (cons Z (Z0) 1 (cons Z (Z0) 0 (nil Z))).
Definition x2 := (cons Z (Z0) 1 (cons Z (Zpos 1) 0 (nil Z))).
Definition train := (List.cons (x1, false) (List.cons (x2, true) List.nil)). 

Example test_perceptron: perceptron 4 train wZero = Some wop.
Proof. reflexivity. Qed.

Fixpoint correctly_classified {n: nat} (T: list ((Zvec n)*bool)) (w : Zvec (S n)) : bool :=
  match T with
  | List.nil => true
  | List.cons (f, l) T' =>
    match correct_class (Zvec_dot w (consb f)) l with
    | true => correctly_classified T' w
    | false => false
    end
  end.

Inductive correctly_classifiedP {n : nat} : (list ((Zvec n)*bool))->(Zvec (S n))->Prop :=
| CCnil  : forall (w : (Zvec (S n))), correctly_classifiedP List.nil w
| CCcons : forall (w : (Zvec (S n))) (T' : (list ((Zvec n)*bool))) f l,
           correctly_classifiedP T' w -> correct_class (Zvec_dot w (consb f)) l = true -> correctly_classifiedP ((f,l)::T') w.

Definition correctly_classifiedP' {n : nat} : list (Zvec n*bool)-> Zvec (S n) -> Prop :=
  fun T w =>
    List.Forall (fun xl : (Zvec n * bool) =>
                   let (x, l) := xl in correct_class (Zvec_dot w (consb x)) l = true) T.

Lemma correctly_classifiedPP' n (T : list (Zvec n*bool)) w :
  correctly_classifiedP T w <-> correctly_classifiedP' T w.
Proof.
  split; intros H; induction H; try econstructor; eauto.
  destruct x; simpl in *; constructor; auto.
Qed.  

Definition linearly_separable {n: nat} (T : (list ((Zvec n)*bool))) : Prop :=
  exists (w : (Zvec (S n))), correctly_classifiedP T w.

Example lin_sep_test : linearly_separable train.
Proof.
  unfold linearly_separable. exists wop. repeat constructor.
Qed.

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
                     Our final Goal is to do something along the following

   Forall T W0 E, Linearly Separable T <-> exists W E0, E >= E0 -> perceptron E T W0 = Some w.
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

Fixpoint IPOL {n:nat} (T:list ((Zvec n) * (bool))) (w: Zvec (S n)) : option ((list ((Zvec n)*bool))*(Zvec (S n))) := 
  match T with
  | List.nil => None
  | List.cons (f, l) T' =>
      match correct_class (Zvec_dot w (consb f)) l with
      | true => IPOL T' w
      | false =>
         match IPOL T' (Zvec_plus w (Zvec_mult_class l (consb f))) with
         | None => Some ((List.cons (f, l) List.nil), (Zvec_plus w (Zvec_mult_class l (consb f))))
         | Some (L, w') => Some ((List.cons (f, l) L), w')
         end
      end
  end.

Fixpoint POL {n:nat} (E:nat) (T:list ((Zvec n) * (bool))) (w : Zvec (S n)) : option((list ((Zvec n)*bool))*(Zvec (S n))) :=
  match E with
  | 0 => None
  | S E' =>
      match (IPOL T w) with
      | None => Some (List.nil, w)
      | Some (L, w') =>
        match POL E' T w' with
        | None => None
        | Some (L', w'') => Some ((List.app L L'), w'')
        end
      end
  end.

Fixpoint MCE {n: nat} (E : nat) (T: list ((Zvec n)*bool)) (w : Zvec (S n)) : (list ((Zvec n)*bool)) :=
  match E with
  | 0 => List.nil
  | S E' =>
    match (IPOL T w) with
    | None => List.nil
    | Some (L, w') => (List.app L (MCE E' T w'))
    end
  end.

(********************************************************************************************
    Proof that if POL converges it does so with a misclassified list equivalent to the list
    produced by MCE on the same arguments.
 ********************************************************************************************)
Lemma POL_MCE : forall {n : nat} (E : nat) (T M : list ((Zvec n)*bool)) (w0 w : Zvec (S n)),
  POL E T w0 = Some (M, w) -> MCE E T w0 = M.
Proof.
  intros n E. induction E; intros.
  { inversion H. } (* base case *)
  inversion H. unfold MCE. destruct (IPOL T w0).
  destruct p as [L w']. fold (MCE E T w'). destruct (POL E T w') eqn:H2.
  destruct p as [L' w'']. apply IHE in H2. rewrite H2.
  inversion H1; subst; clear H1; auto. inversion H1.
  inversion H1; subst; clear H1; auto. Qed.

Theorem IPOL_inner_perceptron_None : forall {n : nat} T (w0: Zvec (S n)),
  IPOL T w0 = None <-> inner_perceptron T w0 = None.
Proof.
  split; generalize dependent w0; induction T; intros w0 H.
  reflexivity. destruct a as [f l].
  inversion H. unfold inner_perceptron. destruct (correct_class (Zvec_dot w0 (consb f)) l) eqn: H2.
  fold (inner_perceptron T w0). apply IHT in H1. apply H1.
  destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))).  destruct p. inversion H1. inversion H1.
  reflexivity. destruct a as [f l].
  inversion H. unfold IPOL. destruct (correct_class (Zvec_dot w0 (consb f)) l).
  fold (IPOL T w0). apply IHT in H1. apply H1.
  destruct (inner_perceptron T (Zvec_plus w0 (Zvec_mult_class l (consb f)))). inversion H1. inversion H1. Qed.

Theorem IPOL_inner_perceptron : forall {n : nat} T (w0 w : Zvec (S n)),
  (exists M, IPOL T w0 = Some (M, w)) <-> inner_perceptron T w0 = Some w.
Proof.
  split; generalize dependent w0; generalize dependent w;
  induction T; intros; [destruct H as [M H]|destruct H as [M H]| |].
  { inversion H. } (* base case T = nil *)
  destruct a as [f l]. inversion H. unfold inner_perceptron.
  destruct (correct_class (Zvec_dot w0 (consb f)) l) eqn:H2.
  fold (inner_perceptron T w0). apply IHT. exists M. apply H1.
  fold (inner_perceptron T (Zvec_plus w0 (Zvec_mult_class l (consb f)))).
  destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H3.
  destruct p as [L w']. assert (H4: inner_perceptron T (Zvec_plus w0 (Zvec_mult_class l (consb f))) = Some w').
  apply IHT. exists L. apply H3. rewrite H4. inversion H1; subst; auto.
  apply IPOL_inner_perceptron_None in H3.
  rewrite H3. inversion H1; subst; auto.
  { inversion H. } (* base case T = nil *)
  destruct a as [f l]. inversion H. unfold IPOL. destruct (correct_class (Zvec_dot w0 (consb f)) l) eqn: H6.
  fold (IPOL T w0). apply IHT with w w0 in H1. apply H1.
  destruct (inner_perceptron T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H2.
  inversion H1; subst. fold (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))).
  apply IHT in H2. destruct H2 as [M H2]. rewrite H2. exists (List.cons (f, l) M). auto.
  fold (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))). apply IPOL_inner_perceptron_None in H2.
  rewrite H2. exists (List.cons (f,l) List.nil). inversion H1; subst. auto. Qed.

(******************************************************************************************
   Proof that POL and Perceptron both produce the same weight vector if they converge
   (if one converges so will the other)
 ******************************************************************************************)
Theorem POL_perceptron : forall {n : nat} (E : nat) T (w0 w : Zvec (S n)),
  (exists M, POL E T w0 = Some (M, w)) <-> perceptron E T w0 = Some w.
Proof.
  split; generalize dependent T; generalize dependent w0;
  generalize dependent w; induction E; intros;
  [destruct H as [M H]| destruct H as [M H]| |].
  { inversion H. } (* base case E = 0 *)
  inversion H. unfold perceptron. destruct (IPOL T w0) eqn:H2.
  destruct p as [L w']. assert (H3: inner_perceptron T w0 = Some w').
  apply IPOL_inner_perceptron. exists L. apply H2. rewrite H3.
  fold (perceptron E T w'). destruct (POL E T w') eqn:H4.
  apply IHE. destruct p as [L' w'']. exists L'. inversion H1; subst.
  apply H4. inversion H1. apply IPOL_inner_perceptron_None in H2. rewrite H2.
  inversion H1; subst. auto.
  { inversion H. } (* base case E = 0 *)
  inversion H. destruct (inner_perceptron T w0) eqn:H2. apply IHE in H1.
  destruct H1 as [M H1]. unfold POL. apply IPOL_inner_perceptron in H2.
  destruct H2 as [M' H2]. rewrite H2. fold (POL E T z). rewrite H1. exists (List.app M' M). auto.
  inversion H1; subst; clear H1. apply IPOL_inner_perceptron_None in H2.
  unfold POL. rewrite H2. exists List.nil. auto. Qed.

Lemma IPOL_sum_m_w : forall {n : nat} (T M: (list ((Zvec n)*bool))) (w0 w: Zvec (S n)),
  IPOL T w0 = Some (M, w) -> w = Zvec_sum_class w0 M.
Proof.
  intros n T. induction T; intros.
  { inversion H. } (* base case T = nil *)
  destruct a as [f l]. inversion H. destruct (correct_class (Zvec_dot w0 (consb f)) l).
  apply IHT in H1. apply H1. destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H3;
  [destruct p as [M' w']; apply IHT in H3|]; inversion H1; subst; clear H1; auto. Qed.

Lemma Zvec_sum_class_append : forall {n : nat} (w0: Zvec (S n)) (M1 M2: (list ((Zvec n)*bool))),
  Zvec_sum_class (Zvec_sum_class w0 M1) M2 = Zvec_sum_class w0 (List.app M1 M2).
Proof.
  intros n w0 M1. generalize dependent w0. induction M1; intros.
  { auto. } destruct a as [f l]. simpl. apply IHM1. Qed.

(**********************************************************************************************
   Proof that if POL converges then w = the sumation of elements of m + w0
   where m are the misclassified elements.
 **********************************************************************************************)
Lemma POL_sum_m_w : forall {n : nat} (E : nat) (T M: (list ((Zvec n)*bool))) (w0 w: Zvec (S n)),
  POL E T w0 = Some (M, w) -> w = Zvec_sum_class w0 M.
Proof.
  intros n E. induction E; intros.
  { inversion H. } (* base case *)
  inversion H. destruct (IPOL T w0) eqn:H2. destruct p as [M' w'].
  apply IPOL_sum_m_w in H2. destruct (POL E T w') eqn: H3. destruct p as [M'' W''].
  inversion H1; subst; clear H1. apply IHE in H3. rewrite Zvec_sum_class_append in H3. apply H3.
  inversion H1. inversion H1; subst; clear H1. auto. Qed.

Theorem POL_S : forall {n : nat} (E : nat) (w w0 : Zvec (S n)) (T M : list ((Zvec n)*bool)),
  POL E T w0 = Some (M, w) -> POL (S E) T w0 = Some (M, w).
Proof.
  intros n E. induction E; intros.
  { inversion H. } (* Base Case E = 0 *)
  simpl in H. simpl.
  destruct (IPOL T w0). destruct p as [L w'].
  destruct (POL E T w') eqn: H1. destruct p as [L' w''].
  apply IHE in H1. simpl in H1.
  destruct (IPOL T w'). destruct p as [L'' w'''].
  destruct (POL E T w'''). destruct p as [L''' w''''].
  inversion H1; subst; clear H1. apply H. inversion H1.
  inversion H1; subst; clear H1. apply H. inversion H. apply H. Qed.

Lemma POL_done : forall {n : nat} (E0 E : nat) (w w0 : Zvec (S n)) (T M : list ((Zvec n)*bool)),
  E >= E0 -> POL E0 T w0 = Some (M, w) -> POL E T w0 = Some (M, w).
Proof.
  intros. induction H. apply H0.
  apply POL_S in IHle. apply IHle. Qed.

Lemma IPOL_nil_false : forall {n: nat} (w0 w: Zvec (S n)) (T : list ((Zvec n)*bool)),
  IPOL T w0 = Some (List.nil, w) -> False.
Proof.
  intros n w0 w T. revert w w0. induction T; intros; inversion H.
  destruct a as [f l].
  destruct (correct_class (Zvec_dot w0 (consb f)) l).
    apply IHT in H1; inversion H1.
    destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f))));
    [destruct p as [L w']| ]; inversion H1. Qed.

Lemma MCE_S : forall {n : nat} (E : nat) (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
  MCE E T w0 = MCE (S E) T w0 -> MCE (S E) T w0 = MCE (S (S E)) T w0.
Proof.
  intros n E. induction E; intros.
  rewrite <- H. simpl. simpl in H.
  destruct (IPOL T w0) eqn:H0. destruct p as [L w].
    destruct L; [apply IPOL_nil_false in H0; inversion H0 | inversion H].
    reflexivity.
  unfold MCE in H. destruct (IPOL T w0) eqn:H1. destruct p as [L w].
  fold (MCE E T w) in H. fold (MCE (S E) T w) in H.
  apply List.app_inv_head in H. apply IHE in H.
  unfold MCE. rewrite H1. fold (MCE (S E) T w). fold (MCE (S (S E)) T w).
  rewrite H. reflexivity.
  simpl. rewrite H1. reflexivity. Qed.

Lemma MCE_done : forall {n : nat} (E0 E : nat) (w0 : Zvec (S n)) (T : list ((Zvec n)*bool)),
  E >= E0 -> MCE E0 T w0 = MCE (S E0) T w0 -> MCE E0 T w0 = MCE E T w0.
Proof.
  intros. revert dependent w0. revert dependent T. induction H; intros.
  reflexivity. assert (H1 := H0).
  apply IHle in H0. rewrite H1.
  simpl. destruct (IPOL T w0) eqn:H2. destruct p as [L w].
  assert (H3: (MCE E0 T w) = (MCE (S E0) T w)).
    destruct E0. simpl in H1. rewrite H2 in H1.
    destruct L. apply IPOL_nil_false in H2. inversion H2. inversion H1.
    unfold MCE in H1. rewrite H2 in H1. fold (MCE E0 T w) in H1.
    fold (MCE (S E0) T w) in H1. apply List.app_inv_head in H1.
    apply MCE_S in H1. apply H1.
  apply IHle in H3. rewrite H3. reflexivity. reflexivity. Qed.

Lemma MCE_eq_POL : forall {n : nat} (E : nat) (w0 : Zvec (S n)) (T : list ((Zvec n)*bool)),
 MCE E T w0 = MCE (S E) T w0 ->
 POL (S E) T w0 = Some ((MCE E T w0), Zvec_sum_class w0 (MCE E T w0)).
Proof.
  intros n E. induction E; intros.
  simpl in H. destruct (IPOL T w0) eqn:H1.
    destruct p as [L w']. destruct L.
      apply IPOL_nil_false in H1; inversion H1.
      inversion H.
    simpl; rewrite H1. auto.
  unfold MCE in H. destruct (IPOL T w0) eqn:H1.
  destruct p as [L w']. fold (MCE E T w') in H.
  fold (MCE (S E) T w') in H. apply List.app_inv_head in H.
  apply IHE in H. simpl. rewrite H1. simpl in H. rewrite H.
  apply IPOL_sum_m_w in H1. rewrite H1.
  rewrite Zvec_sum_class_append. auto.
  simpl. rewrite H1. auto. Qed.

Lemma AplusB_AplusC : forall (A B C : nat),
  A + B = A + C -> B = C.
Proof.
  intros A. induction A; intros.
  simpl in H; auto.
  inversion H. apply IHA in H1. apply H1. Qed.

Lemma MCE_eq_length : forall {n : nat} (E1 E2 : nat) (w0 : Zvec (S n)) (T : list ((Zvec n)*bool)),
  length (MCE E1 T w0) = length (MCE E2 T w0) -> (MCE E1 T w0) = (MCE E2 T w0).
Proof.
  intros n E1. induction E1; intros.
{ simpl. simpl in H. destruct (MCE E2 T w0). auto. inversion H. } (* Base Case *)
  simpl in H. destruct (IPOL T w0) eqn:H1.
  { destruct p as [L w]. destruct E2. simpl in H.
    { destruct L. apply IPOL_nil_false in H1. inversion H1. inversion H. }
    simpl in H. rewrite H1 in H. rewrite List.app_length in H. rewrite List.app_length in H.
    apply AplusB_AplusC in H. apply IHE1 in H. simpl. rewrite H1. rewrite H. auto.
  }
  simpl in H. destruct E2; simpl; rewrite H1; auto. Qed.

Lemma MCE_progress : forall {n : nat} (E : nat) (w0 : Zvec (S n)) (T : list ((Zvec n)*bool)),
  length (MCE E T w0) >= E \/ MCE E T w0 = MCE (S E) T w0.
Proof.
  intros n E. induction E; intros.
  { left. auto. }
  assert (H := (IHE w0 T)).
  inversion H.
  { unfold MCE. destruct (IPOL T w0) eqn:H1. destruct p as [L w].
      fold (MCE E T w). fold (MCE (S E) T w).
      destruct L. apply IPOL_nil_false in H1; inversion H1.
      assert (H2 := (IHE w T)). inversion H2.
      { left. inversion H3. rewrite List.app_length.
        repeat (rewrite <- H4). SearchAbout List.length.
        simpl. omega.
        rewrite List.app_length. rewrite <- H4. simpl. omega.
      } right. rewrite H3. reflexivity.
    right. reflexivity.
  } right. apply MCE_S in H0. apply H0. Qed.

(**************************************************************************************************
         This section will be for reasoning about operations on Zvecs and thier properties
 **************************************************************************************************)
Definition Vector_0_is_nil {A} (v : t A 0) : v = nil A :=
match v with
| nil => eq_refl
end.

Definition Vector_S_is_cons {A} {n} (v: t A (S n)) : exists a, exists v0, v = cons A a n v0 :=
match v as v' in t _ n1
  return match n1 return t A n1 -> Prop with
  |0 => fun _ => True
  |S n => fun v => exists a, exists v0, v = cons A a n v0 end v' with
| nil => I
| cons a _ v0 => ex_intro _ a (ex_intro _ v0 (refl_equal _))
end.

Lemma mutual_induction : forall {A B: Type} (P : forall {n : nat}, t A n -> t B n -> Prop),
  (P (nil A) (nil B)) -> (forall (h1 : A) (h2 : B) {n : nat} (t1 : t A n) (t2 : t B n),
  (P t1 t2) -> (P (cons A h1 n t1) (cons B h2 n t2))) ->
  forall {n : nat} (v1 : t A n) (v2 : t B n), P v1 v2.
Proof.
  intros. induction n. rewrite (Vector_0_is_nil v1). rewrite (Vector_0_is_nil v2). apply H.
  assert (H1 := Vector_S_is_cons v1). assert (H2 := Vector_S_is_cons v2).
  destruct H1 as [a [v1' H1]]. destruct H2 as [b [v2' H2]]. rewrite H1. rewrite H2. apply H0. apply IHn. Qed.

Lemma triple_induction : forall {A B C: Type} (P : forall {n : nat}, t A n -> t B n -> t C n-> Prop),
  (P (nil A) (nil B) (nil C)) -> (forall (h1 : A) (h2 : B) (h3 : C) {n : nat} (t1 : t A n) (t2 : t B n) ( t3 : t C n),
  (P t1 t2 t3) -> (P (cons A h1 n t1) (cons B h2 n t2) (cons C h3 n t3))) ->
  forall {n : nat} (v1 : t A n) (v2 : t B n) (v3 : t C n), P v1 v2 v3.
Proof.
  intros. induction n. rewrite (Vector_0_is_nil v1). rewrite (Vector_0_is_nil v2). rewrite (Vector_0_is_nil v3). apply H.
  assert (H1 := Vector_S_is_cons v1). assert (H2 := Vector_S_is_cons v2). assert (H3 := Vector_S_is_cons v3).
  destruct H1 as [a [v1' H1]]. destruct H2 as [b [v2' H2]]. destruct H3 as [c [v3' H3]]. rewrite H1. rewrite H2. rewrite H3.
  apply H0. apply IHn. Qed.

Lemma fold_left_add_unfold : forall {n : nat} (v1 v2 : Zvec n) (A : Z),
 fold_left Z.add A (map2 Z.mul v1 v2) = Z.add A (fold_left Z.add Z0 (map2 Z.mul v1 v2)).
Proof.
  intros n v1 v2. set (P := fun {n : nat} (v1 v2 : Zvec n) => forall A : Z,
  fold_left Z.add A (map2 Z.mul v1 v2) = Z.add A (fold_left Z.add Z0 (map2 Z.mul v1 v2))).
  change (P n v1 v2). apply mutual_induction; unfold P; intros. apply Zplus_0_r_reverse. simpl. rewrite H.
  assert (fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2) = Z.add (Z.mul h1 h2) (fold_left Z.add Z0 (map2 Z.mul t1 t2))).
    apply H. rewrite H0. rewrite Z.add_assoc. reflexivity. Qed.

Lemma fold_left_add_unfold_1 : forall {n : nat} (v1 v2 : Zvec n) (A : Z),
 fold_left Z.add (Z.add 1 A) (map2 Z.mul v1 v2) = Z.add A (fold_left Z.add (Z.pos 1) (map2 Z.mul v1 v2)).
Proof.
  intros. rewrite Z.add_comm. rewrite fold_left_add_unfold. rewrite <- Z.add_assoc.
  rewrite <- fold_left_add_unfold. reflexivity. Qed.

Lemma Zvec_consb_gt_0 : forall {n : nat} (f : Zvec n),
 Z.gt (Zvec_normsq (consb f)) Z0.
Proof.
  intros n f. unfold Zvec_normsq. unfold Zvec_dot. unfold consb. simpl.
  induction f. simpl. omega.
  simpl. destruct (Z.mul h h) eqn:H0.
    apply IHf.
  { destruct p.
    assert (H1: (Z.pos (Pos.succ p)~0) = (Z.add 1 (Z.pos p~1))).
      simpl. reflexivity.
    rewrite H1. rewrite fold_left_add_unfold_1.
    assert (H2 := Zsgn_spec (Z.pos p~1)). inversion H2; inversion H;
    [omega | inversion H3; inversion H5 | inversion H3; inversion H5].
    assert (H1: (Z.pos p~1) = (Z.add (Z.pos 1) (Z.pos p~0))).
      simpl. reflexivity.
    rewrite H1. rewrite fold_left_add_unfold_1.
    assert (H2 := Zsgn_spec (Z.pos p~1)). inversion H2; inversion H;
    [omega | inversion H3; inversion H5 | inversion H3; inversion H5].
    assert (H1: (Z.pos 2) = (Z.add (Z.pos 1) (Z.pos 1))).
      reflexivity.
    rewrite H1. rewrite fold_left_add_unfold_1. omega.
  } destruct h; inversion H0. Qed.

Lemma Zvec_normsq_not_neg : forall {n : nat} (f : Zvec n),
 Z.le Z0 (Zvec_normsq f).
Proof.
  intros. induction f. unfold Zvec_normsq, Zvec_dot. reflexivity.
  unfold Zvec_normsq, Zvec_dot. simpl.
  destruct h eqn:H. apply IHf. rewrite fold_left_add_unfold.
  destruct (fold_left Z.add Z0 (map2 Z.mul f f)) eqn:H0; simpl; try(apply Zle_0_pos).
  unfold Zvec_normsq, Zvec_dot in IHf; rewrite H0 in IHf. assert (H1 := (Zlt_neg_0 p0)). omega.
  simpl. rewrite fold_left_add_unfold.
  destruct (fold_left Z.add Z0 (map2 Z.mul f f)) eqn:H0; simpl; try(apply Zle_0_pos).
  unfold Zvec_normsq, Zvec_dot in IHf; rewrite H0 in IHf. assert (H1 := (Zlt_neg_0 p0)). omega. Qed.

Lemma Zvec_sum_normsq_ge_0 : forall {n : nat} (L : list ((Zvec n)*bool)),
  Z.le Z0 (Zvec_sum_normsq L).
Proof.
  intros. induction L.
  simpl. omega.
  destruct a as [f l]. simpl. assert (H := Zvec_normsq_not_neg (consb f)). omega. Qed.

Lemma Zvec_normsq_zvec_zero : forall (n : nat),
 Zvec_normsq (Zvec_zero n) = Z0.
Proof.
  intros n. induction n. unfold Zvec_zero, Zvec_normsq, Zvec_dot. reflexivity.
  unfold Zvec_zero, Zvec_normsq, Zvec_dot. simpl. apply IHn. Qed.

Lemma normsq_mult_neg_1_same : forall {n : nat} (f : Zvec n),
  Zvec_normsq f = Zvec_normsq (map (Z.mul (-1)) f).
Proof.
  intros. induction f. simpl. reflexivity.
  unfold Zvec_normsq, Zvec_dot. unfold Zvec_normsq, Zvec_dot in IHf.
  simpl. destruct h; try (apply IHf); simpl; try (rewrite fold_left_add_unfold;
  rewrite IHf; rewrite <- fold_left_add_unfold; auto). Qed.

Lemma Zvec_dot_mult_neg_1 : forall {n:nat} (v1 v2 : Zvec n),
  Zvec_dot v1 (map (Z.mul (Z.neg 1)) v2) = Z.mul (Z.neg 1) (Zvec_dot v1 v2).
Proof.
  intros n v1 v2. set (P := fun (n : nat) (v1 v2 : t Z n) => Zvec_dot v1 (map (Z.mul (Z.neg 1)) v2) =
  Z.mul (Z.neg 1) (Zvec_dot v1 v2)). change (P n v1 v2). apply mutual_induction.
  unfold P. unfold Zvec_dot. reflexivity. intros.
  unfold P in H. unfold P. unfold Zvec_dot.
  assert (fold_left Z.add Z0 (map2 Z.mul (cons Z h1 n0 t1) (map (Z.mul (Z.neg 1)) (cons Z h2 n0 t2))) =
  fold_left Z.add (Z.mul (Z.neg 1) (Z.mul h1 h2)) (map2 Z.mul t1 (map (Z.mul (Z.neg 1)) t2))).
  assert (fold_left Z.add Z0 (map2 Z.mul (cons Z h1 n0 t1) (map (Z.mul (Z.neg 1)) (cons Z h2 n0 t2))) =
  fold_left Z.add (Z.mul h1 (Z.mul (Zneg 1) h2)) (map2 Z.mul t1 (map (Z.mul (Z.neg 1)) t2))). reflexivity.
  rewrite H0. assert (Z.mul h1 (Z.mul (Z.neg 1) h2) = Z.mul (Z.neg 1) (Z.mul h1 h2)).
  rewrite Z.mul_assoc. rewrite Z.mul_comm. rewrite Z.mul_assoc. rewrite Z.mul_assoc.
  rewrite Z.mul_comm. assert (Z.mul h1 h2 = Z.mul h2 h1). apply Z.mul_comm. rewrite <- H1.
  apply Z.mul_assoc. rewrite H1. reflexivity. rewrite H0. rewrite fold_left_add_unfold.
  unfold Zvec_dot in H. rewrite H.
  assert (fold_left Z.add Z0 (map2 Z.mul (cons Z h1 n0 t1) (cons Z h2 n0 t2)) =
          fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2)). reflexivity. rewrite H1.
  assert (fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2) =
          Z.add (Z.mul h1 h2) (fold_left Z.add Z0 (map2 Z.mul t1 t2))). apply fold_left_add_unfold.
  rewrite H2. omega. Qed.

Lemma Z_add_sub_mult_eq : forall (A B C : Z),
  Z.mul A B = Z.sub (Z.mul (Z.add A C) B) (Z.mul C B).
Proof.
  intros. rewrite <- (Zmult_minus_distr_r (Z.add A C) C B).
  rewrite <- Z.add_opp_r. rewrite <- Z.add_assoc. rewrite Z.add_opp_r.
  rewrite <- Zminus_diag_reverse. rewrite <- Zplus_0_r_reverse. reflexivity. Qed.

Lemma Zvec_dot_add_sub_mult_eq : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_dot v1 v2 = (Z.sub (Zvec_dot (Zvec_plus v1 v3) v2) (Zvec_dot v3 v2)).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Zvec n) => Zvec_dot v1 v2 = (Z.sub (Zvec_dot (Zvec_plus v1 v3) v2) (Zvec_dot v3 v2))).
  change (P n v1 v2 v3). apply triple_induction; unfold P; clear P; intros.
  { unfold Zvec_dot. reflexivity. }
  simpl. unfold Zvec_dot. simpl. rewrite fold_left_add_unfold. fold (Zvec_dot t1 t2).
  assert (fold_left Z.add (Z.mul (Z.add h1 h3) h2) (map2 Z.mul (Zvec_plus t1 t3) t2) =
          Z.add (Z.mul (Z.add h1 h3) h2) (fold_left Z.add Z0 (map2 Z.mul (Zvec_plus t1 t3) t2))).
    apply fold_left_add_unfold. rewrite H0. clear H0.
  assert (fold_left Z.add (Z.mul h3 h2) (map2 Z.mul t3 t2) = Z.add (Z.mul h3 h2) (fold_left Z.add Z0 (map2 Z.mul t3 t2))).
  apply fold_left_add_unfold. rewrite H0. clear H0. fold (Zvec_dot (Zvec_plus t1 t3) t2). fold (Zvec_dot t3 t2).
  rewrite H. assert (forall (A B C D : Z), Z.sub (Z.add A B) (Z.add C D) = Z.add (Z.sub A C) (Z.sub B D)). intros. omega.
  rewrite H0; clear H0. rewrite Z_add_sub_mult_eq with (C := h3). reflexivity. Qed.

Lemma Zvec_normsq_cons : forall {n : nat} (h : Z) (t : Zvec n),
  Zvec_normsq (cons Z h n t) = Z.add (Z.mul h h) (Zvec_normsq t).
Proof.
  intros. unfold Zvec_normsq, Zvec_dot. simpl. apply fold_left_add_unfold. Qed.

Lemma Zvec_dot_cons : forall {n : nat} (h1 h2 : Z) (t1 t2 : Zvec n),
  Zvec_dot (cons Z h1 n t1) (cons Z h2 n t2) = Z.add (Z.mul h1 h2) (Zvec_dot t1 t2).
Proof.
  intros. unfold Zvec_dot. simpl. apply fold_left_add_unfold. Qed.

Lemma Zvec_normsq_plus : forall {n: nat} (v1 v2 : Zvec n),
  Zvec_normsq (Zvec_plus v1 v2) = Z.add (Z.add (Zvec_normsq v1) (Z.mul 2 (Zvec_dot v1 v2))) (Zvec_normsq v2).
Proof.
  intros. set (P := fun n (v1 v2 : Zvec n) => Zvec_normsq (Zvec_plus v1 v2) = 
  Z.add (Z.add (Zvec_normsq v1) (Z.mul 2 (Zvec_dot v1 v2))) (Zvec_normsq v2)).
  change (P n v1 v2). apply mutual_induction; unfold P; intros. reflexivity.
  unfold Zvec_plus. assert (map2 Z.add (cons Z h1 n0 t1) (cons Z h2 n0 t2) =
                           cons Z (Z.add h1 h2) n0 (map2 Z.add t1 t2)). reflexivity. rewrite H0; clear H0.
  repeat (rewrite Zvec_normsq_cons). fold (Zvec_plus t1 t2). rewrite H.
  rewrite Zvec_dot_cons. assert (Z.mul 2 (Z.add (Z.mul h1 h2) (Zvec_dot t1 t2)) = 
  Z.add (Z.mul 2 (Z.mul h1 h2)) (Z.mul 2 (Zvec_dot t1 t2))). apply Z.mul_add_distr_l. rewrite H0; clear H0.
  assert ((Z.mul (Z.add h1 h2) (Z.add h1 h2)) = Z.add (Z.mul h1 h1) (Z.add (Z.mul 2 (Z.mul h1 h2)) (Z.mul h2 h2))).
  rewrite Z.mul_add_distr_l. repeat (rewrite Z.mul_add_distr_r). assert (Z.mul 2 (Z.mul h1 h2) = Z.mul (Z.mul h1 h2) 2). omega.
  rewrite H0; clear H0. rewrite <- Zplus_diag_eq_mult_2. repeat (rewrite Z.add_assoc).
  assert (Z.mul h1 h2 = Z.mul h2 h1). apply Z.mul_comm. rewrite H0; clear H0. reflexivity.
  rewrite H0; clear H0. omega. Qed.

Lemma Zvec_dot_Zvec_zero : forall {n : nat} (v : Zvec n),
  Zvec_dot (Zvec_zero n) v = Z0.
Proof.
  intros. induction v. unfold Zvec_zero, Zvec_dot. reflexivity.
  unfold Zvec_dot. simpl. apply IHv. Qed.

Lemma Zvec_dot_Zvec_zero_r : forall {n : nat} (v : Zvec n),
  Zvec_dot v (Zvec_zero n) = Z0.
Proof.
  intros. induction v. unfold Zvec_zero, Zvec_dot. reflexivity.
  unfold Zvec_dot. simpl. rewrite <- Zmult_0_r_reverse. apply IHv. Qed.

Lemma Zvec_plus_Zvec_zero : forall {n : nat} (v : Zvec n),
  Zvec_plus (Zvec_zero n) v = v.
Proof.
  intros. induction v. unfold Zvec_plus, Zvec_zero. reflexivity.
  unfold Zvec_plus, Zvec_zero. simpl. unfold Zvec_plus, Zvec_zero in IHv.
  rewrite IHv. reflexivity. Qed.

Lemma Zvec_plus_Zvec_zero_r : forall {n : nat} (v : Zvec n),
  Zvec_plus v (Zvec_zero n) = v.
Proof.
  intros. induction v. unfold Zvec_plus, Zvec_zero. reflexivity.
  unfold Zvec_plus, Zvec_zero. simpl. unfold Zvec_plus, Zvec_zero in IHv.
  rewrite IHv. rewrite <- Zplus_0_r_reverse. reflexivity. Qed.

Lemma Zvec_dot_dist_l : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_dot (Zvec_plus v1 v2) v3 = Z.add (Zvec_dot v1 v3) (Zvec_dot v2 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Zvec n) =>
  Zvec_dot (Zvec_plus v1 v2) v3 = Z.add (Zvec_dot v1 v3) (Zvec_dot v2 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; intros. reflexivity.
  simpl. rewrite Zvec_dot_cons. rewrite H.
  unfold Zvec_dot. simpl. assert (fold_left Z.add (Z.mul h1 h3) (map2 Z.mul t1 t3) =
  Z.add (Z.mul h1 h3) (fold_left Z.add Z0 (map2 Z.mul t1 t3))). apply fold_left_add_unfold.
  rewrite H0; clear H0. assert (fold_left Z.add (Z.mul h2 h3) (map2 Z.mul t2 t3) =
  Z.add (Z.mul h2 h3) (fold_left Z.add Z0 (map2 Z.mul t2 t3))). apply fold_left_add_unfold.
  rewrite H0; clear H0. fold (Zvec_dot t1 t3). fold (Zvec_dot t2 t3). rewrite Z.add_assoc.
  rewrite Z.add_assoc. rewrite Z.mul_add_distr_r. omega. Qed.

Lemma Zvec_dot_dist_r : forall {n : nat} (v1 v2 v3 : Zvec n),
  Zvec_dot v1 (Zvec_plus v2 v3) = Z.add (Zvec_dot v1 v2) (Zvec_dot v1 v3).
Proof.
  intros. set (P := fun {n} (v1 v2 v3 : Zvec n) =>
  Zvec_dot v1 (Zvec_plus v2 v3) = Z.add (Zvec_dot v1 v2) (Zvec_dot v1 v3)).
  change (P n v1 v2 v3). apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. rewrite Zvec_dot_cons. rewrite H. unfold Zvec_dot. simpl.
  assert (fold_left Z.add (Z.mul h1 h2) (map2 Z.mul t1 t2) =
  Z.add (Z.mul h1 h2) (fold_left Z.add Z0 (map2 Z.mul t1 t2))). apply fold_left_add_unfold.
  rewrite H0; clear H0. fold (Zvec_dot t1 t2).
  assert (fold_left Z.add (Z.mul h1 h3) (map2 Z.mul t1 t3) =
  Z.add (Z.mul h1 h3) (fold_left Z.add Z0 (map2 Z.mul t1 t3))). apply fold_left_add_unfold.
  rewrite H0; clear H0. fold (Zvec_dot t1 t3). repeat (rewrite Z.add_assoc).
  rewrite Z.mul_add_distr_l. omega. Qed.

Lemma Zvec_plus_shuffle : forall {n: nat} (v1 v2 v3 : Zvec n),
  Zvec_plus (Zvec_plus v1 v2) v3 = Zvec_plus (Zvec_plus v1 v3) v2.
Proof.
  intros. set (P := fun n (v1 v2 v3 : Zvec n) => 
  Zvec_plus (Zvec_plus v1 v2) v3 = Zvec_plus (Zvec_plus v1 v3) v2). change (P n v1 v2 v3).
  apply triple_induction; unfold P; clear P; intros. reflexivity.
  simpl. rewrite H. assert (Z.add (Z.add h1 h2) h3 = Z.add (Z.add h1 h3) h2). omega.
  rewrite H0; clear H0. reflexivity. Qed.

Lemma Zvec_plus_comm : forall {n : nat} (v1 v2 : Zvec n),
  Zvec_plus v1 v2 = Zvec_plus v2 v1.
Proof.
  intros. set (P := fun n (v1 v2 : Zvec n) => Zvec_plus v1 v2 = Zvec_plus v2 v1).
  change (P n v1 v2). apply mutual_induction; unfold P; intros; clear P. reflexivity.
  simpl. rewrite H. rewrite Z.add_comm. reflexivity. Qed.

Lemma Zvec_foil_w_0 : forall {n : nat} (v1 v2 : Zvec (S n)) (L : list ((Zvec n)*bool)),
  Z.add (Zvec_dot v1 (Zvec_sum L)) (Zvec_foil v2 L) = Zvec_foil (Zvec_plus v2 v1) L.
Proof.
  intros; generalize dependent v1; generalize dependent v2; induction L; intros.
  simpl. rewrite Zvec_dot_Zvec_zero_r. reflexivity. destruct a as [f l].
  unfold Zvec_sum. fold (Zvec_sum L). unfold Zvec_foil.
  fold (Zvec_foil  (Zvec_plus v2 (Zvec_mult_class l (consb f)))).
  fold (Zvec_foil (Zvec_plus (Zvec_plus v2 v1) (Zvec_mult_class l (consb f)))). rewrite Zvec_dot_dist_r.
  rewrite Z.add_assoc.
  assert (forall (A B C D : Z), Z.add (Z.add (Z.add A B) C) D = Z.add (Z.add A C) (Z.add B D)). intros. omega.
  rewrite H; clear H. rewrite IHL. rewrite <- Zvec_dot_dist_l.
  rewrite Zvec_plus_shuffle. rewrite Zvec_plus_comm. reflexivity. Qed.

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

Lemma In_Ipol_In_T : forall {n : nat} (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)) (L : list ((Zvec n)*bool)) (w : Zvec (S n)) (f : Zvec n) (l : bool),
  IPOL T w0 = Some (L, w) -> List.In (f, l) L -> List.In (f, l) T.
Proof.
  intros n T. induction T; intros. inversion H.
  destruct a as [f' l']. simpl in H. destruct (correct_class (Zvec_dot w0 (consb f')) l').
  apply IHT with w0 L w f l in H. right. apply H. apply H0.
  destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l' (consb f')))) eqn:H1.
  destruct p as [L' w']. inversion H; subst; clear H.
  inversion H0. left. apply H. right. apply IHT with _ _ _ f l in H1. apply H1. apply H.
  inversion H; subst; clear H. inversion H0. left. apply H. inversion H. Qed.

Lemma In_MCE_In_T : forall {n : nat} (E : nat ) (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)) (f : Zvec n) (l : bool),
  List.In (f, l) (MCE E T w0) -> List.In (f, l) T.
Proof.
  intros n E. induction E; intros. inversion H.
  simpl in H. destruct (IPOL T w0) eqn: H0. destruct p as [L w'].
  apply List.in_app_or in H. inversion H.
  apply In_Ipol_In_T with _ _ _ _ f l in H0. apply H0. apply H1.
  apply IHE in H1. apply H1.
  inversion H. Qed.

(**************************************************************************************************
                This section will be for proof of the lower bound
 **************************************************************************************************)
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

Lemma correct_class_T_Zvec_normsq_wstar : forall {n : nat} (T : list ((Zvec n)*bool)) (w : Zvec (S n)),
  correctly_classifiedP T w -> Z.gt (Zvec_normsq w) Z0 \/ T = List.nil.
Proof.
  intros n T; induction T; intros. right. reflexivity. inversion H; subst. apply IHT in H2.
  inversion H2. left. apply H0. subst. left. apply correct_class_w_dot_f_pos in H4.
  assert (Zvec_dot w (Zvec_mult_class l (consb f)) <> Z0). omega. apply Zvec_dot_Not_Zvec_zero in H0.
  destruct H0 as [H0 H1]. apply (Zvec_normsq_Not_Zvec_Zero w H0). Qed.

Lemma Zvec_sum_dot_append : forall {n : nat} (L1 L2 : list ((Zvec n)*bool)) (w : Zvec (S n)),
  Zvec_sum_dot w (List.app L1 L2) = Z.add (Zvec_sum_dot w L1) (Zvec_sum_dot w L2).
Proof.
  intros n L1; induction L1; intros. reflexivity. destruct a as [f l]. simpl. rewrite IHL1.
  repeat (rewrite Z.add_assoc). reflexivity. Qed.

Lemma correct_class_T_Zvec_sum_dot_IPOL : forall {n : nat} (T M: list ((Zvec n)*bool)) (wstar w0 w : Zvec (S n)),
  correctly_classifiedP T wstar -> IPOL T w0 = Some (M, w) -> Z.le Z0 (Zvec_sum_dot wstar M).
Proof.
  intros n T M wstar; generalize dependent M; induction T; intros. inversion H0. destruct a as [f l].
  simpl in H0. inversion H; subst. destruct (correct_class (Zvec_dot w0 (consb f)) l). apply (IHT _ _ _ H5 H0).
  destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H1. destruct p as [M' w']. inversion H0; subst.
  simpl. apply IHT in H1. apply correct_class_w_dot_f_pos in H6. omega. apply H5. inversion H0; subst.
  simpl. apply correct_class_w_dot_f_pos in H6. omega. Qed.

Lemma correct_class_T_Zvec_sum_dot_MCE : forall {n : nat} (E : nat) (T : list ((Zvec n)*bool)) (w w0 : Zvec (S n)),
  correctly_classifiedP T w -> Z.le Z0 (Zvec_sum_dot w (MCE E T w0)).
Proof.
  intros n E; induction E; intros. reflexivity. unfold MCE. destruct (IPOL T w0) eqn:H0.
  destruct p as [L w']. fold (MCE E T w'). rewrite Zvec_sum_dot_append.
  apply correct_class_T_Zvec_sum_dot_IPOL with (wstar := w) in H0. apply IHE with (w0 := w') in H. omega.
  apply H. reflexivity. Qed.

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

Lemma square_preserves_le : forall (A B : nat),
  A <= B -> A*A <= B*B.
Proof.
  intros; induction H. omega.
  simpl. rewrite mult_succ_r. omega. Qed.

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

(**************************************************************************************************
                This section will be for proof of the upper bound
 **************************************************************************************************)
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

Lemma IPOL_mu_neg: forall {n:nat} (T L: (list ((Zvec n)*bool))) (w0 w: Zvec (S n)),
  IPOL T w0 = Some (L, w) -> (Z.le (Z.mul (Z.pos 2) (min_element_product w0 T)) 0).
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
  rewrite H0 in H1. omega. apply H. destruct (IPOL (List.cons a T) w0) eqn:H0.
  destruct p as [L w]. apply IPOL_mu_neg in H0. left. apply H0.
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

Lemma Zvec_foil_IPOL_w0_le_0 : forall {n : nat} (T M : list ((Zvec n)*bool)) (w0 w: Zvec (S n)),
  IPOL T w0 = Some (M, w) -> Z.le (Zvec_foil w0 M) Z0.
Proof.
  intros n T; induction T; intros. inversion H. destruct a as [f l].
  inversion H. destruct (correct_class (Zvec_dot w0 (consb f)) l) eqn:H2.
  apply (IHT _ _ _ H1). destruct (IPOL T (Zvec_plus w0 (Zvec_mult_class l (consb f)))) eqn:H3.
  { destruct p as [M' w']. inversion H1; subst. simpl. apply IHT in H3.
    apply not_correct_z_mu_neg in H2. omega.
  } simpl in H1. inversion H1; subst. simpl. rewrite <- Zplus_0_r_reverse.
  apply (not_correct_z_mu_neg _ _ _ H2). Qed.

Lemma Zvec_foil_MCE_w0_le_0 : forall {n : nat} (E : nat) (T : list ((Zvec n)*bool)) (w0 : Zvec (S n)),
  Z.le (Zvec_foil w0 (MCE E T w0)) Z0.
Proof.
  intros n E. induction E; intros. reflexivity.
  simpl. destruct (IPOL T w0) eqn:H.
  { destruct p as [M w]. rewrite Zvec_foil_append. assert (H0 := H). apply Zvec_foil_IPOL_w0_le_0 in H.
    apply IPOL_sum_m_w in H0. rewrite Zvec_sum_sum_class. rewrite <- H0.
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

(*******************************************************************************************************
     Proof comining the upper and lower bounds and show that our perceptron algorithm then converges
                     from this fact.
 *******************************************************************************************************)
Lemma mult_preserves_le : forall (A B C : nat),
  B <= C -> A*B <= A*C.
Proof.
  intros A; induction A; intros. omega.
  simpl. assert (H0 := IHA B C). omega. Qed.

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

Lemma mult_div_gt : forall (A B: nat),
  A <> 0 -> A * (NPeano.div B A) + A > B.
Proof.
  intros. destruct (NPeano.div B A) eqn:H1.
  apply NPeano.Nat.div_small_iff in H1. omega. omega.
  assert (H2 := (NPeano.Nat.div_mod B A) H).
  rewrite H2. rewrite H1. assert (HB: 0 <= B). omega.
  assert (HA : 0 < A). omega.
  assert (H3 := (NPeano.mod_bound_pos B A) HB HA). omega. Qed.

Lemma mult_lt_preserve : forall (A B C: nat),
 A * C > B * C -> A > B.
Proof.
  intros A B C. induction C; intros. omega.
  repeat (rewrite mult_succ_r in H).
  omega. Qed.

Lemma AB_limit : forall (A B C: nat),
  A <> 0 -> B <> 0 -> C > (NPeano.div B A) -> A * C * C > B * C.
Proof.
  intros. induction H1.
  { repeat (rewrite mult_succ_r). assert (H1 := (mult_div_gt A B) H).
    induction H1. destruct (NPeano.div B A). omega.
    repeat (rewrite mult_succ_r). simpl. omega.
    destruct (NPeano.div B A). omega.
    simpl. omega.
  } rewrite mult_succ_r. rewrite mult_succ_r. rewrite mult_succ_r.
  rewrite mult_plus_distr_r.
  assert (H2 := IHle). apply mult_lt_preserve in H2. omega. Qed.

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

Theorem linearly_separable_POL : forall {n : nat} (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  linearly_separable T -> exists (E0 : nat) M (w : (Zvec (S n))), forall E, E > E0 -> POL E T w0 = Some (M, w).
Proof.
  intros. apply linearly_separable_MCE with w0 T in H. destruct H as [E0 H].
  exists E0. exists (MCE E0 T w0). exists (Zvec_sum_class w0 (MCE E0 T w0)). intros E.
  intros H1. apply MCE_eq_POL in H. apply POL_done with (S E0). omega. apply H. Qed.

Theorem linearly_separable_perceptron : forall {n : nat} (w0 : Zvec (S n)) (T : (list ((Zvec n)*bool))),
  linearly_separable T -> exists (E0 : nat) (w : (Zvec (S n))), forall E, E > E0 -> perceptron E T w0 = Some w.
Proof.
  intros. apply linearly_separable_POL with w0 T in H.
  destruct H as [E0 [M [w H]]]. exists E0. exists w. intros. apply H in H0.
  apply POL_perceptron. exists M. auto. Qed.

Print Assumptions linearly_separable_perceptron.
