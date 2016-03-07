Require Import Coq.Vectors.Vector.
Require Import ZArith.

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
    Linear Separability
 ********************************************************************************************)
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

(********************************************************************************************
    Other Fixpoints that are used to represent computations on the Training data Or Zvec
 ********************************************************************************************)
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