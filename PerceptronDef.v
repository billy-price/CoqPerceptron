Require Import Coq.Vectors.Vector.
Require Import ZArith.
Require Import ZvecArith.

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

Fixpoint inner_perceptron_MCE {n:nat} (T:list ((Zvec n) * (bool))) (w: Zvec (S n)) : option ((list ((Zvec n)*bool))*(Zvec (S n))) := 
  match T with
  | List.nil => None
  | List.cons (f, l) T' =>
      match correct_class (Zvec_dot w (consb f)) l with
      | true => inner_perceptron_MCE T' w
      | false =>
         match inner_perceptron_MCE T' (Zvec_plus w (Zvec_mult_class l (consb f))) with
         | None => Some ((List.cons (f, l) List.nil), (Zvec_plus w (Zvec_mult_class l (consb f))))
         | Some (L, w') => Some ((List.cons (f, l) L), w')
         end
      end
  end.

Fixpoint perceptron_MCE {n:nat} (E:nat) (T:list ((Zvec n) * (bool))) (w : Zvec (S n)) : option((list ((Zvec n)*bool))*(Zvec (S n))) :=
  match E with
  | 0 => None
  | S E' =>
      match (inner_perceptron_MCE T w) with
      | None => Some (List.nil, w)
      | Some (L, w') =>
        match perceptron_MCE E' T w' with
        | None => None
        | Some (L', w'') => Some ((List.app L L'), w'')
        end
      end
  end.

Fixpoint MCE {n: nat} (E : nat) (T: list ((Zvec n)*bool)) (w : Zvec (S n)) : (list ((Zvec n)*bool)) :=
  match E with
  | 0 => List.nil
  | S E' =>
    match (inner_perceptron_MCE T w) with
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