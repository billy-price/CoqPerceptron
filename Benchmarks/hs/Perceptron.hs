module Perceptron where

import qualified Prelude

andb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
andb b1 b2 =
  case b1 of {
   Prelude.True -> b2;
   Prelude.False -> Prelude.False}

negb :: Prelude.Bool -> Prelude.Bool
negb = (Prelude.not)

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

data Comparison =
   Eq
 | Lt
 | Gt

compOpp :: Comparison -> Comparison
compOpp r =
  case r of {
   Eq -> Eq;
   Lt -> Gt;
   Gt -> Lt}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb = (Prelude.==)

succ :: Positive -> Positive
succ x =
  case x of {
   XI p -> XO (succ p);
   XO p -> XI p;
   XH -> XO XH}

add0 :: Positive -> Positive -> Positive
add0 x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add0 p q);
     XO q -> XO (add0 p q);
     XH -> XI p};
   XH ->
    case y of {
     XI q -> XO (succ q);
     XO q -> XI q;
     XH -> XO XH}}

add_carry :: Positive -> Positive -> Positive
add_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XI (add_carry p q);
     XO q -> XO (add_carry p q);
     XH -> XI (succ p)};
   XO p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add0 p q);
     XH -> XO (succ p)};
   XH ->
    case y of {
     XI q -> XI (succ q);
     XO q -> XO (succ q);
     XH -> XI XH}}

pred_double :: Positive -> Positive
pred_double x =
  case x of {
   XI p -> XI (XO p);
   XO p -> XI (pred_double p);
   XH -> XH}

data Mask =
   IsNul
 | IsPos Positive
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos XH;
   IsPos p -> IsPos (XI p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos (XO p);
   x0 -> x0}

double_pred_mask :: Positive -> Mask
double_pred_mask x =
  case x of {
   XI p -> IsPos (XO (XO p));
   XO p -> IsPos (XO (pred_double p));
   XH -> IsNul}

sub_mask :: Positive -> Positive -> Mask
sub_mask x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double_mask (sub_mask p q);
     XO q -> succ_double_mask (sub_mask p q);
     XH -> IsPos (XO p)};
   XO p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XH ->
    case y of {
     XH -> IsNul;
     _ -> IsNeg}}

sub_mask_carry :: Positive -> Positive -> Mask
sub_mask_carry x y =
  case x of {
   XI p ->
    case y of {
     XI q -> succ_double_mask (sub_mask_carry p q);
     XO q -> double_mask (sub_mask p q);
     XH -> IsPos (pred_double p)};
   XO p ->
    case y of {
     XI q -> double_mask (sub_mask_carry p q);
     XO q -> succ_double_mask (sub_mask_carry p q);
     XH -> double_pred_mask p};
   XH -> IsNeg}

sub :: Positive -> Positive -> Positive
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> XH}

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add0 y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

size_nat :: Positive -> Nat
size_nat p =
  case p of {
   XI p0 -> S (size_nat p0);
   XO p0 -> S (size_nat p0);
   XH -> S O}

compare_cont :: Comparison -> Positive -> Positive -> Comparison
compare_cont r x y =
  case x of {
   XI p ->
    case y of {
     XI q -> compare_cont r p q;
     XO q -> compare_cont Gt p q;
     XH -> Gt};
   XO p ->
    case y of {
     XI q -> compare_cont Lt p q;
     XO q -> compare_cont r p q;
     XH -> Gt};
   XH ->
    case y of {
     XH -> r;
     _ -> Lt}}

compare :: Positive -> Positive -> Comparison
compare =
  compare_cont Eq

ggcdn :: Nat -> Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcdn n a b =
  case n of {
   O -> (,) XH ((,) a b);
   S n0 ->
    case a of {
     XI a' ->
      case b of {
       XI b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) XH XH);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa (add0 aa (XO ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add0 bb (XO ab)) bb)}}};
       XO b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa (XO bb))}};
       XH -> (,) XH ((,) a XH)};
     XO a0 ->
      case b of {
       XI _ ->
        case ggcdn n0 a0 b of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) (XO aa) bb)}};
       XO b0 ->
        case ggcdn n0 a0 b0 of {
         (,) g p -> (,) (XO g) p};
       XH -> (,) XH ((,) a XH)};
     XH -> (,) XH ((,) XH b)}}

ggcd :: Positive -> Positive -> (,) Positive ((,) Positive Positive)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

double :: Z -> Z
double x =
  case x of {
   Z0 -> Z0;
   Zpos p -> Zpos (XO p);
   Zneg p -> Zneg (XO p)}

succ_double :: Z -> Z
succ_double x =
  case x of {
   Z0 -> Zpos XH;
   Zpos p -> Zpos (XI p);
   Zneg p -> Zneg (pred_double p)}

pred_double0 :: Z -> Z
pred_double0 x =
  case x of {
   Z0 -> Zneg XH;
   Zpos p -> Zpos (pred_double p);
   Zneg p -> Zneg (XI p)}

pos_sub :: Positive -> Positive -> Z
pos_sub x y =
  case x of {
   XI p ->
    case y of {
     XI q -> double (pos_sub p q);
     XO q -> succ_double (pos_sub p q);
     XH -> Zpos (XO p)};
   XO p ->
    case y of {
     XI q -> pred_double0 (pos_sub p q);
     XO q -> double (pos_sub p q);
     XH -> Zpos (pred_double p)};
   XH ->
    case y of {
     XI q -> Zneg (XO q);
     XO q -> Zneg (pred_double q);
     XH -> Z0}}

add1 :: Z -> Z -> Z
add1 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add0 x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add0 x' y')}}

opp :: Z -> Z
opp x =
  case x of {
   Z0 -> Z0;
   Zpos x0 -> Zneg x0;
   Zneg x0 -> Zpos x0}

mul0 :: Z -> Z -> Z
mul0 x y =
  case x of {
   Z0 -> Z0;
   Zpos x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zpos (mul x' y');
     Zneg y' -> Zneg (mul x' y')};
   Zneg x' ->
    case y of {
     Z0 -> Z0;
     Zpos y' -> Zneg (mul x' y');
     Zneg y' -> Zpos (mul x' y')}}

compare0 :: Z -> Z -> Comparison
compare0 x y =
  case x of {
   Z0 ->
    case y of {
     Z0 -> Eq;
     Zpos _ -> Lt;
     Zneg _ -> Gt};
   Zpos x' ->
    case y of {
     Zpos y' -> compare x' y';
     _ -> Gt};
   Zneg x' ->
    case y of {
     Zneg y' -> compOpp (compare x' y');
     _ -> Lt}}

sgn :: Z -> Z
sgn z =
  case z of {
   Z0 -> Z0;
   Zpos _ -> Zpos XH;
   Zneg _ -> Zneg XH}

leb :: Z -> Z -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

abs :: Z -> Z
abs z =
  case z of {
   Zneg p -> Zpos p;
   x -> x}

to_pos :: Z -> Positive
to_pos z =
  case z of {
   Zpos p -> p;
   _ -> XH}

ggcd0 :: Z -> Z -> (,) Z ((,) Z Z)
ggcd0 a b =
  case a of {
   Z0 -> (,) (abs b) ((,) Z0 (sgn b));
   Zpos a0 ->
    case b of {
     Z0 -> (,) (abs a) ((,) (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zpos aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zpos aa) (Zneg bb))}}};
   Zneg a0 ->
    case b of {
     Z0 -> (,) (abs a) ((,) (sgn a) Z0);
     Zpos b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zneg aa) (Zpos bb))}};
     Zneg b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) (Zpos g) ((,) (Zneg aa) (Zneg bb))}}}}

zeq_bool :: Z -> Z -> Prelude.Bool
zeq_bool x y =
  case compare0 x y of {
   Eq -> Prelude.True;
   _ -> Prelude.False}

data Q =
   Qmake Z Positive

qnum :: Q -> Z
qnum q =
  case q of {
   Qmake qnum0 _ -> qnum0}

qden :: Q -> Positive
qden q =
  case q of {
   Qmake _ qden0 -> qden0}

qeq_bool :: Q -> Q -> Prelude.Bool
qeq_bool x y =
  zeq_bool (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x)))

qle_bool :: Q -> Q -> Prelude.Bool
qle_bool x y =
  leb (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x)))

qplus :: Q -> Q -> Q
qplus x y =
  Qmake
    (add1 (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x))))
    (mul (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake (mul0 (qnum x) (qnum y)) (mul (qden x) (qden y))

qred :: Q -> Q
qred q =
  case q of {
   Qmake q1 q2 ->
    case snd (ggcd0 q1 (Zpos q2)) of {
     (,) r1 r2 -> Qmake r1 (to_pos r2)}}

map :: (a1 -> a2) -> Nat -> (([]) a1) -> ([]) a2
map = (\g _ l -> Prelude.map g l)

map2 :: (a1 -> a2 -> a3) -> Nat -> (([]) a1) -> (([]) a2) -> ([]) a3
map2 = (\g _ l1 l2 -> Prelude.map (\(x,y) -> g x y) (Prelude.zip l1 l2))

fold_left :: (a2 -> a1 -> a2) -> a2 -> Nat -> (([]) a1) -> a2
fold_left = (\g a _ l -> Prelude.foldl g a l)

qplus0 :: Q -> Q -> Q
qplus0 a b =
  qred (qplus a b)

qmult0 :: Q -> Q -> Q
qmult0 a b =
  qred (qmult a b)

type Qvec = ([]) Q

qvec_plus :: Nat -> Qvec -> Qvec -> ([]) Q
qvec_plus n v1 v2 =
  map2 qplus0 n v1 v2

qvec_dot :: Nat -> Qvec -> Qvec -> Q
qvec_dot n v1 v2 =
  fold_left qplus0 (Qmake Z0 XH) n (map2 qmult0 n v1 v2)

class0 :: Q -> Prelude.Bool
class0 i =
  qle_bool (Qmake Z0 XH) i

correct_class :: Q -> Prelude.Bool -> Prelude.Bool
correct_class i l =
  andb (eqb l (class0 i)) (negb (qeq_bool i (Qmake Z0 XH)))

qvec_mult_class :: Nat -> Prelude.Bool -> Qvec -> Qvec
qvec_mult_class n l f =
  case l of {
   Prelude.True -> f;
   Prelude.False -> map (qmult0 (Qmake (opp (Zpos XH)) XH)) n f}

consb :: Nat -> Qvec -> ([]) Q
consb n v =
  (\a _ v -> a : v) (Qmake (Zpos XH) XH) n v

inner_perceptron :: Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec -> Option
                    Qvec
inner_perceptron n t w =
  case t of {
   [] -> None;
   (:) p t' ->
    case p of {
     (,) f l ->
      case correct_class (qvec_dot (S n) w (consb n f)) l of {
       Prelude.True -> inner_perceptron n t' w;
       Prelude.False ->
        case inner_perceptron n t'
               (qvec_plus (S n) w (qvec_mult_class (S n) l (consb n f))) of {
         Some w' -> Some w';
         None -> Some
          (qvec_plus (S n) w (qvec_mult_class (S n) l (consb n f)))}}}}

perceptron :: Nat -> Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec -> Option
              Qvec
perceptron n e t w =
  case e of {
   O -> None;
   S e' ->
    case inner_perceptron n t w of {
     Some w' -> perceptron n e' t w';
     None -> Some w}}

inner_perceptron_MCE :: Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec ->
                        Option ((,) (([]) ((,) Qvec Prelude.Bool)) Qvec)
inner_perceptron_MCE n t w =
  case t of {
   [] -> None;
   (:) p t' ->
    case p of {
     (,) f l ->
      case correct_class (qvec_dot (S n) w (consb n f)) l of {
       Prelude.True -> inner_perceptron_MCE n t' w;
       Prelude.False ->
        case inner_perceptron_MCE n t'
               (qvec_plus (S n) w (qvec_mult_class (S n) l (consb n f))) of {
         Some p0 ->
          case p0 of {
           (,) l0 w' -> Some ((,) ((:) ((,) f l) l0) w')};
         None -> Some ((,) ((:) ((,) f l) [])
          (qvec_plus (S n) w (qvec_mult_class (S n) l (consb n f))))}}}}

gas :: (Nat -> a1) -> a1
gas = (\f -> let infiniteGas = S infiniteGas in f infiniteGas)

fueled_perceptron :: Nat -> Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec ->
                     Option Qvec
fueled_perceptron n _ t w =
  gas (\fuel -> perceptron n fuel t w)

