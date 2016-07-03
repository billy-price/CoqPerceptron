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

add :: Positive -> Positive -> Positive
add x y =
  case x of {
   XI p ->
    case y of {
     XI q -> XO (add_carry p q);
     XO q -> XI (add p q);
     XH -> XO (succ p)};
   XO p ->
    case y of {
     XI q -> XI (add p q);
     XO q -> XO (add p q);
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
     XO q -> XI (add p q);
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

mul :: Positive -> Positive -> Positive
mul x y =
  case x of {
   XI p -> add y (XO (mul p y));
   XO p -> XO (mul p y);
   XH -> y}

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

add0 :: Z -> Z -> Z
add0 x y =
  case x of {
   Z0 -> y;
   Zpos x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> Zpos (add x' y');
     Zneg y' -> pos_sub x' y'};
   Zneg x' ->
    case y of {
     Z0 -> x;
     Zpos y' -> pos_sub y' x';
     Zneg y' -> Zneg (add x' y')}}

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

leb :: Z -> Z -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

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
  Qmake (add0 (mul0 (qnum x) (Zpos (qden y))) (mul0 (qnum y) (Zpos (qden x)))) (mul (qden x) (qden y))

qmult :: Q -> Q -> Q
qmult x y =
  Qmake (mul0 (qnum x) (qnum y)) (mul (qden x) (qden y))

map :: (a1 -> a2) -> Nat -> (([]) a1) -> ([]) a2
map = (\g _ l -> Prelude.map g l)

map2 :: (a1 -> a2 -> a3) -> Nat -> (([]) a1) -> (([]) a2) -> ([]) a3
map2 = (\g _ l1 l2 -> Prelude.map (\(x,y) -> g x y) (Prelude.zip l1 l2))

fold_left :: (a2 -> a1 -> a2) -> a2 -> Nat -> (([]) a1) -> a2
fold_left = (\g a _ l -> Prelude.foldl g a l)

type Qvec = ([]) Q

qvec_plus :: Nat -> Qvec -> Qvec -> ([]) Q
qvec_plus n v1 v2 =
  map2 qplus n v1 v2

qvec_dot :: Nat -> Qvec -> Qvec -> Q
qvec_dot n v1 v2 =
  fold_left qplus (Qmake Z0 XH) n (map2 qmult n v1 v2)

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
   Prelude.False -> map (qmult (Qmake (opp (Zpos XH)) XH)) n f}

consb :: Nat -> Qvec -> ([]) Q
consb n v =
  (\a _ v -> a : v) (Qmake (Zpos XH) XH) n v

inner_perceptron :: Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec -> Option Qvec
inner_perceptron n t w =
  case t of {
   [] -> None;
   (:) p t' ->
    case p of {
     (,) f l ->
      case correct_class (qvec_dot (S n) w (consb n f)) l of {
       Prelude.True -> inner_perceptron n t' w;
       Prelude.False ->
        case inner_perceptron n t' (qvec_plus (S n) w (qvec_mult_class (S n) l (consb n f))) of {
         Some w' -> Some w';
         None -> Some (qvec_plus (S n) w (qvec_mult_class (S n) l (consb n f)))}}}}

perceptron :: Nat -> Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec -> Option Qvec
perceptron n e t w =
  case e of {
   O -> None;
   S e' ->
    case inner_perceptron n t w of {
     Some w' -> perceptron n e' t w';
     None -> Some w}}

gas :: (Nat -> a1) -> a1
gas = (\f -> let infiniteGas = S infiniteGas in f infiniteGas)

fueled_perceptron :: Nat -> Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec -> Option Qvec
fueled_perceptron n _ t w =
  gas (\fuel -> perceptron n fuel t w)

