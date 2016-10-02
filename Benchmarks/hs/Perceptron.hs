module Perceptron where

import qualified Prelude
import Data.Ratio

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

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb = (Prelude.==)

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p -> (\x -> (Prelude.*) 2 x)
    (succ p))
    (\p -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p)
    (\_ -> (\x -> (Prelude.*) 2 x)
    1)
    x

add0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add0 x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add_carry p q))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add0 p q))
      (\_ -> (\x -> (Prelude.*) 2 x)
      (succ p))
      y)
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add0 p q))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add0 p q))
      (\_ -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      p)
      y)
    (\_ ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.*) 2 x)
      (succ q))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      q)
      (\_ -> (\x -> (Prelude.*) 2 x)
      1)
      y)
    x

add_carry :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add_carry x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add_carry p q))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add_carry p q))
      (\_ -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (succ p))
      y)
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add_carry p q))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add0 p q))
      (\_ -> (\x -> (Prelude.*) 2 x)
      (succ p))
      y)
    (\_ ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (succ q))
      (\q -> (\x -> (Prelude.*) 2 x)
      (succ q))
      (\_ -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      1)
      y)
    x

pred_double :: Prelude.Integer -> Prelude.Integer
pred_double x =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    ((\x -> (Prelude.*) 2 x)
    p))
    (\p -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    (pred_double p))
    (\_ ->
    1)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

succ_double_mask :: Mask -> Mask
succ_double_mask x =
  case x of {
   IsNul -> IsPos 1;
   IsPos p -> IsPos ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1) p);
   IsNeg -> IsNeg}

double_mask :: Mask -> Mask
double_mask x =
  case x of {
   IsPos p -> IsPos ((\x -> (Prelude.*) 2 x) p);
   x0 -> x0}

double_pred_mask :: Prelude.Integer -> Mask
double_pred_mask x =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p -> IsPos ((\x -> (Prelude.*) 2 x) ((\x -> (Prelude.*) 2 x)
    p)))
    (\p -> IsPos ((\x -> (Prelude.*) 2 x)
    (pred_double p)))
    (\_ ->
    IsNul)
    x

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> (Prelude.*) 2 x)
      p))
      y)
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\_ ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\_ ->
      IsNeg)
      (\_ ->
      IsNeg)
      (\_ ->
      IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      double_mask (sub_mask_carry p q))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\_ ->
      double_pred_mask p)
      y)
    (\_ ->
    IsNeg)
    x

sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub x y =
  case sub_mask x y of {
   IsPos z -> z;
   _ -> 1}

mul :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    add0 y ((\x -> (Prelude.*) 2 x) (mul p y)))
    (\p -> (\x -> (Prelude.*) 2 x)
    (mul p y))
    (\_ ->
    y)
    x

size_nat :: Prelude.Integer -> Nat
size_nat p =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p0 -> S
    (size_nat p0))
    (\p0 -> S
    (size_nat p0))
    (\_ -> S
    O)
    p

compare_cont :: Comparison -> Prelude.Integer -> Prelude.Integer ->
                Comparison
compare_cont r x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      compare_cont r p q)
      (\q ->
      compare_cont Gt p q)
      (\_ ->
      Gt)
      y)
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      compare_cont Lt p q)
      (\q ->
      compare_cont r p q)
      (\_ ->
      Gt)
      y)
    (\_ ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\_ ->
      Lt)
      (\_ ->
      Lt)
      (\_ ->
      r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare =
  compare_cont Eq

ggcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcdn n a b =
  case n of {
   O -> (,) 1 ((,) a b);
   S n0 ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\a' ->
      (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
        (\b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) 1 1);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa
              (add0 aa ((\x -> (Prelude.*) 2 x) ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,)
              (add0 bb ((\x -> (Prelude.*) 2 x) ab)) bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa ((\x -> (Prelude.*) 2 x) bb))}})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\a0 ->
      (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
        (\_ ->
        case ggcdn n0 a0 b of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) ((\x -> (Prelude.*) 2 x) aa) bb)}})
        (\b0 ->
        case ggcdn n0 a0 b0 of {
         (,) g p -> (,) ((\x -> (Prelude.*) 2 x) g) p})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\_ -> (,) 1 ((,) 1
      b))
      a}

ggcd :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
        ((,) Prelude.Integer Prelude.Integer)
ggcd a b =
  ggcdn (add (size_nat a) (size_nat b)) a b

double :: Prelude.Integer -> Prelude.Integer
double x =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p ->  ((\x -> (Prelude.*) 2 x)
    p))
    (\p -> (\x -> (Prelude.*) x (-1)) ((\x -> (Prelude.*) 2 x)
    p))
    x

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ -> 
    1)
    (\p ->  ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p))
    (\p -> (\x -> (Prelude.*) x (-1))
    (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ -> (\x -> (Prelude.*) x (-1))
    1)
    (\p -> 
    (pred_double p))
    (\p -> (\x -> (Prelude.*) x (-1))
    ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p))
    x

pos_sub :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pos_sub x y =
  (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      double (pos_sub p q))
      (\q ->
      succ_double (pos_sub p q))
      (\_ ->  ((\x -> (Prelude.*) 2 x)
      p))
      y)
    (\p ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double (pos_sub p q))
      (\_ -> 
      (pred_double p))
      y)
    (\_ ->
    (\xI xO xH p ->                    if (Prelude.==) p 1 then xH ()                    else if Prelude.even p then xO (Prelude.quot p 2)                         else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.*) x (-1)) ((\x -> (Prelude.*) 2 x)
      q))
      (\q -> (\x -> (Prelude.*) x (-1))
      (pred_double q))
      (\_ ->
      0)
      y)
    x

add1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add1 = (Prelude.+)

opp :: Prelude.Integer -> Prelude.Integer
opp x =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\x0 -> (\x -> (Prelude.*) x (-1))
    x0)
    (\x0 -> 
    x0)
    x

mul0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul0 = (Prelude.*)

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 x y =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Eq)
      (\_ ->
      Lt)
      (\_ ->
      Gt)
      y)
    (\x' ->
    (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Gt)
      (\y' ->
      compare x' y')
      (\_ ->
      Gt)
      y)
    (\x' ->
    (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Lt)
      (\_ ->
      Lt)
      (\y' ->
      compOpp (compare x' y'))
      y)
    x

sgn :: Prelude.Integer -> Prelude.Integer
sgn z =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\_ -> 
    1)
    (\_ -> (\x -> (Prelude.*) x (-1))
    1)
    z

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    p)
    (\p -> 
    p)
    z

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    1)
    (\p ->
    p)
    (\_ ->
    1)
    z

ggcd0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcd0 a b =
  (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
    (\_ -> (,) (abs b) ((,) 0
    (sgn b)))
    (\a0 ->
    (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ( g) ((,) ( aa) ( bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ( g) ((,) ( aa) ((\x -> (Prelude.*) x (-1)) bb))}})
      b)
    (\a0 ->
    (\fO fPos fNeg z ->                    if (Prelude.==) z 0 then fO ()                    else if (Prelude.>) z 0 then fPos z                         else fNeg ((Prelude.*) z (-1)))
      (\_ -> (,) (abs a) ((,) (sgn a)
      0))
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ( g) ((,) ((\x -> (Prelude.*) x (-1)) aa) ( bb))}})
      (\b0 ->
      case ggcd a0 b0 of {
       (,) g p ->
        case p of {
         (,) aa bb -> (,) ( g) ((,) ((\x -> (Prelude.*) x (-1)) aa)
          ((\x -> (Prelude.*) x (-1)) bb))}})
      b)
    a

qeq_bool :: Rational -> Rational -> Prelude.Bool
qeq_bool = (Prelude.==)

qle_bool :: Rational -> Rational -> Prelude.Bool
qle_bool = (Prelude.<=)

map :: (a1 -> a2) -> Nat -> (([]) a1) -> ([]) a2
map = (\g _ l -> Prelude.map g l)

map2 :: (a1 -> a2 -> a3) -> Nat -> (([]) a1) -> (([]) a2) -> ([]) a3
map2 = (\g _ l1 l2 -> Prelude.map (\(x,y) -> g x y) (Prelude.zip l1 l2))

fold_left :: (a2 -> a1 -> a2) -> a2 -> Nat -> (([]) a1) -> a2
fold_left = (\g a _ l -> Prelude.foldl g a l)

qplus :: Rational -> Rational -> Rational
qplus = (Prelude.+)

qmult :: Rational -> Rational -> Rational
qmult = (Prelude.*)

type Qvec = ([]) Rational

qvec_plus :: Nat -> Qvec -> Qvec -> ([]) Rational
qvec_plus n v1 v2 =
  map2 qplus n v1 v2

qvec_dot :: Nat -> Qvec -> Qvec -> Rational
qvec_dot n v1 v2 =
  fold_left qplus ((\n d -> (Data.Ratio.%) n d) 0 1) n
    (map2 qmult n v1 v2)

class0 :: Rational -> Prelude.Bool
class0 i =
  qle_bool ((\n d -> (Data.Ratio.%) n d) 0 1) i

correct_class :: Rational -> Prelude.Bool -> Prelude.Bool
correct_class i l =
  andb (eqb l (class0 i))
    (negb (qeq_bool i ((\n d -> (Data.Ratio.%) n d) 0 1)))

qvec_mult_class :: Nat -> Prelude.Bool -> Qvec -> Qvec
qvec_mult_class n l f =
  case l of {
   Prelude.True -> f;
   Prelude.False ->
    map (qmult ((\n d -> (Data.Ratio.%) n d) (opp ( 1)) 1)) n f}

consb :: Nat -> Qvec -> ([]) Rational
consb n v =
  (\a _ v -> a : v) ((\n d -> (Data.Ratio.%) n d) ( 1) 1) n v

inner_perceptron :: Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec ->
                    Option Qvec
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

perceptron :: Nat -> Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec ->
              Option Qvec
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

fueled_perceptron :: Nat -> Nat -> (([]) ((,) Qvec Prelude.Bool)) -> Qvec
                     -> Option Qvec
fueled_perceptron n _ t w =
  gas (\fuel -> perceptron n fuel t w)

