module FueledPerceptronOpt where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect x f y =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec x f y =
  eq_rect x f y

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r x h y =
  eq_rec x h y

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

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x y -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) x y -> y}

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

data CompareSpecT =
   CompEqT
 | CompLtT
 | CompGtT

compareSpec2Type :: Comparison -> CompareSpecT
compareSpec2Type c =
  case c of {
   Eq -> CompEqT;
   Lt -> CompLtT;
   Gt -> CompGtT}

type CompSpecT a = CompareSpecT

compSpec2Type :: a1 -> a1 -> Comparison -> CompSpecT a1
compSpec2Type x y c =
  compareSpec2Type c

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

data Sumor a =
   Inleft a
 | Inright

plus :: Nat -> Nat -> Nat
plus n m =
  case n of {
   O -> m;
   S p -> S (plus p m)}

nat_iter :: Nat -> (a1 -> a1) -> a1 -> a1
nat_iter n f x =
  case n of {
   O -> x;
   S n' -> f (nat_iter n' f x)}

positive_rect :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                 a1) -> a1 -> Prelude.Integer -> a1
positive_rect f f0 f1 p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    f p0 (positive_rect f f0 f1 p0))
    (\p0 ->
    f0 p0 (positive_rect f f0 f1 p0))
    (\_ ->
    f1)
    p

positive_rec :: (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1 ->
                a1) -> a1 -> Prelude.Integer -> a1
positive_rec =
  positive_rect

n_rect :: a1 -> (Prelude.Integer -> a1) -> Prelude.Integer -> a1
n_rect f f0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    f)
    (\x ->
    f0 x)
    n

n_rec :: a1 -> (Prelude.Integer -> a1) -> Prelude.Integer -> a1
n_rec =
  n_rect

z_rect :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
          Prelude.Integer -> a1
z_rect f f0 f1 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    f)
    (\x ->
    f0 x)
    (\x ->
    f1 x)
    z

z_rec :: a1 -> (Prelude.Integer -> a1) -> (Prelude.Integer -> a1) ->
         Prelude.Integer -> a1
z_rec =
  z_rect

eqb :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool
eqb = (Prelude.==)

data Reflect =
   ReflectT
 | ReflectF

iff_reflect :: Prelude.Bool -> Reflect
iff_reflect b =
  case b of {
   Prelude.True -> and_rec (\_ _ -> ReflectT);
   Prelude.False -> and_rec (\_ _ -> ReflectF)}

type T = Prelude.Integer

succ :: Prelude.Integer -> Prelude.Integer
succ x =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p -> (\x -> (Prelude.*) 2 x)
    (succ p))
    (\p -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p)
    (\_ -> (\x -> (Prelude.*) 2 x)
    1)
    x

add :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add x y =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add_carry p q))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add p q))
      (\_ -> (\x -> (Prelude.*) 2 x)
      (succ p))
      y)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add p q))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add p q))
      (\_ -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      p)
      y)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
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
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add_carry p q))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add_carry p q))
      (\_ -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (succ p))
      y)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q -> (\x -> (Prelude.*) 2 x)
      (add_carry p q))
      (\q -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (add p q))
      (\_ -> (\x -> (Prelude.*) 2 x)
      (succ p))
      y)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
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
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) ((\x -> (Prelude.*) 2 x)
    p))
    (\p -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    (pred_double p))
    (\_ ->
    1)
    x

pred :: Prelude.Integer -> Prelude.Integer
pred x =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p -> (\x -> (Prelude.*) 2 x)
    p)
    (\p ->
    pred_double p)
    (\_ ->
    1)
    x

pred_N :: Prelude.Integer -> Prelude.Integer
pred_N x =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->  ((\x -> (Prelude.*) 2 x)
    p))
    (\p -> 
    (pred_double p))
    (\_ ->
    0)
    x

data Mask =
   IsNul
 | IsPos Prelude.Integer
 | IsNeg

mask_rect :: a1 -> (Prelude.Integer -> a1) -> a1 -> Mask -> a1
mask_rect f f0 f1 m =
  case m of {
   IsNul -> f;
   IsPos x -> f0 x;
   IsNeg -> f1}

mask_rec :: a1 -> (Prelude.Integer -> a1) -> a1 -> Mask -> a1
mask_rec =
  mask_rect

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
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p -> IsPos ((\x -> (Prelude.*) 2 x) ((\x -> (Prelude.*) 2 x)
    p)))
    (\p -> IsPos ((\x -> (Prelude.*) 2 x)
    (pred_double p)))
    (\_ ->
    IsNul)
    x

pred_mask :: Mask -> Mask
pred_mask p =
  case p of {
   IsPos q ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 -> IsPos
      (pred q))
      (\p0 -> IsPos
      (pred q))
      (\_ ->
      IsNul)
      q;
   _ -> IsNeg}

sub_mask :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask x y =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      double_mask (sub_mask p q))
      (\q ->
      succ_double_mask (sub_mask p q))
      (\_ -> IsPos ((\x -> (Prelude.*) 2 x)
      p))
      y)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p ->
      IsNeg)
      (\p ->
      IsNeg)
      (\_ ->
      IsNul)
      y)
    x

sub_mask_carry :: Prelude.Integer -> Prelude.Integer -> Mask
sub_mask_carry x y =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      succ_double_mask (sub_mask_carry p q))
      (\q ->
      double_mask (sub_mask p q))
      (\_ -> IsPos
      (pred_double p))
      y)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
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
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    add y ((\x -> (Prelude.*) 2 x) (mul p y)))
    (\p -> (\x -> (Prelude.*) 2 x)
    (mul p y))
    (\_ ->
    y)
    x

iter :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter n f x =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\n' ->
    f (iter n' f (iter n' f x)))
    (\n' ->
    iter n' f (iter n' f x))
    (\_ ->
    f x)
    n

pow :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow x y =
  iter y (mul x) 1

square :: Prelude.Integer -> Prelude.Integer
square p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) ((\x -> (Prelude.*) 2 x)
    (add (square p0) p0)))
    (\p0 -> (\x -> (Prelude.*) 2 x) ((\x -> (Prelude.*) 2 x)
    (square p0)))
    (\_ ->
    1)
    p

div2 :: Prelude.Integer -> Prelude.Integer
div2 p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

div2_up :: Prelude.Integer -> Prelude.Integer
div2_up p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    succ p0)
    (\p0 ->
    p0)
    (\_ ->
    1)
    p

size_nat :: Prelude.Integer -> Nat
size_nat p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 -> S
    (size_nat p0))
    (\p0 -> S
    (size_nat p0))
    (\_ -> S
    O)
    p

size :: Prelude.Integer -> Prelude.Integer
size p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    succ (size p0))
    (\p0 ->
    succ (size p0))
    (\_ ->
    1)
    p

compare_cont :: Prelude.Integer -> Prelude.Integer -> Comparison ->
                Comparison
compare_cont x y r =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      compare_cont p q r)
      (\q ->
      compare_cont p q Gt)
      (\_ ->
      Gt)
      y)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      compare_cont p q Lt)
      (\q ->
      compare_cont p q r)
      (\_ ->
      Gt)
      y)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      Lt)
      (\q ->
      Lt)
      (\_ ->
      r)
      y)
    x

compare :: Prelude.Integer -> Prelude.Integer -> Comparison
compare x y =
  compare_cont x y Eq

min :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min p p' =
  case compare p p' of {
   Gt -> p';
   _ -> p}

max :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max p p' =
  case compare p p' of {
   Gt -> p;
   _ -> p'}

eqb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb0 p q =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      eqb0 p0 q0)
      (\p1 ->
      Prelude.False)
      (\_ ->
      Prelude.False)
      q)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p1 ->
      Prelude.False)
      (\q0 ->
      eqb0 p0 q0)
      (\_ ->
      Prelude.False)
      q)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      q)
    p

leb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb x y =
  case compare x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb x y =
  case compare x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

sqrtrem_step :: (Prelude.Integer -> Prelude.Integer) -> (Prelude.Integer ->
                Prelude.Integer) -> ((,) Prelude.Integer Mask) -> (,)
                Prelude.Integer Mask
sqrtrem_step f g p =
  case p of {
   (,) s y ->
    case y of {
     IsPos r ->
      let {
       s' = (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) ((\x -> (Prelude.*) 2 x)
        s)}
      in
      let {r' = g (f r)} in
      case leb s' r' of {
       Prelude.True -> (,) ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1) s)
        (sub_mask r' s');
       Prelude.False -> (,) ((\x -> (Prelude.*) 2 x) s) (IsPos r')};
     _ -> (,) ((\x -> (Prelude.*) 2 x) s)
      (sub_mask (g (f 1)) ((\x -> (Prelude.*) 2 x) ((\x -> (Prelude.*) 2 x)
        1)))}}

sqrtrem :: Prelude.Integer -> (,) Prelude.Integer Mask
sqrtrem p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) x) (\x ->
        (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) x) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> (Prelude.*) 2 x) x) (\x ->
        (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) x) (sqrtrem p1))
      (\_ -> (,) 1 (IsPos ((\x -> (Prelude.*) 2 x)
      1)))
      p0)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1) x) (\x ->
        (\x -> (Prelude.*) 2 x) x) (sqrtrem p1))
      (\p1 ->
      sqrtrem_step (\x -> (\x -> (Prelude.*) 2 x) x) (\x ->
        (\x -> (Prelude.*) 2 x) x) (sqrtrem p1))
      (\_ -> (,) 1 (IsPos
      1))
      p0)
    (\_ -> (,) 1
    IsNul)
    p

sqrt :: Prelude.Integer -> Prelude.Integer
sqrt p =
  fst (sqrtrem p)

gcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcdn n a b =
  case n of {
   O -> 1;
   S n0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\a' ->
      (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
        (\b' ->
        case compare a' b' of {
         Eq -> a;
         Lt -> gcdn n0 (sub b' a') a;
         Gt -> gcdn n0 (sub a' b') b})
        (\b0 ->
        gcdn n0 a b0)
        (\_ ->
        1)
        b)
      (\a0 ->
      (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
        (\p ->
        gcdn n0 a0 b)
        (\b0 -> (\x -> (Prelude.*) 2 x)
        (gcdn n0 a0 b0))
        (\_ ->
        1)
        b)
      (\_ ->
      1)
      a}

gcd :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd a b =
  gcdn (plus (size_nat a) (size_nat b)) a b

ggcdn :: Nat -> Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcdn n a b =
  case n of {
   O -> (,) 1 ((,) a b);
   S n0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\a' ->
      (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
        (\b' ->
        case compare a' b' of {
         Eq -> (,) a ((,) 1 1);
         Lt ->
          case ggcdn n0 (sub b' a') a of {
           (,) g p ->
            case p of {
             (,) ba aa -> (,) g ((,) aa
              (add aa ((\x -> (Prelude.*) 2 x) ba)))}};
         Gt ->
          case ggcdn n0 (sub a' b') b of {
           (,) g p ->
            case p of {
             (,) ab bb -> (,) g ((,) (add bb ((\x -> (Prelude.*) 2 x) ab))
              bb)}}})
        (\b0 ->
        case ggcdn n0 a b0 of {
         (,) g p ->
          case p of {
           (,) aa bb -> (,) g ((,) aa ((\x -> (Prelude.*) 2 x) bb))}})
        (\_ -> (,) 1 ((,) a
        1))
        b)
      (\a0 ->
      (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
        (\p ->
        case ggcdn n0 a0 b of {
         (,) g p0 ->
          case p0 of {
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
  ggcdn (plus (size_nat a) (size_nat b)) a b

nsucc_double :: Prelude.Integer -> Prelude.Integer
nsucc_double x =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> 
    1)
    (\p ->  ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p))
    x

ndouble :: Prelude.Integer -> Prelude.Integer
ndouble n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p ->  ((\x -> (Prelude.*) 2 x)
    p))
    n

lor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor p q =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (lor p0 q0))
      (\q0 -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (lor p0 q0))
      (\_ ->
      p)
      q)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      (lor p0 q0))
      (\q0 -> (\x -> (Prelude.*) 2 x)
      (lor p0 q0))
      (\_ -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      p0)
      q)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      q)
      (\q0 -> (\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      q0)
      (\_ ->
      q)
      q)
    p

land :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land p q =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      nsucc_double (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ -> 
      1)
      q)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      ndouble (land p0 q0))
      (\q0 ->
      ndouble (land p0 q0))
      (\_ ->
      0)
      q)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 -> 
      1)
      (\q0 ->
      0)
      (\_ -> 
      1)
      q)
    p

ldiff :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff p q =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      nsucc_double (ldiff p0 q0))
      (\_ ->  ((\x -> (Prelude.*) 2 x)
      p0))
      q)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\q0 ->
      ndouble (ldiff p0 q0))
      (\_ -> 
      p)
      q)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      0)
      (\q0 -> 
      1)
      (\_ ->
      0)
      q)
    p

lxor :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor p q =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\_ ->  ((\x -> (Prelude.*) 2 x)
      p0))
      q)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->
      nsucc_double (lxor p0 q0))
      (\q0 ->
      ndouble (lxor p0 q0))
      (\_ ->  ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      p0))
      q)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q0 ->  ((\x -> (Prelude.*) 2 x)
      q0))
      (\q0 ->  ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
      q0))
      (\_ ->
      0)
      q)
    p

shiftl_nat :: Prelude.Integer -> Nat -> Prelude.Integer
shiftl_nat p n =
  nat_iter n (\x -> (\x -> (Prelude.*) 2 x) x) p

shiftr_nat :: Prelude.Integer -> Nat -> Prelude.Integer
shiftr_nat p n =
  nat_iter n div2 p

shiftl :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl p n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    p)
    (\n0 ->
    iter n0 (\x -> (\x -> (Prelude.*) 2 x) x) p)
    n

shiftr :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr p n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    p)
    (\n0 ->
    iter n0 div2 p)
    n

testbit_nat :: Prelude.Integer -> Nat -> Prelude.Bool
testbit_nat p n =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    case n of {
     O -> Prelude.True;
     S n' -> testbit_nat p0 n'})
    (\p0 ->
    case n of {
     O -> Prelude.False;
     S n' -> testbit_nat p0 n'})
    (\_ ->
    case n of {
     O -> Prelude.True;
     S n0 -> Prelude.False})
    p

testbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
testbit p n =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Prelude.True)
      (\n0 ->
      testbit p0 (pred_N n0))
      n)
    (\p0 ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Prelude.False)
      (\n0 ->
      testbit p0 (pred_N n0))
      n)
    (\_ ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      n)
    p

iter_op :: (a1 -> a1 -> a1) -> Prelude.Integer -> a1 -> a1
iter_op op p a =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    op a (iter_op op p0 (op a a)))
    (\p0 ->
    iter_op op p0 (op a a))
    (\_ ->
    a)
    p

to_nat :: Prelude.Integer -> Nat
to_nat x =
  iter_op plus x (S O)

of_nat :: Nat -> Prelude.Integer
of_nat n =
  case n of {
   O -> 1;
   S x ->
    case x of {
     O -> 1;
     S n0 -> succ (of_nat x)}}

of_succ_nat :: Nat -> Prelude.Integer
of_succ_nat n =
  case n of {
   O -> 1;
   S x -> succ (of_succ_nat x)}

eq_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec x y =
  positive_rec (\p h y0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0))
      (\p0 ->
      Right)
      (\_ ->
      Right)
      y0) (\p h y0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (h p0))
      (\_ ->
      Right)
      y0) (\y0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p ->
      Right)
      (\p ->
      Right)
      (\_ ->
      Left)
      y0) x y

peano_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rect a f p =
  let {
   f2 = peano_rect (f 1 a) (\p0 x ->
          f (succ ((\x -> (Prelude.*) 2 x) p0))
            (f ((\x -> (Prelude.*) 2 x) p0) x))}
  in
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\q ->
    f ((\x -> (Prelude.*) 2 x) q) (f2 q))
    (\q ->
    f2 q)
    (\_ ->
    a)
    p

peano_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rec =
  peano_rect

data PeanoView =
   PeanoOne
 | PeanoSucc Prelude.Integer PeanoView

peanoView_rect :: a1 -> (Prelude.Integer -> PeanoView -> a1 -> a1) ->
                  Prelude.Integer -> PeanoView -> a1
peanoView_rect f f0 p p0 =
  case p0 of {
   PeanoOne -> f;
   PeanoSucc p1 p2 -> f0 p1 p2 (peanoView_rect f f0 p1 p2)}

peanoView_rec :: a1 -> (Prelude.Integer -> PeanoView -> a1 -> a1) ->
                 Prelude.Integer -> PeanoView -> a1
peanoView_rec =
  peanoView_rect

peanoView_xO :: Prelude.Integer -> PeanoView -> PeanoView
peanoView_xO p q =
  case q of {
   PeanoOne -> PeanoSucc 1 PeanoOne;
   PeanoSucc p0 q0 -> PeanoSucc (succ ((\x -> (Prelude.*) 2 x) p0))
    (PeanoSucc ((\x -> (Prelude.*) 2 x) p0) (peanoView_xO p0 q0))}

peanoView_xI :: Prelude.Integer -> PeanoView -> PeanoView
peanoView_xI p q =
  case q of {
   PeanoOne -> PeanoSucc (succ 1) (PeanoSucc 1 PeanoOne);
   PeanoSucc p0 q0 -> PeanoSucc
    (succ ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1) p0)) (PeanoSucc
    ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1) p0) (peanoView_xI p0 q0))}

peanoView :: Prelude.Integer -> PeanoView
peanoView p =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p0 ->
    peanoView_xI p0 (peanoView p0))
    (\p0 ->
    peanoView_xO p0 (peanoView p0))
    (\_ ->
    PeanoOne)
    p

peanoView_iter :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer ->
                  PeanoView -> a1
peanoView_iter a f p q =
  case q of {
   PeanoOne -> a;
   PeanoSucc p0 q0 -> f p0 (peanoView_iter a f p0 q0)}

eqb_spec :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec x y =
  iff_reflect (eqb0 x y)

switch_Eq :: Comparison -> Comparison -> Comparison
switch_Eq c c' =
  case c' of {
   Eq -> c;
   x -> x}

mask2cmp :: Mask -> Comparison
mask2cmp p =
  case p of {
   IsNul -> Eq;
   IsPos p0 -> Gt;
   IsNeg -> Lt}

leb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec0 x y =
  iff_reflect (leb x y)

ltb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec0 x y =
  iff_reflect (ltb x y)

max_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
max_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat n (max n m) __ (hl __);
   _ -> compat m (max n m) __ (hr __)}

max_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case n m x x0 x1 =
  max_case_strong n m x (\_ -> x0) (\_ -> x1)

max_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec n m =
  max_case n m (\x y _ h0 -> h0) Left Right

min_case_strong :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                   Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (() ->
                   a1) -> a1
min_case_strong n m compat hl hr =
  let {c = compSpec2Type n m (compare n m)} in
  case c of {
   CompGtT -> compat m (min n m) __ (hr __);
   _ -> compat n (min n m) __ (hl __)}

min_case :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
            Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case n m x x0 x1 =
  min_case_strong n m x (\_ -> x0) (\_ -> x1)

min_dec :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec n m =
  min_case n m (\x y _ h0 -> h0) Left Right

max_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong0 n m x x0 =
  max_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case0 n m x x0 =
  max_case_strong0 n m (\_ -> x) (\_ -> x0)

max_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec0 =
  max_dec

min_case_strong0 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong0 n m x x0 =
  min_case_strong n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case0 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case0 n m x x0 =
  min_case_strong0 n m (\_ -> x) (\_ -> x0)

min_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec0 =
  min_dec

type T0 = Prelude.Integer

zero :: Prelude.Integer
zero =
  0

one :: Prelude.Integer
one =
   1

two :: Prelude.Integer
two =
   ((\x -> (Prelude.*) 2 x) 1)

succ_double :: Prelude.Integer -> Prelude.Integer
succ_double x =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> 
    1)
    (\p ->  ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p))
    x

double :: Prelude.Integer -> Prelude.Integer
double n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p ->  ((\x -> (Prelude.*) 2 x)
    p))
    n

succ0 :: Prelude.Integer -> Prelude.Integer
succ0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> 
    1)
    (\p -> 
    (succ p))
    n

pred0 :: Prelude.Integer -> Prelude.Integer
pred0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p ->
    pred_N p)
    n

succ_pos :: Prelude.Integer -> Prelude.Integer
succ_pos n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    1)
    (\p ->
    succ p)
    n

add0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
add0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    m)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      n)
      (\q -> 
      (add p q))
      m)
    n

sub0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\n' ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      n)
      (\m' ->
      case sub_mask n' m' of {
       IsPos p ->  p;
       _ -> 0})
      m)
    n

mul0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      0)
      (\q -> 
      (mul p q))
      m)
    n

compare0 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Eq)
      (\m' ->
      Lt)
      m)
    (\n' ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Gt)
      (\m' ->
      compare n' m')
      m)
    n

eqb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb1 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Prelude.True)
      (\p ->
      Prelude.False)
      m)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Prelude.False)
      (\q ->
      eqb0 p q)
      m)
    n

leb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb0 x y =
  case compare0 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb0 x y =
  case compare0 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

min0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min0 n n' =
  case compare0 n n' of {
   Gt -> n';
   _ -> n}

max0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max0 n n' =
  case compare0 n n' of {
   Gt -> n;
   _ -> n'}

div0 :: Prelude.Integer -> Prelude.Integer
div0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p -> 
      p)
      (\p -> 
      p)
      (\_ ->
      0)
      p0)
    n

even :: Prelude.Integer -> Prelude.Bool
even n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    Prelude.True)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    n

odd :: Prelude.Integer -> Prelude.Bool
odd n =
  negb (even n)

pow0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow0 n p =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> 
    1)
    (\p0 ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      0)
      (\q -> 
      (pow q p0))
      n)
    p

square0 :: Prelude.Integer -> Prelude.Integer
square0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p -> 
    (square p))
    n

log2 :: Prelude.Integer -> Prelude.Integer
log2 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p -> 
      (size p))
      (\p -> 
      (size p))
      (\_ ->
      0)
      p0)
    n

size0 :: Prelude.Integer -> Prelude.Integer
size0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p -> 
    (size p))
    n

size_nat0 :: Prelude.Integer -> Nat
size_nat0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    O)
    (\p ->
    size_nat p)
    n

pos_div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                Prelude.Integer
pos_div_eucl a b =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = succ_double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\a' ->
    case pos_div_eucl a' b of {
     (,) q r ->
      let {r' = double r} in
      case leb0 b r' of {
       Prelude.True -> (,) (succ_double q) (sub0 r' b);
       Prelude.False -> (,) (double q) r'}})
    (\_ ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ -> (,) 0 (
      1))
      (\p ->
      (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
        (\p0 -> (,) 0 (
        1))
        (\p0 -> (,) 0 (
        1))
        (\_ -> (,) ( 1)
        0)
        p)
      b)
    a

div_eucl :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
            Prelude.Integer
div_eucl a b =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> (,) 0
    0)
    (\na ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ -> (,) 0
      a)
      (\p ->
      pos_div_eucl na b)
      b)
    a

div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div a b =
  fst (div_eucl a b)

modulo :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo a b =
  snd (div_eucl a b)

gcd0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd0 a b =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    b)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      a)
      (\q -> 
      (gcd p q))
      b)
    a

ggcd0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcd0 a b =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> (,) b ((,) 0 (
    1)))
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ -> (,) a ((,) ( 1)
      0))
      (\q ->
      case ggcd p q of {
       (,) g p0 ->
        case p0 of {
         (,) aa bb -> (,) ( g) ((,) ( aa) ( bb))}})
      b)
    a

sqrtrem0 :: Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
sqrtrem0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ -> (,) 0
    0)
    (\p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) ( s) ( r);
       _ -> (,) ( s) 0}})
    n

sqrt0 :: Prelude.Integer -> Prelude.Integer
sqrt0 n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p -> 
    (sqrt p))
    n

lor0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    m)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      n)
      (\q -> 
      (lor p q))
      m)
    n

land0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      0)
      (\q ->
      land p q)
      m)
    n

ldiff0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      n)
      (\q ->
      ldiff p q)
      m)
    n

lxor0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor0 n m =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    m)
    (\p ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      n)
      (\q ->
      lxor p q)
      m)
    n

shiftl_nat0 :: Prelude.Integer -> Nat -> Prelude.Integer
shiftl_nat0 a n =
  nat_iter n double a

shiftr_nat0 :: Prelude.Integer -> Nat -> Prelude.Integer
shiftr_nat0 a n =
  nat_iter n div0 a

shiftl0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl0 a n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\a0 -> 
    (shiftl a0 n))
    a

shiftr0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr0 a n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    a)
    (\p ->
    iter p div0 a)
    n

testbit_nat0 :: Prelude.Integer -> Nat -> Prelude.Bool
testbit_nat0 a =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ x ->
    Prelude.False)
    (\p ->
    testbit_nat p)
    a

testbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
testbit0 a n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    Prelude.False)
    (\p ->
    testbit p n)
    a

to_nat0 :: Prelude.Integer -> Nat
to_nat0 a =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    O)
    (\p ->
    to_nat p)
    a

of_nat0 :: Nat -> Prelude.Integer
of_nat0 n =
  case n of {
   O -> 0;
   S n' ->  (of_succ_nat n')}

iter0 :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter0 n f x =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    x)
    (\p ->
    iter p f x)
    n

eq_dec0 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec0 n m =
  n_rec (\m0 ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Left)
      (\p ->
      Right)
      m0) (\p m0 ->
    (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
      (\_ ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0))
      m0) n m

discr :: Prelude.Integer -> Sumor Prelude.Integer
discr n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    Inright)
    (\p -> Inleft
    p)
    n

binary_rect :: a1 -> (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1
               -> a1) -> Prelude.Integer -> a1
binary_rect f0 f2 fS2 n =
  let {f2' = \p -> f2 ( p)} in
  let {fS2' = \p -> fS2 ( p)} in
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    f0)
    (\p ->
    positive_rect fS2' f2' (fS2 0 f0) p)
    n

binary_rec :: a1 -> (Prelude.Integer -> a1 -> a1) -> (Prelude.Integer -> a1
              -> a1) -> Prelude.Integer -> a1
binary_rec =
  binary_rect

peano_rect0 :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rect0 f0 f n =
  let {f' = \p -> f ( p)} in
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    f0)
    (\p ->
    peano_rect (f 0 f0) f' p)
    n

peano_rec0 :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
peano_rec0 =
  peano_rect0

leb_spec1 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec1 x y =
  iff_reflect (leb0 x y)

ltb_spec1 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec1 x y =
  iff_reflect (ltb0 x y)

recursion :: a1 -> (Prelude.Integer -> a1 -> a1) -> Prelude.Integer -> a1
recursion =
  peano_rect0

sqrt_up :: Prelude.Integer -> Prelude.Integer
sqrt_up a =
  case compare0 0 a of {
   Lt -> succ0 (sqrt0 (pred0 a));
   _ -> 0}

log2_up :: Prelude.Integer -> Prelude.Integer
log2_up a =
  case compare0 ( 1) a of {
   Lt -> succ0 (log2 (pred0 a));
   _ -> 0}

lcm :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm a b =
  mul0 a (div b (gcd0 a b))

eqb_spec0 :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec0 x y =
  iff_reflect (eqb1 x y)

b2n :: Prelude.Bool -> Prelude.Integer
b2n b =
  case b of {
   Prelude.True ->  1;
   Prelude.False -> 0}

setbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
setbit a n =
  lor0 a (shiftl0 ( 1) n)

clearbit :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
clearbit a n =
  ldiff0 a (shiftl0 ( 1) n)

ones :: Prelude.Integer -> Prelude.Integer
ones n =
  pred0 (shiftl0 ( 1) n)

lnot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lnot a n =
  lxor0 a (ones n)

max_case_strong1 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat n (max0 n m) __ (hl __);
   _ -> compat m (max0 n m) __ (hr __)}

max_case1 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case1 n m x x0 x1 =
  max_case_strong1 n m x (\_ -> x0) (\_ -> x1)

max_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec1 n m =
  max_case1 n m (\x y _ h0 -> h0) Left Right

min_case_strong1 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong1 n m compat hl hr =
  let {c = compSpec2Type n m (compare0 n m)} in
  case c of {
   CompGtT -> compat m (min0 n m) __ (hr __);
   _ -> compat n (min0 n m) __ (hl __)}

min_case1 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case1 n m x x0 x1 =
  min_case_strong1 n m x (\_ -> x0) (\_ -> x1)

min_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec1 n m =
  min_case1 n m (\x y _ h0 -> h0) Left Right

max_case_strong2 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong2 n m x x0 =
  max_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case2 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case2 n m x x0 =
  max_case_strong2 n m (\_ -> x) (\_ -> x0)

max_dec2 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec2 =
  max_dec1

min_case_strong2 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong2 n m x x0 =
  min_case_strong1 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case2 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case2 n m x x0 =
  min_case_strong2 n m (\_ -> x) (\_ -> x0)

min_dec2 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec2 =
  min_dec1

type T1 = Prelude.Integer

zero0 :: Prelude.Integer
zero0 =
  0

one0 :: Prelude.Integer
one0 =
   1

two0 :: Prelude.Integer
two0 =
   ((\x -> (Prelude.*) 2 x) 1)

double0 :: Prelude.Integer -> Prelude.Integer
double0 x =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p ->  ((\x -> (Prelude.*) 2 x)
    p))
    (\p -> (\x -> (Prelude.*) x (-1)) ((\x -> (Prelude.*) 2 x)
    p))
    x

succ_double0 :: Prelude.Integer -> Prelude.Integer
succ_double0 x =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ -> 
    1)
    (\p ->  ((\x -> (Prelude.+) ((Prelude.*) 2 x) 1)
    p))
    (\p -> (\x -> (Prelude.*) x (-1))
    (pred_double p))
    x

pred_double0 :: Prelude.Integer -> Prelude.Integer
pred_double0 x =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
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
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      double0 (pos_sub p q))
      (\q ->
      succ_double0 (pos_sub p q))
      (\_ ->  ((\x -> (Prelude.*) 2 x)
      p))
      y)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\q ->
      pred_double0 (pos_sub p q))
      (\q ->
      double0 (pos_sub p q))
      (\_ -> 
      (pred_double p))
      y)
    (\_ ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
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
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\x0 -> (\x -> (Prelude.*) x (-1))
    x0)
    (\x0 -> 
    x0)
    x

succ1 :: Prelude.Integer -> Prelude.Integer
succ1 x =
  add1 x ( 1)

pred1 :: Prelude.Integer -> Prelude.Integer
pred1 x =
  add1 x ((\x -> (Prelude.*) x (-1)) 1)

sub1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
sub1 m n =
  add1 m (opp n)

mul1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
mul1 = (Prelude.*)

pow_pos :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow_pos z n =
  iter n (mul1 z) ( 1)

pow1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
pow1 x y =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ -> 
    1)
    (\p ->
    pow_pos x p)
    (\p ->
    0)
    y

square1 :: Prelude.Integer -> Prelude.Integer
square1 x =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    (square p))
    (\p -> 
    (square p))
    x

compare1 :: Prelude.Integer -> Prelude.Integer -> Comparison
compare1 x y =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Eq)
      (\y' ->
      Lt)
      (\y' ->
      Gt)
      y)
    (\x' ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Gt)
      (\y' ->
      compare x' y')
      (\y' ->
      Gt)
      y)
    (\x' ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Lt)
      (\y' ->
      Lt)
      (\y' ->
      compOpp (compare x' y'))
      y)
    x

sgn :: Prelude.Integer -> Prelude.Integer
sgn z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    1)
    (\p -> (\x -> (Prelude.*) x (-1))
    1)
    z

leb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
leb1 x y =
  case compare1 x y of {
   Gt -> Prelude.False;
   _ -> Prelude.True}

ltb1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
ltb1 x y =
  case compare1 x y of {
   Lt -> Prelude.True;
   _ -> Prelude.False}

geb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
geb = (Prelude.>=)

gtb :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
gtb = (Prelude.>)

eqb2 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
eqb2 = (Prelude.==)

max1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
max1 n m =
  case compare1 n m of {
   Lt -> m;
   _ -> n}

min1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
min1 n m =
  case compare1 n m of {
   Gt -> m;
   _ -> n}

abs :: Prelude.Integer -> Prelude.Integer
abs z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    p)
    (\p -> 
    p)
    z

abs_nat :: Prelude.Integer -> Nat
abs_nat z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    O)
    (\p ->
    to_nat p)
    (\p ->
    to_nat p)
    z

abs_N :: Prelude.Integer -> Prelude.Integer
abs_N z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    p)
    (\p -> 
    p)
    z

to_nat1 :: Prelude.Integer -> Nat
to_nat1 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    O)
    (\p ->
    to_nat p)
    (\p ->
    O)
    z

to_N :: Prelude.Integer -> Prelude.Integer
to_N z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    p)
    (\p ->
    0)
    z

of_nat1 :: Nat -> Prelude.Integer
of_nat1 n =
  case n of {
   O -> 0;
   S n0 ->  (of_succ_nat n0)}

of_N :: Prelude.Integer -> Prelude.Integer
of_N n =
  (\fO fPos z ->
                   if (Prelude.==) z 0 then fO ()
                   else fPos z)
    (\_ ->
    0)
    (\p -> 
    p)
    n

to_pos :: Prelude.Integer -> Prelude.Integer
to_pos z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    1)
    (\p ->
    p)
    (\p ->
    1)
    z

iter1 :: Prelude.Integer -> (a1 -> a1) -> a1 -> a1
iter1 n f x =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    x)
    (\p ->
    iter p f x)
    (\p ->
    x)
    n

pos_div_eucl0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
                 Prelude.Integer
pos_div_eucl0 a b =
  (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = add1 (mul1 ( ((\x -> (Prelude.*) 2 x) 1)) r) ( 1)} in
      case ltb1 r' b of {
       Prelude.True -> (,) (mul1 ( ((\x -> (Prelude.*) 2 x) 1)) q) r';
       Prelude.False -> (,)
        (add1 (mul1 ( ((\x -> (Prelude.*) 2 x) 1)) q) ( 1)) (sub1 r' b)}})
    (\a' ->
    case pos_div_eucl0 a' b of {
     (,) q r ->
      let {r' = mul1 ( ((\x -> (Prelude.*) 2 x) 1)) r} in
      case ltb1 r' b of {
       Prelude.True -> (,) (mul1 ( ((\x -> (Prelude.*) 2 x) 1)) q) r';
       Prelude.False -> (,)
        (add1 (mul1 ( ((\x -> (Prelude.*) 2 x) 1)) q) ( 1)) (sub1 r' b)}})
    (\_ ->
    case leb1 ( ((\x -> (Prelude.*) 2 x) 1)) b of {
     Prelude.True -> (,) 0 ( 1);
     Prelude.False -> (,) ( 1) 0})
    a

div_eucl0 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
             Prelude.Integer
div_eucl0 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ -> (,) 0
    0)
    (\a' ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ -> (,) 0
      0)
      (\p ->
      pos_div_eucl0 a' b)
      (\b' ->
      case pos_div_eucl0 a' ( b') of {
       (,) q r ->
        (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
          (\_ -> (,) (opp q)
          0)
          (\p -> (,) (opp (add1 q ( 1)))
          (add1 b r))
          (\p -> (,) (opp (add1 q ( 1)))
          (add1 b r))
          r})
      b)
    (\a' ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ -> (,) 0
      0)
      (\p ->
      case pos_div_eucl0 a' b of {
       (,) q r ->
        (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
          (\_ -> (,) (opp q)
          0)
          (\p0 -> (,) (opp (add1 q ( 1)))
          (sub1 b r))
          (\p0 -> (,) (opp (add1 q ( 1)))
          (sub1 b r))
          r})
      (\b' ->
      case pos_div_eucl0 a' ( b') of {
       (,) q r -> (,) q (opp r)})
      b)
    a

div1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div1 a b =
  case div_eucl0 a b of {
   (,) q x -> q}

modulo0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo0 a b =
  case div_eucl0 a b of {
   (,) x r -> r}

quotrem :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
           Prelude.Integer
quotrem a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ -> (,) 0
    0)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ -> (,) 0
      a)
      (\b0 ->
      case pos_div_eucl a0 ( b0) of {
       (,) q r -> (,) (of_N q) (of_N r)})
      (\b0 ->
      case pos_div_eucl a0 ( b0) of {
       (,) q r -> (,) (opp (of_N q)) (of_N r)})
      b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ -> (,) 0
      a)
      (\b0 ->
      case pos_div_eucl a0 ( b0) of {
       (,) q r -> (,) (opp (of_N q)) (opp (of_N r))})
      (\b0 ->
      case pos_div_eucl a0 ( b0) of {
       (,) q r -> (,) (of_N q) (opp (of_N r))})
      b)
    a

quot :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
quot a b =
  fst (quotrem a b)

rem :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
rem a b =
  snd (quotrem a b)

even0 :: Prelude.Integer -> Prelude.Bool
even0 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    Prelude.True)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Prelude.False)
      (\p0 ->
      Prelude.True)
      (\_ ->
      Prelude.False)
      p)
    z

odd0 :: Prelude.Integer -> Prelude.Bool
odd0 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    Prelude.False)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      p)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 ->
      Prelude.True)
      (\p0 ->
      Prelude.False)
      (\_ ->
      Prelude.True)
      p)
    z

div3 :: Prelude.Integer -> Prelude.Integer
div3 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 -> 
      (div2 p))
      (\p0 -> 
      (div2 p))
      (\_ ->
      0)
      p)
    (\p -> (\x -> (Prelude.*) x (-1))
    (div2_up p))
    z

quot2 :: Prelude.Integer -> Prelude.Integer
quot2 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 -> 
      (div2 p))
      (\p0 -> 
      (div2 p))
      (\_ ->
      0)
      p)
    (\p ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p0 -> (\x -> (Prelude.*) x (-1))
      (div2 p))
      (\p0 -> (\x -> (Prelude.*) x (-1))
      (div2 p))
      (\_ ->
      0)
      p)
    z

log0 :: Prelude.Integer -> Prelude.Integer
log0 z =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p0 ->
    (\xI xO xH p ->
                   if (Prelude.==) p 1 then xH ()
                   else if Prelude.even p then xO (Prelude.quot p 2)
                        else xI (Prelude.quot p 2))
      (\p -> 
      (size p))
      (\p -> 
      (size p))
      (\_ ->
      0)
      p0)
    (\p ->
    0)
    z

sqrtrem1 :: Prelude.Integer -> (,) Prelude.Integer Prelude.Integer
sqrtrem1 n =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ -> (,) 0
    0)
    (\p ->
    case sqrtrem p of {
     (,) s m ->
      case m of {
       IsPos r -> (,) ( s) ( r);
       _ -> (,) ( s) 0}})
    (\p -> (,) 0
    0)
    n

sqrt1 :: Prelude.Integer -> Prelude.Integer
sqrt1 n =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\p -> 
    (sqrt p))
    (\p ->
    0)
    n

gcd1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
gcd1 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    abs b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      abs a)
      (\b0 -> 
      (gcd a0 b0))
      (\b0 -> 
      (gcd a0 b0))
      b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      abs a)
      (\b0 -> 
      (gcd a0 b0))
      (\b0 -> 
      (gcd a0 b0))
      b)
    a

ggcd1 :: Prelude.Integer -> Prelude.Integer -> (,) Prelude.Integer
         ((,) Prelude.Integer Prelude.Integer)
ggcd1 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ -> (,) (abs b) ((,) 0
    (sgn b)))
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
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
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
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

testbit1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool
testbit1 a n =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    odd0 a)
    (\p ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Prelude.False)
      (\a0 ->
      testbit a0 ( p))
      (\a0 ->
      negb (testbit0 (pred_N a0) ( p)))
      a)
    (\p ->
    Prelude.False)
    n

shiftl1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftl1 a n =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    a)
    (\p ->
    iter p (mul1 ( ((\x -> (Prelude.*) 2 x) 1))) a)
    (\p ->
    iter p div3 a)
    n

shiftr1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
shiftr1 a n =
  shiftl1 a (opp n)

lor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lor1 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      a)
      (\b0 -> 
      (lor a0 b0))
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (ldiff0 (pred_N b0) ( a0))))
      b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      a)
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (ldiff0 (pred_N a0) ( b0))))
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (land0 (pred_N a0) (pred_N b0))))
      b)
    a

land1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
land1 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      0)
      (\b0 ->
      of_N (land a0 b0))
      (\b0 ->
      of_N (ldiff0 ( a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      0)
      (\b0 ->
      of_N (ldiff0 ( b0) (pred_N a0)))
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (lor0 (pred_N a0) (pred_N b0))))
      b)
    a

ldiff1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
ldiff1 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    0)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      a)
      (\b0 ->
      of_N (ldiff a0 b0))
      (\b0 ->
      of_N (land0 ( a0) (pred_N b0)))
      b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      a)
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (lor0 (pred_N a0) ( b0))))
      (\b0 ->
      of_N (ldiff0 (pred_N b0) (pred_N a0)))
      b)
    a

lxor1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lxor1 a b =
  (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
    (\_ ->
    b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      a)
      (\b0 ->
      of_N (lxor a0 b0))
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (lxor0 ( a0) (pred_N b0))))
      b)
    (\a0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      a)
      (\b0 -> (\x -> (Prelude.*) x (-1))
      (succ_pos (lxor0 (pred_N a0) ( b0))))
      (\b0 ->
      of_N (lxor0 (pred_N a0) (pred_N b0)))
      b)
    a

eq_dec1 :: Prelude.Integer -> Prelude.Integer -> Sumbool
eq_dec1 x y =
  z_rec (\y0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Left)
      (\p ->
      Right)
      (\p ->
      Right)
      y0) (\p y0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0))
      (\p0 ->
      Right)
      y0) (\p y0 ->
    (\fO fPos fNeg z ->
                   if (Prelude.==) z 0 then fO ()
                   else if (Prelude.>) z 0 then fPos z
                        else fNeg ((Prelude.*) z (-1)))
      (\_ ->
      Right)
      (\p0 ->
      Right)
      (\p0 ->
      sumbool_rec (\_ -> eq_rec_r p0 Left p) (\_ -> Right) (eq_dec p p0))
      y0) x y

leb_spec2 :: Prelude.Integer -> Prelude.Integer -> Reflect
leb_spec2 x y =
  iff_reflect (leb1 x y)

ltb_spec2 :: Prelude.Integer -> Prelude.Integer -> Reflect
ltb_spec2 x y =
  iff_reflect (ltb1 x y)

sqrt_up0 :: Prelude.Integer -> Prelude.Integer
sqrt_up0 a =
  case compare1 0 a of {
   Lt -> succ1 (sqrt1 (pred1 a));
   _ -> 0}

log2_up0 :: Prelude.Integer -> Prelude.Integer
log2_up0 a =
  case compare1 ( 1) a of {
   Lt -> succ1 (log0 (pred1 a));
   _ -> 0}

div4 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div4 =
  quot

modulo1 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
modulo1 =
  rem

lcm0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
lcm0 a b =
  abs (mul1 a (div1 b (gcd1 a b)))

eqb_spec1 :: Prelude.Integer -> Prelude.Integer -> Reflect
eqb_spec1 x y =
  iff_reflect (eqb2 x y)

b2z :: Prelude.Bool -> Prelude.Integer
b2z b =
  case b of {
   Prelude.True ->  1;
   Prelude.False -> 0}

setbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
setbit0 a n =
  lor1 a (shiftl1 ( 1) n)

clearbit0 :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
clearbit0 a n =
  ldiff1 a (shiftl1 ( 1) n)

lnot0 :: Prelude.Integer -> Prelude.Integer
lnot0 a =
  pred1 (opp a)

ones0 :: Prelude.Integer -> Prelude.Integer
ones0 n =
  pred1 (shiftl1 ( 1) n)

max_case_strong3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat n (max1 n m) __ (hl __);
   _ -> compat m (max1 n m) __ (hr __)}

max_case3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
max_case3 n m x x0 x1 =
  max_case_strong3 n m x (\_ -> x0) (\_ -> x1)

max_dec3 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec3 n m =
  max_case3 n m (\x y _ h0 -> h0) Left Right

min_case_strong3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
                    Prelude.Integer -> () -> a1 -> a1) -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong3 n m compat hl hr =
  let {c = compSpec2Type n m (compare1 n m)} in
  case c of {
   CompGtT -> compat m (min1 n m) __ (hr __);
   _ -> compat n (min1 n m) __ (hl __)}

min_case3 :: Prelude.Integer -> Prelude.Integer -> (Prelude.Integer ->
             Prelude.Integer -> () -> a1 -> a1) -> a1 -> a1 -> a1
min_case3 n m x x0 x1 =
  min_case_strong3 n m x (\_ -> x0) (\_ -> x1)

min_dec3 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec3 n m =
  min_case3 n m (\x y _ h0 -> h0) Left Right

max_case_strong4 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
max_case_strong4 n m x x0 =
  max_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

max_case4 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
max_case4 n m x x0 =
  max_case_strong4 n m (\_ -> x) (\_ -> x0)

max_dec4 :: Prelude.Integer -> Prelude.Integer -> Sumbool
max_dec4 =
  max_dec3

min_case_strong4 :: Prelude.Integer -> Prelude.Integer -> (() -> a1) -> (()
                    -> a1) -> a1
min_case_strong4 n m x x0 =
  min_case_strong3 n m (\x1 y _ x2 -> eq_rect __ x2 __) x x0

min_case4 :: Prelude.Integer -> Prelude.Integer -> a1 -> a1 -> a1
min_case4 n m x x0 =
  min_case_strong4 n m (\_ -> x) (\_ -> x0)

min_dec4 :: Prelude.Integer -> Prelude.Integer -> Sumbool
min_dec4 =
  min_dec3

fuelIter :: ((a1 ->  a2) -> a1 ->  a2) -> a1 -> Nat ->  a2
fuelIter = (\f a _ -> f (\a0 -> fuelIter f a0 O) a)

fuelFix :: ((a1 ->  a2) -> a1 ->  a2) -> a1 ->  a2
fuelFix = (\f a -> fuelIter f a O)

map :: (a1 -> a2) -> Nat -> (([]) a1) -> ([]) a2
map = (\g _ l -> Prelude.map g l)

map2 :: (a1 -> a2 -> a3) -> Nat -> (([]) a1) -> (([]) a2) -> ([]) a3
map2 = (\g _ l1 l2 -> Prelude.map (\(x,y) -> g x y) (Prelude.zip l1 l2))

fold_left :: (a2 -> a1 -> a2) -> a2 -> Nat -> (([]) a1) -> a2
fold_left = (\g a _ l -> Prelude.foldl g a l)

type Zvec = ([]) Prelude.Integer

zvec_plus :: Nat -> Zvec -> Zvec -> ([]) Prelude.Integer
zvec_plus n v1 v2 =
  map2 add1 n v1 v2

zvec_dot :: Nat -> Zvec -> Zvec -> Prelude.Integer
zvec_dot n v1 v2 =
  fold_left add1 0 n (map2 mul1 n v1 v2)

class0 :: Prelude.Integer -> Prelude.Bool
class0 i =
  geb i 0

correct_class :: Prelude.Integer -> Prelude.Bool -> Prelude.Bool
correct_class i l =
  andb (eqb l (class0 i)) (negb (eqb2 i 0))

zvec_mult_class :: Nat -> Prelude.Bool -> Zvec -> Zvec
zvec_mult_class n l f =
  case l of {
   Prelude.True -> f;
   Prelude.False -> map (mul1 ((\x -> (Prelude.*) x (-1)) 1)) n f}

consb :: Nat -> Zvec -> ([]) Prelude.Integer
consb n v =
  (\a _ v -> a : v) ( 1) n v

inner_perceptron :: Nat -> (([]) ((,) Zvec Prelude.Bool)) -> Zvec -> Option
                    Zvec
inner_perceptron n t w =
  case t of {
   [] -> None;
   (:) p t' ->
    case p of {
     (,) f l ->
      case correct_class (zvec_dot (S n) w (consb n f)) l of {
       Prelude.True -> inner_perceptron n t' w;
       Prelude.False ->
        case inner_perceptron n t'
               (zvec_plus (S n) w (zvec_mult_class (S n) l (consb n f))) of {
         Some w' -> Some w';
         None -> Some
          (zvec_plus (S n) w (zvec_mult_class (S n) l (consb n f)))}}}}

perceptron_aux :: Nat -> (((,) (([]) ((,) Zvec Prelude.Bool)) Zvec) ->  
                  Zvec) -> ((,) (([]) ((,) Zvec Prelude.Bool)) Zvec) ->  
                  Zvec
perceptron_aux n f tw =
  case tw of {
   (,) t w ->
    case inner_perceptron n t w of {
     Some w' ->  (f ((,) t w'));
     None ->  w}}

fueled_perceptron :: Nat -> ((,) (([]) ((,) Zvec Prelude.Bool)) Zvec) -> 
                     Zvec
fueled_perceptron n =
  fuelFix (perceptron_aux n)

