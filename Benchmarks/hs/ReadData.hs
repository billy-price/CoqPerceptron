module Main where

import System.IO

import Perceptron

import Prelude hiding (Bool, True, False)
import qualified Prelude as P

import Data.Ratio ( (%), numerator, denominator )
import Data.List ( isInfixOf )


-- Assumes string is a string representation of rational or float
readRational :: String -> Rational
readRational input =
  if (isInfixOf "%" input) then
    read input
  else
    ((read intPart)*(10 ^ length fracPart) + (read fracPart)) % (10 ^ length fracPart)
    where (intPart, fromDot) = span (/='.') input
          fracPart           = if null fromDot then "0" else tail fromDot


-- Assumes z >= 1
intToPos :: Integral a => a -> Positive
intToPos z
  | z == 1 = XH
  | P.odd z = XI (intToPos (z `P.quot` 2))
  | otherwise = XO (intToPos (z `P.quot` 2))

intToZ :: Integral a => a -> Z
intToZ z
  | z == 0 = Z0
  | z < 0  = Zneg (intToPos (P.abs z))
  | otherwise = Zpos (intToPos z)

-- Assumes Z >= 0
intToNat :: Integral a => a -> Nat
intToNat z
  | z == 0 = O
  | otherwise = S (intToNat (z-1))

-- See Assumptions for intToZ and intToPos
ratToQ :: Rational -> Q
ratToQ q =
  Qmake (intToZ (numerator q)) (intToPos (denominator q))

debug = P.False

-- Not tail-recursive...should rewrite to use an acc.
read_vec :: Nat -> IO ((,) Qvec P.Bool)
read_vec nfeats =
  do { lbl <- hGetLine stdin
     ; let l = if read lbl == 0 then P.False else P.True -- no error-handling here
     ; if debug then do { putStr "label = "; putStrLn (show lbl) } else return ()
     ; res <- go nfeats
     ; return (res, l)
     }
     where go :: Nat -> IO Qvec
           go n =
             case n of
               O -> return []
               S n' ->
                 do { feat <- hGetLine stdin
                    ; if debug then do { putStr "feat = "; putStrLn (show feat) } else return ()
                    ; rest <- go n'
                    ; return $ (:) (ratToQ (readRational feat)) rest
                    }

read_vecs :: Int -> Int -> IO (([]) ((,) Qvec P.Bool))
read_vecs nvecs nfeats
  | nvecs <= 0 = return []
  | otherwise
  = do { let feats = intToNat nfeats
       ; v <- read_vec feats
       ; rest <- read_vecs (nvecs-1) nfeats
       ; return $ (:) v rest
       }

zero_vec :: Nat -> Qvec
zero_vec O = []
zero_vec (S n') = (:) (Qmake Z0 XH) (zero_vec n')

main = 
  do { num_vecs  <- hGetLine stdin
     ; if debug then do { putStr "num_vecs = "; putStrLn (show num_vecs) } else return ()
     ; num_feats <- hGetLine stdin
     ; if debug then do { putStr "num_feats = "; putStrLn (show num_feats) } else return ()
     ; let nvecs  = read num_vecs
     ; let nfeats = read num_feats
     ; vs <- read_vecs nvecs nfeats
     ; let w = zero_vec (S (intToNat nfeats))
     ; let res = fueled_perceptron (intToNat nfeats) O vs w
     ; case res of
         None -> putStrLn "None"
         Some {} -> putStrLn "Some"
     }
