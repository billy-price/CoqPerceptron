module Main where

import System.IO
import Data.IORef

import FueledPerceptron 

import Prelude hiding (Bool, True, False)
import qualified Prelude as P

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

-- Assumes z >= 0
intToNat :: Integral a => a -> Nat
intToNat z
  | z == 0 = O
  | otherwise = S (intToNat (z-1))

debug = P.False

-- Not tail-recursive...should rewrite to use an acc.
read_vec :: Nat -> IO (Prod Zvec Bool)
read_vec nfeats =
  do { lbl <- hGetLine stdin
     ; let l = if read lbl == 0 then False else True -- no error-handling here
     ; if debug then do { putStr "label = "; putStrLn (show lbl) } else return ()
     ; res <- go nfeats
     ; return (Pair res l)
     } 
     where go :: Nat -> IO Zvec
           go n =
             case n of
               O -> return Nil0
               S n' ->
                 do { feat <- hGetLine stdin
                    ; if debug then do { putStr "feat = "; putStrLn (show feat) } else return ()
                    ; rest <- go n'
                    ; return $ Cons0 (intToZ (read feat)) n' rest
                    } 

read_vecs :: Int -> Int -> IO (List (Prod Zvec Bool))
read_vecs nvecs nfeats
  | nvecs <= 0 = return Nil
  | otherwise
  = do { v <- read_vec (intToNat nfeats)
       ; rest <- read_vecs (nvecs-1) nfeats       
       ; return $ Cons v rest 
       }

zero_vec :: Nat -> Zvec
zero_vec O = Nil0
zero_vec (S n') = Cons0 Z0 n' (zero_vec n')

main =
  do { num_vecs  <- hGetLine stdin
     ; if debug then do { putStr "num_vecs = "; putStrLn (show num_vecs) } else return ()
     ; num_feats <- hGetLine stdin
     ; if debug then do { putStr "num_feats = "; putStrLn (show num_feats) } else return ()
     ; let nvecs  = read num_vecs
     ; let nfeats = read num_feats
     ; vs <- read_vecs nvecs nfeats
     ; let w = Cons0 (intToZ 10000) (intToNat nfeats) (zero_vec (intToNat nfeats))
     ; let res = fueled_perceptron O (Pair vs w)
     ; case res of
         Nil0 -> putStrLn "Nil0"
         Cons0 {} -> putStrLn "Cons0"
     } 
