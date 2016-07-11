module Main where

import System.IO

import Perceptron
import ReadData

main = 
  do { num_vecs  <- hGetLine stdin
     ; if debug then do { putStr "num_vecs = "; putStrLn (show num_vecs) } else return ()
     ; num_feats <- hGetLine stdin
     ; if debug then do { putStr "num_feats = "; putStrLn (show num_feats) } else return ()
     ; let nvecs  = read num_vecs
     ; let nfeats = read num_feats
     ; vs <- read_vecs nvecs nfeats
     ; w <- read_vec' (S (intToNat nfeats))
     ; let res = inner_perceptron_MCE (intToNat nfeats) vs w
     ; case res of
         None -> putStrLn "Valid Separator"
         Some {} -> putStrLn "Invalid Separator"
     }
