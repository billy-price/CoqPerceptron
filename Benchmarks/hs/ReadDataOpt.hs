module Main where

import System.IO
import Data.IORef

import FueledPerceptronOpt

import Prelude

debug = False

read_vec :: Int -> IO (Zvec, Bool)
read_vec nfeats =
  do { lbl <- hGetLine stdin
     ; let l = if read lbl == 0 then False else True -- no error-handling here
     ; if debug then do { putStr "label = "; putStrLn (show lbl) } else return ()
     ; res <- go nfeats []
     ; return (res, l)
     } 
     where go :: Int -> Zvec -> IO Zvec
           go n acc
             | n == 0 = return $ reverse acc
             | otherwise = 
                 do { feat <- hGetLine stdin
                    ; if debug then do { putStr "feat = "; putStrLn (show feat) } else return ()
                    ; go (n-1) (read feat : acc)
                    } 

read_vecs :: Int -> Int -> IO [(Zvec, Bool)]
read_vecs nvecs nfeats = go nvecs []
  where go n acc 
          | n <= 0 = return (reverse acc)
          | otherwise =
              do { v <- read_vec nfeats
                 ; go (n-1) (v : acc)
                 }

zero_vec :: Int -> Zvec
zero_vec n = take n zeros
  where zeros = 0 : zeros

main =
  do { num_vecs  <- hGetLine stdin
     ; if debug then do { putStr "num_vecs = "; putStrLn (show num_vecs) } else return ()
     ; num_feats <- hGetLine stdin
     ; if debug then do { putStr "num_feats = "; putStrLn (show num_feats) } else return ()
     ; let nvecs  = read num_vecs
     ; let nfeats = read num_feats
     ; vs <- read_vecs nvecs nfeats
     ; let w = 0 : zero_vec nfeats
     ; let res = fueled_perceptron O (vs, w)
     ; case res of
         [] -> putStrLn "empty"
         (bias : _) -> putStrLn $ "bias = " ++ show bias
     } 
