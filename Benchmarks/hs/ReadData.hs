module ReadData where

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
read_vec' :: Nat -> IO Qvec
read_vec' n =
  case n of
    O -> return []
    S n' ->
      do { feat <- hGetLine stdin
         ; if debug then do { putStr "feat = "; putStrLn (show feat) } else return ()
         ; rest <- read_vec' n'
         ; return $ (:) (ratToQ (readRational feat)) rest
         }

read_vec :: Nat -> IO ((,) Qvec P.Bool)
read_vec nfeats =
  do { lbl <- hGetLine stdin
     ; let l = if read lbl == 0 then P.False else P.True -- no error-handling here
     ; if debug then do { putStr "label = "; putStrLn (show lbl) } else return ()
     ; res <- read_vec' nfeats
     ; return (res, l)
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


-- Functionality to Convert from Q to Rat and Print Qvecs and Lists of Qvecs
posToInt :: Positive -> Integer
posToInt p =
  case p of
    XH -> 1
    XI p' -> (2 * (posToInt p') + 1)
    XO p' -> (2 * (posToInt p'))

zToInt :: Z -> Integer
zToInt z =
  case z of
    Z0 -> 0
    Zneg p -> (- posToInt p)
    Zpos p -> (posToInt p)

qToRat :: Q -> Rational
qToRat r =
  case r of
    Qmake z p -> (zToInt z)%(posToInt p)

printQvec :: Qvec -> IO ()
printQvec qv =
  do { 
     ; putStr "<"
     ; go qv
     ; putStr ">"
     }
     where go :: Qvec -> IO ()
           go qv =
             case qv of
               (:) q [] -> putStr (show (qToRat q))
               (:) q qv' -> do { putStr (show (qToRat q)); putStr ", "; go qv' }

putQvec :: Qvec -> IO ()
putQvec qv =
  case qv of
    [] -> putStr ""
    (:) q qv' -> do { putStrLn (show (qToRat q)); putQvec qv' }

printQvecL :: ([]) ((,) Qvec P.Bool) -> IO ()
printQvecL l =
  case l of
    [] -> putStr ""
    (:) ((,) qv lbl) l' -> do { putStr "("
                              ; printQvec qv
                              ; putStr ", "
                              ; putStr (show lbl)
                              ; putStrLn ")"
                              ; printQvecL l'
                              }

putQvecL :: ([]) ((,) Qvec P.Bool) -> IO ()
putQvecL l =
  case l of
    [] -> putStr ""
    (:) ((,) qv lbl) l' -> do { if lbl == P.True then putStrLn "1" else putStrLn "0"
                              ; putQvec qv
                              ; putQvecL l'
}
