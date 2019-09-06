{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module Respuestas
  where

import SintaxisPL

import Data.List (union)

-- Primera versión

varsOf :: PL -> [Indice]
varsOf phi = case phi of
  Top -> []
  Bot -> []
  Var n -> [n]
  Oneg alpha -> varsOf alpha
  Oand alpha beta -> union (varsOf alpha) (varsOf beta)
  Oor alpha beta -> union (varsOf alpha) (varsOf beta)
  Oimp alpha beta -> union (varsOf alpha) (varsOf beta)

hayConjunciones :: PL -> Bool
hayConjunciones phi = case phi of
  Top -> False
  Bot -> False
  Var n -> False
  Oneg alpha -> hayConjunciones alpha
  Oand alpha beta -> True
  Oor alpha beta -> hayConjunciones alpha || hayConjunciones beta
  Oimp alpha beta -> hayConjunciones alpha || hayConjunciones beta

disy :: PL -> [PL]
disy phi = case phi of
  Top -> []
  Bot -> []
  Var n -> []
  Oneg alpha -> case alpha of
    Oor beta gamma -> (Oneg $ Oor beta gamma) : disy beta ++ disy gamma
    _ -> disy alpha
  Oand alpha beta -> disy alpha ++ disy beta
  Oor alpha beta -> (Oor alpha beta) : disy alpha ++ disy beta
  Oimp alpha beta -> disy alpha ++ disy beta

quitaImpl :: PL -> PL
quitaImpl phi = case phi of
  Top -> Top
  Bot -> Bot
  Var n -> Var n
  Oneg alpha -> Oneg $ quitaImpl alpha
  Oand alpha beta -> Oand (quitaImpl alpha) (quitaImpl beta)
  Oor alpha beta -> Oor (quitaImpl alpha) (quitaImpl beta)
  Oimp alpha beta -> Oor (quitaImpl $ Oneg alpha) (quitaImpl beta) 


-- Segunda versión

reversa :: [a] -> [a]
reversa li = case li of
  [] -> []
  x:xs -> reversa xs ++ [x]

primN :: Int -> [a] -> [a]
primN n li = case n of
  0 -> []
  n -> case li of
    [] -> error $ "No hay suficientes elementos."
    l:ls -> [l] ++ primN (n-1) ls

ultimN :: Int -> [a] -> [a]
ultimN n = primN n . reversa

ultimN2 :: Int -> [a] -> [a]
ultimN2 n l@(x:xs)
  | n > length(l) = error $ "N más grande que la lista"
  | n == length(l) = l
  | otherwise = ultimN2 n xs

hayImplicaciones :: PL -> Bool
hayImplicaciones phi = case phi of
  Top -> False
  Bot -> False
  Var n -> False
  Oneg alpha -> hayImplicaciones alpha
  Oand alpha beta -> hayImplicaciones alpha || hayImplicaciones beta
  Oor alpha beta -> hayImplicaciones alpha || hayImplicaciones beta
  Oimp alpha beta -> True

conj :: PL -> [PL]
conj phi = case phi of
  Top -> []
  Bot -> []
  Var n -> []
  Oneg alpha -> case alpha of
    Oand beta gamma -> (Oneg $ Oand beta gamma) : conj beta ++ conj gamma
    _ -> conj alpha
  Oand alpha beta -> (Oand alpha beta) : conj alpha ++ conj beta
  Oor alpha beta ->  conj alpha ++ conj beta
  Oimp alpha beta -> conj alpha ++ conj beta

quitaDisy :: PL -> PL
quitaDisy phi = case phi of
  Top -> Top
  Bot -> Bot
  Var n -> Var n
  Oneg alpha -> Oneg $ quitaDisy alpha
  Oand alpha beta -> Oand (quitaDisy alpha) (quitaDisy beta)
  Oor alpha beta -> Oimp (quitaDisy $ Oneg alpha) (beta)
  Oimp alpha beta -> Oimp (quitaDisy alpha) (quitaDisy beta)
