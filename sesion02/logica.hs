{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module EjemplosLogica2
  where

import SintaxisPL

-- Función que nos da el número de variables en una fórmula
numVar :: PL -> Int
numVar phi = case phi of
  Top -> 0
  Bot -> 0
  Var _ -> 1
  Oneg alpha -> numVar alpha
  Oand alpha beta -> numVar alpha + numVar beta
  Oor alpha beta -> numVar alpha + numVar beta
  Oimp alpha beta -> numVar alpha + numVar beta

-- Función que nos indica si hay conjunciones en una formula
hayConjunciones :: PL -> Bool
hayConjunciones phi = case phi of
  Top -> False
  Bot -> False
  Var _ -> False
  Oneg alpha -> hayConjunciones alpha
  Oand alpha beta -> True || hayConjunciones alpha || hayConjunciones beta
  Oor alpha beta ->  hayConjunciones alpha || hayConjunciones beta
  Oimp alpha beta -> hayConjunciones alpha || hayConjunciones beta
  
-- Función que nos da las conjunciones de una formula
conj :: PL -> [PL]
conj phi = case phi of
  Top -> []
  Bot -> []
  Var _ -> []
  Oneg alpha -> conj alpha
  Oand alpha beta -> [Oand alpha beta] ++ conj alpha ++ conj beta
  Oor alpha beta -> conj alpha ++ conj beta
  Oimp alpha beta -> conj alpha ++ conj beta

-- Función que nos da el numero de disyunciones en una formula
numDis :: PL -> Int
numDis phi = case phi of
  Top -> 0
  Bot -> 0
  Var _ -> 0
  Oneg alpha -> numDis alpha
  Oand alpha beta -> numDis alpha + numDis beta 
  Oor alpha beta -> numDis alpha + numDis beta + 1
  Oimp alpha beta -> numDis alpha + numDis beta  

-- Función que elimina las conjunciones de una formula
quitaConj :: PL -> PL
quitaConj phi = case phi of
  Top -> Top
  Bot -> Bot
  Var x -> Var x
  Oneg alpha -> Oneg (quitaConj alpha)
  Oand alpha beta -> Oneg (Oor (Oneg (quitaConj alpha)) (Oneg (quitaConj beta)))
  Oor alpha beta -> Oor (quitaConj alpha) (quitaConj beta)
  Oimp alpha beta -> Oimp (quitaConj alpha) (quitaConj beta)

-- Función que nos indica si una formula esta en forma normal de negación.
{-
isInNFF :: PL -> Bool
isInNFF phi = case phi of
 Top-> True
 Bot-> True
 Var v -> True
 Oneg alpha -> case alpha of
  Var x -> True
  _ -> False 
 Oor alpha beta -> isInNFF alpha && isInNFF beta
 Oand alpha beta -> isInNFF alpha && isInNFF beta
 Oimp _ _ -> False
-}
