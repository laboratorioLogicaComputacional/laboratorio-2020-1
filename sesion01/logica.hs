{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module EjemplosLogica1
  where

import SintaxisPL

-- Función que nos da el número de operadores en una formula
numOp :: PL -> Int
numOp phi = case phi of
  Top -> 0
  Bot -> 0
  Var v -> 0
  Oneg alpha -> numOp alpha + 1
  Oand alpha beta -> numOp alpha + numOp beta + 1
  Oor alpha beta -> numOp alpha + numOp beta + 1
  Oimp alpha beta -> numOp alpha + numOp beta + 1

-- Función que elimina las implicaciones de una formula
quitaImp :: PL -> PL
quitaImp phi = case phi of
  Top -> Top
  Bot -> Bot
  Var v -> Var v
  Oneg alpha -> Oneg $ quitaImp alpha
  Oand alpha beta -> Oand (quitaImp alpha) (quitaImp beta)
  Oor alpha beta -> Oor (quitaImp alpha) (quitaImp beta)
  Oimp alpha beta -> Oor (Oneg $ quitaImp alpha) (quitaImp beta)

-- Función que cuenta los operadores binarios en una formula
numObin :: PL -> Int
numObin phi = case phi of
  Top -> 0
  Bot -> 0
  Var v -> 0
  Oneg alpha -> numObin alpha
  Oand alpha beta -> numObin alpha + numObin beta + 1
  Oor alpha beta -> numObin alpha + numObin beta + 1
  Oimp alpha beta -> numObin alpha + numObin beta + 1

-- Precondicion: no debe tener implicaciones
noImp2NNF :: PL -> PL
noImp2NNF phi = case phi of
  -- Casos base:
  Top -> phi
  Bot -> phi
  Var v -> Var v
  -- Casos recursivos:
  Oneg alpha -> case alpha of
    -- Casos bases (alpha)
    Top -> Bot
    Bot -> Top
    Var v -> Oneg (Var v)
    -- Casos recursivos (alpha)
    Oneg beta -> noImp2NNF beta
    Oand beta gamma -> noImp2NNF (Oor (Oneg beta) (Oneg gamma))
    Oor beta gamma -> noImp2NNF (Oand (Oneg beta) (Oneg gamma))

  Oand alpha beta -> Oand (noImp2NNF alpha) (noImp2NNF beta)
  Oor alpha beta -> Oor (noImp2NNF alpha) (noImp2NNF beta)

-- Función que transforma una formula a su forma normal de negación.
-- Precondición: ninguna.
toNNF :: PL -> PL
toNNF = noImp2NNF . quitaImp -- Composicion de funciones.
