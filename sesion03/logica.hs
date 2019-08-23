{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module EjemplosLogica3
  where

import SintaxisPL


-- Definimos el tipo de valuación
type Valuacion = Indice -> Bool

-- Definimos el tipo Modelo
type Modelo = [Indice]

-- Función que nos da la lista de variables de una formula
varsOf :: PL -> [Indice]
varsOf phi = case phi of
  Top -> []
  Bot -> []
  Var n -> [n]
  Oneg alpha -> varsOf alpha
  Oand alpha beta -> varsOf alpha ++ varsOf beta
  Oor alpha beta -> varsOf alpha ++ varsOf beta
  Oimp alpha beta -> varsOf alpha ++ varsOf beta

-- Función que nos dice si una valuación satisface una formula lógica
satPL :: Valuacion -> PL -> Bool
satPL valor phi = case phi of
 Top -> True
 Bot -> False
 Var alpha -> (valor alpha)
 Oneg alpha -> not(satPL valor alpha)
 Oand alpha beta -> (satPL valor alpha) && (satPL valor beta)
 Oor alpha beta -> (satPL valor alpha) || (satPL valor beta)
 Oimp alpha beta -> not(satPL valor alpha) || (satPL valor beta)


-- Función que nos dice si un modelo satisface una formula lógica
satMod :: Modelo -> PL -> Bool
satMod m phi = case phi of
 Top -> True
 Bot -> False
 Var n -> elem n m
 Oneg alpha -> not(satMod m alpha)
 Oand alpha beta -> (satMod m alpha) && (satMod m beta)
 Oor alpha beta -> (satMod m alpha) || (satMod m beta)
 Oimp alpha beta -> not(satMod m alpha) || (satMod m beta)

 -- Función que nos da el conjunto potencia de un conjunto dado
powerSet :: [t] -> [[t]]
powerSet l  = case l of
  []   -> [[]]
  x:xs -> powerXS ++ [x:w | w <- powerXS] where
    powerXS = powerSet xs 

-- Función que dado un conjunto y una formula nos dice si hay una implicacion logic
impLogicamente :: [PL] -> PL -> Bool
impLogicamente cGamma phi = and [(satMod m alpha) `opImp` (satMod m phi) | 
                                 alpha <- cGamma, 
                                 m <- powerSet $ varsOf alpha ] where
  opImp :: Bool -> Bool -> Bool
  opImp g h = not g || h

-- Función que nos dice si dos formulas son equivalentes
logEquivalentes :: PL -> PL -> Bool
logEquivalentes phi psi = (impLogicamente [phi] psi) && (impLogicamente [psi] phi)
