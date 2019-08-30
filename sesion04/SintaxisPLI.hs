{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module SintaxisPLI
  where

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PLI = Bot | Var Indice | Oimp PLI PLI 
        deriving (Eq,Show,Ord,Read)
