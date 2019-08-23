{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module SintaxisPL
  where

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PL = Top | Bot 
              | Var Indice | Oneg PL 
              | Oand PL PL | Oor PL PL 
              | Oimp PL PL deriving Eq

-- Hacemos parte de Show al tipo LP
instance Show PL where
  show Top = "T"
  show Bot = "F"
  show (Var x) = "v"++show x
  show (Oneg alpha) = "¬"++(show alpha)
  show (Oand alpha beta) = "("++show alpha++" & "++show beta++")"
  show (Oor alpha beta) = "("++show alpha++" | "++show beta++")"
  show (Oimp alpha beta) = "("++show alpha++" -> "++show beta++")"
