{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module EjemplosLogica1
  where

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PL = Top | Bot 
              | Var Indice | Oneg PL 
              | Oand PL PL | Oor PL PL 
              | Oimp PL PL deriving (Eq, Show)

-- Función que nos da el número de operadores en una formula
numOp :: PL -> Int
numOp phi = case phi of
     Top -> 0
     Bot -> 0
     Var p -> 0
     Oneg p -> numOp p + 1
     Oand p q -> numOp p + numOp q + 1
     Oor p q -> numOp p + numOp q + 1
     Oimp p q -> numOp p + numOp q + 1

-- Función que elimina las implicaciones de una formula
quitaImp :: PL -> PL
quitaImp phi = case phi of
     Top -> Top
     Bot -> Bot
     Var p -> Var p
     Oneg p -> Oneg $ quitaImp p
     Oand p q -> Oand (quitaImp p) (quitaImp q)
     Oor p q -> Oor (quitaImp p) (quitaImp q)
     Oimp p q -> Oor (Oneg $ quitaImp p) (quitaImp q)

-- Función que cuenta los operadores binarios en una formula
numObin :: PL -> Int
numObin phi = case phi of
     Top -> 0
     Bot -> 0
     Var p -> 0
     Oneg p -> numObin p
     Oand p q -> numObin p + numObin q + 1
     Oor p q -> numObin p + numObin q + 1
     Oimp p q -> numObin p + numObin q + 1
