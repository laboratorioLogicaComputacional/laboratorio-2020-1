{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module DeduccionLEjemplos
  where

import SintaxisPLI
import DeduccionL (ReglaL(..),esDeduccionEnL,NumTeo,NumCor)


-- Ejercicios de Miguel
--
(⇒) :: PLI->PLI->PLI
-- Abreviatura de Oimp f g
f⇒g = Oimp f g

-------------------------------------------------------------------------------
--
-- Ejemplos de pruebas que usan una lista (global) de teoremas: ---------------
--
teoremasL :: [NumTeo]
-- Una lista global de teoremas numerados. (Se usa en el ejercicioT1).
-- Formato de cada teorema numerado:
--   (n,            -- Numero de teorema. Cada numero debe ser distinto
--      (phi,       -- Teorema (formula)
--       lPasos ))  -- Lista de pasos de una prueba (sin premisas) de phi en L. {} |- phi
teoremasL = 
    let v1= Var 1
    in
    [(1, -- {} |- v1 ⇒ v1
        (v1⇒v1, 
            [(1, (v1⇒((v1⇒v1)⇒v1), Ax)), -- Axioma 1
            (2, ((v1⇒((v1⇒v1)⇒v1))⇒((v1⇒(v1⇒v1))⇒(v1⇒v1)), Ax)),-- Axioma 2
            (3, ((v1⇒(v1⇒v1))⇒(v1⇒v1), ModPon 1 2)),
            (4, (v1⇒(v1⇒v1), Ax)), -- Axioma 1
            (5, (v1⇒v1, ModPon 4 3))
            ] )),
     (2,
     (((v1⇒Bot)⇒v1)⇒v1,
        [(1, ((v1⇒Bot)⇒(v1⇒Bot), Teo 1)),
        (2, (((v1⇒Bot)⇒(v1⇒Bot))⇒(((v1⇒Bot)⇒v1)⇒v1), Ax)),
        (3, (((v1⇒Bot)⇒v1)⇒v1, ModPon 1 2))
        ]))
    ]

corolariosL :: [NumCor]
corolariosL =
    let v5 = Var 5
        v6 = Var 6
        v7 = Var 7
    in
    [(1,
    (v5 ⇒ v7,[v5⇒v6, v6⇒v7],
     [(1, ((v6⇒v7)⇒(v5⇒(v6⇒v7)), Ax)), -- Axioma 1
      (2, (v6⇒v7, Prem)), -- Premisa 
      (3, (v5⇒(v6⇒v7), ModPon 2 1)), -- MP  2 1
      (4, ((v5⇒(v6⇒v7)) ⇒ ((v5⇒v6)⇒(v5⇒v7)), Ax)), -- Axioma 2
      (5, ((v5⇒v6)⇒(v5⇒v7), ModPon 3 4)), -- MP 3 4
      (6, (v5⇒v6, Prem)),
      (7, (v5⇒v7, ModPon 6 5))
     ]))
    ]
--
ejercicioT1 :: IO()
-- Deduccion en L de (v2->v2) usando que |-(v1->v1)
ejercicioT1 = -- {} |- v2 -> v2
  let 
    v2      = Var 2
    gamma   = []
    lpasos  = [
        (1, (v2⇒v2, Teo 1)) -- v2⇒v2 ... Instancia del Teorema 1 de teoremasL1
        ]
    phi = v2 ⇒ v2
    in esDeduccionEnL teoremasL corolariosL gamma lpasos phi
--
ejercicioT2 :: IO()
-- Deduccion en L de ((v3->Bot)->(v3->Bot)) usando que |-(v1->v1)
ejercicioT2 = -- {} |- ((v3->Bot)->(v3->Bot))
  let 
    v3      = Var 3
    gamma   = []
    lpasos  = [
        (1, ((v3⇒Bot)⇒(v3⇒Bot), Teo 1)) -- v2⇒v2 ... Instancia del Teorema 1 de teoremasL1
        ]
    phi = (v3⇒Bot)⇒(v3⇒Bot)
    in esDeduccionEnL teoremasL corolariosL gamma lpasos phi

ejercicioT3 :: IO()
-- Deducción en L de ((v4 -> Bot) -> v4) -> v4 usando |- (v1 -> v1)
ejercicioT3 = -- {} |- ((v4 -> Bot) -> v4) -> v4
  let
    v4      = Var 4
    gamma   = []
    lpasos  = [
        (1, ((v4⇒Bot)⇒(v4⇒Bot), Teo 1)),
        (2, (((v4⇒Bot)⇒(v4⇒Bot))⇒(((v4⇒Bot)⇒v4)⇒v4), Ax)),
        (3, (((v4⇒Bot)⇒v4)⇒v4, ModPon 1 2))
        ]
    phi     = (((v4⇒Bot)⇒v4)⇒v4)
    in esDeduccionEnL teoremasL corolariosL gamma lpasos phi

ejercicioT4 :: IO()
ejercicioT4 = -- {a ⇒ b, b ⇒ g} |- a ⇒ g
  let
    v5 = Var 5
    v6 = Var 6
    v7 = Var 7
    gamma = [v5⇒v6, v6⇒v7]
    lpasos = [
        (1, ((v6⇒v7)⇒(v5⇒(v6⇒v7)), Ax)), -- Axioma 1
        (2, (v6⇒v7, Prem)), -- Premisa 
        (3, (v5⇒(v6⇒v7), ModPon 2 1)), -- MP  2 1
        (4, ((v5⇒(v6⇒v7)) ⇒ ((v5⇒v6)⇒(v5⇒v7)), Ax)), -- Axioma 2
        (5, ((v5⇒v6)⇒(v5⇒v7), ModPon 3 4)), -- MP 3 4
        (6, (v5⇒v6, Prem)),
        (7, (v5⇒v7, ModPon 6 5))
        ]
    phi = v5 ⇒ v7
      in esDeduccionEnL teoremasL corolariosL gamma lpasos phi

ejercicioT5 =
  let
    v8 = Var 8
    v9 = Var 9
    v10 = Var 10
    gamma = [v8 ⇒ (v9 ⇒ v10)]
    lpasos = [
        (1, (v8 ⇒ (v9 ⇒ v10), Prem)),
        (2, ((v8 ⇒ (v9 ⇒ v10)) ⇒ ((v8⇒v9)⇒(v8⇒v10)), Ax)) , -- Axioma 2
        (3, (v9⇒(v8⇒v9), Ax)), -- Axioma 1
        (4, ((v8⇒v9)⇒(v8⇒v10), ModPon 1 2)),
        (5, (v9 ⇒ (v8 ⇒ v10), Cor 1 3 4))
        ]
    phi = v9 ⇒ (v8 ⇒ v10)
      in esDeduccionEnL teoremasL corolariosL gamma lpasos phi
--
todosLosEjemplos :: IO ()
todosLosEjemplos =
    do
    ejercicioT1
    putStrLn "---------------------------------------"
    ejercicioT2
    putStrLn "---------------------------------------"
--
{-
ejercicio_ :: IO()
ejercicio_ = -- {} |- phi
  let
    a = Var _
    gamma = []
    lpasos = [
        (1, (, )), --
        (2, (, )), -- 
        (3, (, )) --
        ]
    phi = phi
      in esDeduccionEnL [] gamma lpasos phi
-}
