{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module DeduccionLEjemplos
  where

import SintaxisPLI
import DeduccionL (ReglaL(..),esDeduccionEnL)


-- Ejercicios de Miguel

-- Ejercicio B
ejercicio_b :: IO ()
ejercicio_b = -- {v1->(v2->v3), v1->v2} |- v1->v3
  let
    v1 = Var 1
    v2 = Var 2
    v3 = Var 3
    gamma = [v1⇒(v2⇒v3), v1⇒v2]
    (⇒) :: PLI->PLI->PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (v1⇒(v2⇒v3), Prem)),
        (2, (v1⇒v2, Prem)),
        (3, ((v1⇒(v2⇒v3)) ⇒ ((v1⇒v2) ⇒ (v1⇒v3)), Ax)), -- Axioma 2
        (4, ((v1⇒v2) ⇒ (v1⇒v3), ModPon 1 3)),
        (5, (v1⇒v3, ModPon 2 4))
        ]
    phi = v1⇒v3
  in esDeduccionEnL gamma lpasos phi

-- Ejercicio C
ejercicio_c :: IO ()
ejercicio_c = -- {Var 1, Var 1 -> Bot} |- Bot
  let
    v1 = Var 1
    gamma = [v1, oNeg v1]
    lpasos = [
        (1, (v1, Prem)),
        (2, (oNeg v1, Prem)),
        (3, (Bot, ModPon 1 2))
        ]
    phi = Bot
      in esDeduccionEnL gamma lpasos phi

-- Ejercicio D
ejercicio_d :: IO()
ejercicio_d = -- {v1} |- v1
  let
    v = Var 1
    gamma = [v]
    (⇒) :: PLI -> PLI -> PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (v, Prem))
        ]
    phi = v
      in esDeduccionEnL gamma lpasos phi

-- Ejercicio E
ejercicio_e :: IO ()
ejercicio_e = -- {} |- v ⇒ v
  let
    v = Var 1
    gamma = []
    (⇒) :: PLI -> PLI -> PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (v⇒((v⇒v)⇒v), Ax)), -- Axioma 1
        (2, ((v⇒((v⇒v)⇒v))⇒((v⇒(v⇒v))⇒(v⇒v)), Ax)),-- Axioma 2
        (3, ((v⇒(v⇒v))⇒(v⇒v), ModPon 1 2)),
        (4, (v⇒(v⇒v), Ax)), -- Axioma 1
        (5, (v⇒v, ModPon 4 3))
        ]
    phi = v⇒v
      in esDeduccionEnL gamma lpasos phi

-- Ejercicio G
ejercicio_g :: IO()
ejercicio_g = -- {a ⇒ b, b ⇒ g} |- a ⇒ g
  let
    a = Var 1
    b = Var 2
    g = Var 3
    gamma = [a⇒b, b⇒g]
    (⇒) :: PLI -> PLI -> PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, ((b⇒g)⇒(a⇒(b⇒g)), Ax)), -- Axioma 1
        (2, (b⇒g, Prem)), -- Premisa 
        (3, (a⇒(b⇒g), ModPon 2 1)), -- MP  2 1
        (4, ((a⇒(b⇒g)) ⇒ ((a⇒b)⇒(a⇒g)), Ax)), -- Axioma 2
        (5, ((a⇒b)⇒(a⇒g), ModPon 3 4)), -- MP 3 4
        (6, (a⇒b, Prem)),
        (7, (a⇒g, ModPon 6 5))
        ]
    phi = a ⇒ g
      in esDeduccionEnL gamma lpasos phi

-- Ejercicio H
ejercicio_h :: IO()
ejercicio_h = -- {a ⇒ (b ⇒ g)} |- b ⇒ (a ⇒ g)
  let
    a = Var 1
    b = Var 2
    g = Var 3
    gamma = [a ⇒ (b ⇒ g)]
    (⇒) :: PLI -> PLI -> PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (a ⇒ (b ⇒ g), Prem)), -- Premisa
        (2, ((a ⇒ (b ⇒ g)) ⇒ ((a⇒b)⇒(a⇒g)), Ax)), -- Axioma 2 
        (3, ((a⇒b)⇒(a⇒g), ModPon 1 2)), -- MP 1 2
        (4, (b⇒(a⇒b), Ax)), -- Axioma 1
        (5, (((a⇒b)⇒(a⇒g))⇒(b⇒((a⇒b)⇒(a⇒g))), Ax)), -- Axioma 1
        (6, (b⇒((a⇒b)⇒(a⇒g)), ModPon 3 5)),
        (7, ((b⇒((a⇒b)⇒(a⇒g))) ⇒ ((b⇒(a⇒b))⇒(b⇒(a⇒g))), Ax)), -- Axioma 2
        (8, ((b⇒(a⇒b))⇒(b⇒(a⇒g)), ModPon 6 7)),
        (9, (b⇒(a⇒g), ModPon 4 8))
        ]
    phi = b ⇒ (a ⇒ g)
      in esDeduccionEnL gamma lpasos phi

-- Ejercicio J
ejercicio_j :: IO()
ejercicio_j = -- {Bot} |- a
  let
    a = Var 1
    gamma = [Bot]
    (⇒) :: PLI -> PLI -> PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (Bot, Prem)), --
        (2, (Bot ⇒ a, Ax)), -- 
        (3, (a, ModPon 1 2)) --
        ]
    phi = a
      in esDeduccionEnL gamma lpasos phi


{-
ejercicio_ :: IO()
ejercicio_ = -- {} |- phi
  let
    a = Var 1
    b = Var 2
    g = Var 3
    gamma = []
    (⇒) :: PLI -> PLI -> PLI
    f⇒g = Oimp f g
    lpasos = [
        (1, (, )), --
        (2, (, )), -- 
        (3, (, )) --
        ]
    phi = phi
      in esDeduccionEnL gamma lpasos phi
-}
