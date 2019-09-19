{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module DeduccionLEjemplos
  where

import SintaxisPLI
import DeduccionL (ReglaL(..),esDeduccionEnL)


-- Introduction to mathematical logic, Mendelson.

lema_1_8 :: IO ()
lema_1_8 = -- {} |- v ⇒ v
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


ejercicio_1_47_b :: IO()
ejercicio_1_47_b = -- {a ⇒ b, b ⇒ g} |- a ⇒ g
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


ejercicio_1_47_c :: IO()
ejercicio_1_47_c = -- {} |- phi
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


{-
nombre :: IO()
nombre = -- {} |- phi
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
