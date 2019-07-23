{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}
module Ejemplos1
  where

-- Función que regresa la potencia del número n a la m

pote :: Int -> Int -> Int
pote n m = case m of
  0 -> 1
  p -> n * (pote n (m-1))

-- Función que regresa el factorial de un número

fact :: Int -> Int
fact n = case n of
  0 -> 1
  m -> n * fact (n-1)

-- Función que regresa el número de elementos de una lista

tam :: [a] -> Int
tam l = case l of
  [] -> 0
  (l:ls) -> tam ls + 1

-- Función que regresa el n elementos de una lista

primN :: [a] -> Int -> [a]
primN (l:ls) n = case n of
  0 -> []
  m -> [l] ++ primN ls (n-1)

-- Función que regresa los elementos que son mayores a un número dado

mayores :: Ord a => [a] -> a -> [a]
mayores l n = [m | m <- l, m > n]
