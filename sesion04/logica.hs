{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

module EjemplosLogica4
  where

import SintaxisPLI

--Ejercicio. Definir una funcion recursivia que despliegue formulas de la PLI, 
showPLI :: PLI -> String
-- Muestra una formula de la PLI
showPLI phi = case phi of
    Bot                                     -> "FF" 
    Var v                                   -> "v"++show v
    Oimp Bot Bot                            -> "TT" -- toLuk(Top)= ~Bot
    (p `Oimp` (q `Oimp` Bot)) `Oimp` Bot    -> "("++ (showPLI p) ++" & "++ (showPLI q) ++")" -- toLuk(f ^ g) = toLuk(¬(f -> ¬g))
--     (p `Oimp` Bot) `Oimp` q                 -> "("++ (showPLI p) ++" | "++ (showPLI q) ++")" -- toLuk(f v g) = toLuk((¬f) -> g)
    Oimp p Bot                              -> "~("++ (showPLI p) ++")" -- toLuk(¬f) = ~toLuk(f)
    Oimp p q                                -> "("++ (showPLI p) ++" -> "++ (showPLI q) ++")" 
    --_         -> error $ "showPLI: no definida en este caso, phi="++show phi
