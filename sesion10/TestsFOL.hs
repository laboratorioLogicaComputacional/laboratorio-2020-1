module TestsFOL
--Pruebas para la logica de predicados de primer orden
--mcb
where
--
import SintaxisFOL
import SemanticaFOL
--
--------------------------------------------------------
--
-- Ejemplos de formulas sobre alfabetos diversos: ---------------------------------------
f1 :: FOL
-- P(x,y)
f1 = Pred ("P",2) [Tvar "x", Tvar "y"]
-- satMiVphi m0 interpV0 f1
-- satMiVphi m0 interpV1 f1

f2 :: FOL
-- Q(a,h(w))
f2 = Pred ("Q",2) [Tvar "a", (Tfun ("h",1) [Tvar "w"])]
-- satMiVphi m0 interpV0 f2
-- satMiVphi m0 interpV1 f2

f3 :: FOL
-- ∀x.Q(x,g(y))
f3 = All "x" $ Pred ("Q",2) [Tvar "x", Tfun ("g",1) [Tvar "y"]]

f4 :: FOL
-- ∀x.∃y.P(x,y)
f4 = All "x" $ Exi "y" $ Pred ("P",2) [Tvar "x", Tvar"y"]

f1S ::String
f1S= showFOL f1

f5 :: FOL 
--(∀x. (P (x) ∧ Q(x))) → (¬P (x) ∨ Q(y))  -- Huth-Ryan p. 104
f5= (All "x" (Pred ("P",1) [Tvar "x"] `Oand` Pred ("Q",1) [Tvar "x"])) `Oimp` 
    (Oneg $ Pred ("P",1) [Tvar "x"] `Oor` Pred ("Q",1) [Tvar "y"])

f5S ::String
f5S= showFOL f5

freeInf5 :: [Var]
freeInf5= freeInFOL f5

boundInf5 :: [Var]
boundInf5= boundInFOL f5

-- Tests:
-- > :l TestsFOL_2019m11d03.hs 
-- *TestsFOL_2019m11d03> showFOL f5
-- "((ForAll x. (P(x) & Q(x))) -> ~(P(x) | Q(y)))"
-- *TestsFOL_2019m11d03> 
-- *TestsFOL_2019m11d03> freeInFOL f5
-- ["x","y"]
-- *TestsFOL_2019m11d03> boundInFOL f5
-- ["x"]
-- *TestsFOL_2019m11d03> 
--

f6 :: FOL 
-- (∀x. Q(y))
f6= (All "x" (Pred ("Q",1) [Tvar "y"]))
f6S ::String
f6S= showFOL f6

freeInf6 :: [Var]
freeInf6= freeInFOL f6

boundInf6 :: [Var]
boundInf6= boundInFOL f6

-- Tests:
-- > :l TestsFOL_2019m11d03.hs 
-- *TestsFOL_2019m11d03> showFOL f6
-- "(ForAll x. Q(y))"
-- *TestsFOL_2019m11d03> freeInFOL f6
-- ["y"]
-- *TestsFOL_2019m11d03> boundInFOL f6
-- []  -- OK "x" NO ocurre ligada en f6
-- *TestsFOL_2019m11d03> 
-------------------------------------------------------------------------------
--
-- Pruebas de la semantica de FOL: --------------------------------------------
--
sigma0 :: Alfabeto
-- Un alfabeto
sigma0 = -- Alfabeto visto en clase
            ([("H",1),("M",1),("A",2)], -- simbolos de predicado. esHombre, esMujer, amigoDe
             [("f",1),("g",2),("h",1)] ,        -- simbolos de funcion
             [] )                       -- simbolos de constante
--
-- Estructura m0 para el alfabeto sigma0
type D0 = Int -- Para definir el dominio de la estructura m0
m0 :: Estructura D0
m0 = (dM0, rL0, fL0, cL0)
    where
    dM0 :: Dominio D0
    dM0 = [1..10]                       -- Dominio de m0= {1,2,...,10}
    rL0 = [ (hS,hM0),(mS,mM),(aS,aM0)   -- Relaciones de m0
            ,(pS,pM0),(qS,qM0)]   
    fL0 = [(fS,fM0),(gS,gM0),(hfS,hfM0)] -- Funciones de m0
    cL0 = []                            -- Constantes de m0
    --
    hS :: SRel
    hS = ("H",1) -- Simbolo de relacion
    --
    hM0 :: Relacion D0
    hM0 ld 
        | isTupleFORsimINdom ld hS dM0  = case ld of
                                            [x] -> x <= 5
                                            _   -> error $ "hM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "hM0: aridad(hS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    mS :: SRel
    mS = ("M",1)
    --
    mM :: Relacion D0
    mM ld 
        | isTupleFORsimINdom ld mS dM0  = case ld of
                                            [x] -> 5 < x
                                            _   -> error $ "mM: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "mM: aridad(mS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    aS :: SRel
    aS = ("A",2)
    --
    aM0 :: Relacion D0
    aM0 ld 
        | isTupleFORsimINdom ld aS dM0  = case ld of
                                            [x,y]   -> x <= 5 && 5 < y
                                            _       -> error $ "aM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "aM0: aridad(aS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    --
    pS :: SRel
    pS = ("P",2)
    --
    pM0 :: Relacion D0
    pM0 ld 
        | isTupleFORsimINdom ld pS dM0  = case ld of
                                            [x,y]   -> x <= 5 && 5 < y
                                            _       -> error $ "pM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "pM0: aridad(pS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    qS :: SRel
    qS = ("Q",2)
    --
    qM0 :: Relacion D0
    qM0 ld 
        | isTupleFORsimINdom ld qS dM0  = case ld of
                                            [x,y]   -> x <= 5 && 5 < y
                                            _       -> error $ "qM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "qM0: aridad(qS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    fS :: SFun
    fS = ("f",1)
    --
    fM0 :: Funcion D0
    fM0 ld 
        | isTupleFORsimINdom ld fS dM0  = case ld of
                                            [x] -> x
                                            _   -> error $ "fM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "fM0: aridad(fS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    gS :: SFun
    gS = ("g",2)
    --
    gM0 :: Funcion D0
    gM0 ld 
        | isTupleFORsimINdom ld gS dM0  = case ld of
                                            [_,y]   -> y
                                            _       -> error $ "gM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "gM0: aridad(gS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
    hfS :: SFun
    hfS = ("h",1)
    --
    hfM0 :: Funcion D0
    hfM0 ld 
        | isTupleFORsimINdom ld hfS dM0 = case ld of
                                            [x] -> x
                                            _   -> error $ "hfM0: no definida en esta ld= "++ show ld
        | otherwise                     = error $ "hfM0: aridad(hfS)!=|ld| o ld notSubset dM0"++ show (length ld)
    --
--
--
interpV0 :: VarInterp D0
-- Una interpretacion de variables sobre D0 (ver arriba)
interpV0 x = length x
--
interpV1 :: VarInterp D0
-- Otra interpretacion de variables sobre D0 (ver arriba)
interpV1 x = case x of
                "x" -> 1
                "y" -> 2
                "u" -> 3
                "v" -> 4
                "w" -> 5
                "z" -> 6
                "a" -> 7
                _   -> 10
--
f7 :: FOL
-- ∀x.A(x,f(y))
f7 = All "x" $ Pred ("A",2) [Tvar "x", Tfun ("f",1) [Tvar "y"]]

f8 :: FOL
-- ∀x.∃y.P(x,y)
f8 = All "x" $ Exi "y" $ Pred ("A",2) [Tvar "x", Tvar"y"]

f9 :: FOL
-- ∀x.M(x) -> ~∃x.~M(x)
f9 = (All "x" $ Pred ("M",1) [Tvar "x"]) `Oimp` (Oneg (Exi "x" (Oneg $ Pred ("M",1) [Tvar "x"])))

f10 :: FOL
-- ∃x.M(x)
f10 = (Exi "x" $ Pred ("M",1) [Tvar "x"])

f11 :: FOL
-- ∀x.(M(x) or H(x))
f11 = All "x" ((Pred ("M",1) [Tvar "x"] `Oor` Pred ("H",1) [Tvar "x"]))


--
sat7 :: Bool
sat7 = satMiVphi m0 interpV0 f7
--
sat8 :: Bool
sat8 = satMiVphi m0 interpV0 f8
--
sat9 :: Bool
sat9 = satMiVphi m0 interpV0 f9
--
sat10 :: Bool
sat10 = satMiVphi m0 interpV0 f10
--
sat11 :: Bool
sat11 = satMiVphi m0 interpV0 f11
--
--
