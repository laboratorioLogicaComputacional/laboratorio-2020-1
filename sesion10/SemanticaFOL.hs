module SemanticaFOL(VarInterp,Estructura,Dominio,Relacion,Funcion,Constante, interpTerm,interpTermL,interpVxTOb,checkEstruc,domTOn,isTupleFORsimINdom,aridadOf, satMiVphi)
--Semantica de la logica de predicados de primer orden (FOL)
--mcb
where
import SintaxisFOL (Var,SimAridad,SRel,SFun,SCon, Alfabeto, Term(..), FOL(..), aridadOf) 
--import Data.List as L (union, (\\), nub)
--
-------------------------------------------------------------------------------
--
-- Tipos de datos para la semantica de la FOL: -----------------------------------
--
type VarInterp d    = Var -> d          -- Interpretacion de variables (Valuaciones)
type Dominio d      = [d]               -- Dominio de una estructura, [d]=una lista (conjunto)
type Relacion d     = (Dominio d)->Bool -- Relaciones sobre el Dominio d=[d]=tuplas no acotadas
type Funcion d      = (Dominio d)->d    -- Funciones sobre el Dominio d=[d]=tuplas no acotadas
type Constante d    = d                 -- Constantes en el dominio d
type Estructura d   = (Dominio d, [(SRel,Relacion d)], [(SFun,Funcion d)], [(SCon,Constante d)])
                    -- d                    : dominio de la estructura
                    -- [(SRel,Relacion d)]  : Una lista de pares (simboloDeRelacion, Relacion)
                    -- [(SFun,Funcion d)]   : Una lista de pares (simboloDeFuncion, Funcion)
                    -- [(SCon,Constante d)] : Una lista de pares (simboloDeConstante, Constante)
--
-------------------------------------------------------------------------------
--
-- Interpretacion de Terminos de la FOL: --------------------------------------
-- 
-- tupleINdom :: (Eq d)=> [d]->Dominio d -> Bool
-- -- True si todos los elementos de la tupl (lista) ld son elementos del dominio (lista) dM.
-- tupleINdom ld dM = and [x `elem` dM | x <- ld]
--
isTupleFORsimINdom :: (Eq d)=> [d]->SimAridad->Dominio d -> Bool
-- True si ld es una tupla(lista) correcta para el simbolo sim en el dominio (lista) dM.
-- Es decir, True si length(ld)=aridadOf(sim) y forall x: x in ld x in dM.
isTupleFORsimINdom ld sim dM = (length ld== aridadOf sim) && (and [x `elem` dM | x <- ld])
--
interpTerm :: (VarInterp d)->(Estructura d)->Term -> d
-- Interpretacion de un termino t mediante una interpretacion de variables interpV y una estructura m.
interpTerm interpV m t = 
    case t of
        Tvar v          -> interpV v        -- Interpretacion de la variable v
        Tfun (f,fa) lt  -> if fa==ltN       -- Si la aridad del simbolo f coincide con el numero de terminos en lt:
                                then fM ltM -- Aplicar fM a la interpretacion de los terminos de lt
                                else        -- si no, aridad(f) != length(lt):
                                    error $ "interpTerm: aridad(f) != length(lt), (fa,ltN)= "
                                    ++ show (fa,ltN)
                            where
                            ltN     = length lt                 -- Numero de terminos en lt (argumentos de fM)
                            fM      = interpF (f,fa) m          -- Interpretacion de (f,fa)
                            ltM     = interpTermL interpV m lt  -- Interpretacion de los terminos de lt
        Tcon c          -> interpC c m
--
interpTermL :: (VarInterp d)->(Estructura d)->[Term] -> [d]
-- Interpretacion de una lista de terminos lt mediante una interpretacion de variables interpV y una estructura m.
interpTermL interpV m lt = map (interpTerm interpV m) lt
--
interpC :: SCon->(Estructura d) -> d
-- Interpretacion de un simbolo de constante sC mediante una estructura.
interpC sC (_,_,_,scmL) = 
    case mscM of
        Just cM -> cM
        Nothing -> error $ "interpC: el simbolo de funcion sC no tiene interpretación en m, (sC,scmL)= "
                   ++show (sC, map fst scmL)
    where
    mscM = lookup sC scmL
--
interpF :: SFun->(Estructura d) -> (Funcion d)
-- Interpretacion de un simbolo de funcion sF mediante una estructura.
interpF sF (_,_,sfmL,_) = 
    case (lookup sF sfmL) of -- Busca el simbolo de funcion sF en las funciones de la estructura.
        Just fM -> fM
        Nothing -> error $ "interpF: el simbolo de funcion sF no tiene interpretación en m, (sF,sfmL)= "
                   ++show (sF, map fst sfmL)
--
--
-- Semantica de la FOL: -------------------------------------------------------
--
interpR :: SRel->(Estructura d) -> (Relacion d)
-- Interpretacion de un simbolo de relacion sR mediante una estructura.
interpR sR (_,srmL,_,_) = 
    case (lookup sR srmL) of -- Busca el simbolo de relacion sR en las relaciones de la estructura.
        Just rM -> rM
        Nothing -> error $ "interpR: el simbolo de relacion sR no tiene interpretación en m, (sR,srmL)= "
                   ++show (sR, map fst srmL)
--
satMiVpred :: (Estructura d)->(VarInterp d)->FOL -> Bool
-- True si m,iV satisface al predicado (Pred (r,ra) lt), es decir m,iV |= (Pred (r,ra) lt).
satMiVpred m iV phi =
    case phi of
        Pred (r,ra) lt  -> if ra==ltN       -- Si la aridad del simbolo r coincide con el numero de terminos en lt:
                                then rM ltM -- Aplicar rM a la interpretacion de los terminos de lt
                                else        -- si no, aridad(r) != length(lt):
                                    error $ "satMiVphi: aridad(r) != length(lt), (ra,ltN)= "
                                    ++ show (ra,ltN)
                            where
                            ltN = length lt             -- Numero de terminos en lt (argumentos de rM)
                            rM  = interpR (r,ra) m      -- Interpretacion de (r,ra)
                            ltM = interpTermL iV m lt   -- Interpretacion de los terminos de lt
        _               -> error $ "satMiVpred: phi debe ser un predicado, phi="++show phi
    
--
interpVxTOb :: (VarInterp d)->Var->d -> (VarInterp d)
-- Regresa la interpretacion de variables que resulta de modificar iV asignando b a la variable x, iV[x->b]
interpVxTOb iV x b = iVxTOb
    where
    iVxTOb v = if v /= x
                  then iV v
                  else b
--
satMiVphi :: (Estructura d)->(VarInterp d)->FOL -> Bool
-- True si m,iV satisface a phi, es decir m,iV |= phi.
satMiVphi m@(dM,_,_,_) iV phi =
    case phi of
        Bot         -> True
        Top         -> False
        Pred _ _    -> satMiVpred m iV phi
        --
        Oimp f g    -> not(satMiVphi m iV f) || (satMiVphi m iV g)
        Oand f g    -> (satMiVphi m iV f) && (satMiVphi m iV g)
        Oor  f g    -> (satMiVphi m iV f) || (satMiVphi m iV g)
        Oneg f      -> not(satMiVphi m iV f)
        --
        All x f     -> and [satMiVphi m (interpVxTOb iV x b) f | b <- dM]
        Exi x f     -> or  [satMiVphi m (interpVxTOb iV x b) f | b <- dM]
--         --_               -> error $ "satMiVphi: no definida en este caso, phi="++show phi
--
-- Huth-Ryan p. 
-- Definition 2.20 Let Γ be a (possibly infinite) set of formulas in predicate
-- logic and ψ a formula of predicate logic.
--         1. Semantic entailment Γ |= ψ holds iff for all models M and look-up tables l,
--         whenever M |= l φ holds for all φ ∈ Γ, then M |= l ψ holds as well.
--         2. Formula ψ is satisfiable iff there is some model M and some environment l such
--         that M |= l ψ holds.
--         3. Formula ψ is valid iff M |= l ψ holds for all models M and environments l in
--         which we can check ψ.
--         4. The set Γ is consistent or satisfiable iff there is a model M and a look-up table
--         l such that M |= l φ holds for all φ ∈ Γ.
-- In predicate logic, the symbol |= is overloaded: 
-- it denotes model checks ‘M |= φ’ and semantic entailment ‘φ_1 , φ_2 , . . . , φ_n |= ψ.’ 
-- Computationally, each of these notions means trouble. 
-- First, establishing M |= φ will cause problems,
-- if done on a machine, as soon as the universe of values A of M is infinite.
-- In that case, checking the sentence ∀x ψ, where x is free in ψ, amounts to
-- verifying M |= [x → a] ψ for infinitely many elements a.
-- Second, and much more seriously, in trying to verify that φ_1 , φ_2 , . . . , φ_n |= ψ holds, 
-- we have to check things out for all possible models, all models which
-- are equipped with the right structure (i.e. they have functions and predicates
-- with the matching number of arguments). This task is impossible to perform mechanically.
--
--
{-
Responder Si o No, y hacer la deducción cuando la respuesta es Si.
Ejercicio posterior: 
cuando la respuesta es No, construir una estructura M y una valuación \sigma tales que 
M,\sigma |= \Gamma  y  $M,\sigma \not\models \varphi$.
Como ayuda, pueden pensar que: P(v1) significa "v1 es un Pegaso" y Q(v1) significa "v1 es una Quimera".
Por ejemplo: 
¿Si existe una cosa, v1, tal que (v1 es un Pegaso o v1 es una Quimera), entonces (existe un Pegaso o existe una Quimera)?
¿Si todas las cosas son Pegasos o son Quimeras, entonces (Todas las cosas son Pegasos, o Todas las cosas son Quimeras)?

1) ¿{∃v1. (P(v1) or Q(v1))} |- (∃v1. P(v1)) or (∃v1. Q(v1))?
2) ¿{(∃v1. P(v1))} |- ∃v1. (P(v1) or Q(v1))?
3) ¿{∃v1. (P(v1) or Q(v1))} |- (∃v1. P(v1))?
4) ¿{∀v1. (P(v1) & Q(v1))} |- (∀v1. P(v1)) & (∀v1. Q(v1))?
5) ¿{(∀v1. P(v1))} |- ∀v1. (P(v1) & Q(v1))?
6) ¿{∀v1. (P(v1) & Q(v1))} |- (∀v1. P(v1))?

7) ¿{∃v1. (P(v1) & Q(v1))} |- (∃v1. P(v1)) & (∃v1. Q(v1))?
8) ¿{(∃v1. P(v1))} |- ∃v1. (P(v1) & Q(v1))?
9) ¿{∃v1. (P(v1) & Q(v1))} |- (∃v1. P(v1))?
10) ¿{∀v1. (P(v1) or Q(v1))} |- (∀v1. P(v1)) or (∀v1. Q(v1))?
11) ¿{(∀v1. P(v1))} |- ∀v1. (P(v1) or Q(v1))?
12) ¿{∀v1. (P(v1) or Q(v1))} |- (∀v1. P(v1))?

13) ¿{∃v1. (P(v1) -> Q(v1))} |- (∃v1. P(v1)) -> (∃v1. Q(v1))?
14) ¿{(∃v1. P(v1))} |- ∃v1. (P(v1) -> Q(v1))?
15) ¿{∃v1. (P(v1) -> Q(v1))} |- (∃v1. P(v1))?
16) ¿{∀v1. (P(v1) -> Q(v1))} |- (∀v1. P(v1)) -> (∀v1. Q(v1))?
17) ¿{(∀v1. P(v1))} |- ∀v1. (P(v1) -> Q(v1))?
18) ¿{∀v1. (P(v1) -> Q(v1))} |- (∀v1. P(v1))?
-}

--
checkEstruc :: (Show d) => (Estructura d)->Alfabeto-> Bool
-- True si m es una sigma-estructura para FOL, es decir m es una estructura definida mediante el alfabeto sigma.
checkEstruc _ _ = error $ "checkEstruc: NO implementada"
--                         ++ show (m,sigma) -- XXXX
--
--
domTOn :: [d] -> Int -> [[d]]
domTOn dL n 
    | n == 0    = [[]]
    | n >= 1    = [x: tNminus1 | x <- dL, tNminus1 <- domTOnMinus1]
    | otherwise = error $ "domTOn: n debe ser >=0, n= "++ show n
    where
    domTOnMinus1= domTOn dL (n-1)
--

--
