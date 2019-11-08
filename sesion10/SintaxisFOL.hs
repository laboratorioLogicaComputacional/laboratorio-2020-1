module SintaxisFOL (Var,Aridad, FOL(..), Term(..), SimAridad, SRel,SFun,SCon, Alfabeto, aridadOf, showFOL, showTerm, freeInFOL, boundInFOL, checkFormula)
--Sintaxis de la logica de predicados de primer orden
--mcb
where
import Data.List as L (union, (\\), nub)
--
--------------------------------------------------------
--
type Var        = String        -- Variables
type Simbolo    = String        -- Simbolos
type Aridad     = Int           -- Aridad >= 0
type SimAridad  = (Simbolo,Aridad)  -- Simbolos con aridad
type SRel       = SimAridad         -- Simbolos de relacion
type SFun       = SimAridad         -- Simbolos de funcion
type SCon       = Simbolo           -- Simbolos de constante
type Alfabeto   = ([SRel],[SFun],[SCon]) -- Alfabetos para FOL: (SimbolosDeRelacion, SimbolosDeFuncion, SimbolosDeConstante)
--
-- Terminos:
data Term =   Tvar Var            -- una variable 
            | Tfun SFun [Term]    -- un simbolo de funcion aplicado a una lista de terminos
            | Tcon SCon           -- un simbolo de constante
            deriving (Eq,Show,Ord,Read)
--
-- Formulas de FOL 
data FOL =    Bot | Top         -- False,True,
            | Pred SRel [Term]  -- Predicados: simbolo de relacion aplicado a una lista de terminos
            | Oimp FOL FOL | Oand FOL FOL | Oor FOL FOL | Oneg FOL  --Implicacion,Conjuncion,Dis,Negacion
            | All Var FOL       -- Formula universal:   \forall x : phi 
            | Exi Var FOL       -- Formula existencial: \exists x : phi
            deriving (Eq,Show,Ord,Read)
--
--
aridadOf :: SimAridad -> Aridad
-- aridad de un simbolo con aridad.
aridadOf s = snd s
--
--
-- Funciones para mostrar terminos y formulas:
--
showTerm :: Term -> String
-- Muestra un termino 
showTerm t  = 
    case t of
        Tvar v           -> v
        Tfun (f,n) lt    -> if length lt==n 
                                then f++ "("++ showLterms lt++ ")"
                                else error $ "showTerm: el numero de parametros de "++f
                                     ++ " es distinto de la aridad, "++show n
        Tcon c           -> c
--
showLterms :: [Term] -> String
-- Muestra una lista de terminos
showLterms lt = case lt of
                     []     -> ""
                     [t]    -> showTerm t
                     t:l    -> showTerm t++"," ++ showLterms l
--
showPred :: FOL -> String
-- Muestra un predicado de FOL
showPred f= 
    case f of
        Pred (p,n) lt  -> if length lt==n 
                            then p++ "("++ showLterms lt++ ")"
                            else error $ "showPred: el numero de parametros de "++p
                                 ++ " es distinto de la aridad, "++show n
        _               -> error $ "showPred: f debe ser un predicado, f="++show f

showFOL :: FOL -> String
-- Muestra una formula de la FOL 
showFOL phi = case phi of
    Bot         -> "FF"
    Top         -> "TT"
    Pred _ _    -> showPred phi
    --
    Oimp p q    -> "("++ (showFOL p) ++" -> "++ (showFOL q) ++")" 
    Oand p q    -> "("++ (showFOL p) ++" & "++ (showFOL q) ++")"
    Oor  p q    -> "("++ (showFOL p) ++" | "++ (showFOL q) ++")"
    Oneg p      -> "~"++(showFOL p)
    --
    All x alpha -> "(ForAll "++ x ++ ". " ++ (showFOL alpha)++")"
    Exi x alpha -> "(Exists "++ x ++ ". " ++ (showFOL alpha)++")"
    --_               -> error $ "showFOL: no definida en este caso, alpha="++show alpha
--
--
varInTerm :: Term -> [Var]
-- Variables que ocurren en un termino.
varInTerm t = case t of
  Tvar x    -> [x]
  Tfun _ [] -> []
  Tfun _ lt -> varInTermL lt
  Tcon _    -> []

varInTermL :: [Term] -> [Var]
-- Variables que ocurren en una lista de términos
varInTermL lt = L.nub $ concat $ map varInTerm lt

freeInFOL :: FOL -> [Var]
-- Variables que ocurren libres en una Formula
freeInFOL phi = case phi of
  Bot       -> []
  Top       -> []
  Pred _ lt -> varInTermL lt
  --
  Oimp a b  -> freeInFOL a `L.union` freeInFOL b
  Oand a b  -> freeInFOL a `L.union` freeInFOL b
  Oor a b   -> freeInFOL a `L.union` freeInFOL b
  Oneg a    -> freeInFOL a
  --
  All x a   -> (freeInFOL a) L.\\ [x]
  Exi x a   -> (freeInFOL a) L.\\ [x]
--
--
--
varInScopeOf :: FOL -> [Var]
-- Variables en el alcance (scope) de un cuantificador Q
--varInScopeOf(Q x. alpha)= [x] si x ocurre libre en alpha, si no: varInScopeOf(Q x. alpha)=[]
varInScopeOf phi = case phi of
    All x alpha -> if x `elem` freeInFOL alpha
                            then [x] 
                            else []
    Exi x alpha -> if x `elem` freeInFOL alpha
                            then [x]
                            else []
    _           -> error $ "varInScopeOf: phi debe ser un cuanficador, phi= "++showFOL phi


boundInFOL :: FOL -> [Var]
-- Variables que ocurren ligadas (bound) en una Formula (bajo el alcance de un cuantificador)
boundInFOL phi = case phi of
  Bot       -> []
  Top       -> []
  Pred _ _  -> []
  --
  Oimp a b  -> boundInFOL a `L.union` boundInFOL b
  Oand a b  -> boundInFOL a `L.union` boundInFOL b
  Oor a b   -> boundInFOL a `L.union` boundInFOL b
  Oneg a    -> boundInFOL a
  --
  All x a   -> (varInScopeOf $ All x a) `L.union` boundInFOL a
  Exi x a   -> (varInScopeOf $ Exi x a) `L.union` boundInFOL a
--
--
checkFormula :: FOL->Alfabeto-> Bool
-- True si phi \in sigma-FOL, es decir phi es una formula de FOL escrita con el alfabeto sigma
checkFormula phi sigma  = error $ "checkFormula: NO implementada"
                        ++ show (phi,sigma) -- XXXX
--
