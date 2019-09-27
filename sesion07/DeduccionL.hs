module DeduccionL
{-Facultad de Ciencias UNAM - Lógica Computacional 2020-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Sara Doris Montes Incin
		  Laboratorio: Mauricio Esquivel Reyes-}

where
--
import Data.List as L (lookup)
--
----------------------------------------------------------------
import SintaxisPLI

-- Función que nos dice si una formula de PLI cumple el Axioma 1
esAxL1 :: PLI -> Bool
esAxL1 phi = case phi of
  (alpha `Oimp` (_ `Oimp` beta)) -> alpha == beta
  _                              -> False

-- Función que nos dice si una formula de PLI cumple el Axioma 2
esAxL2 :: PLI -> Bool
esAxL2 phi = case phi of
  (alpha `Oimp` (beta `Oimp` gamma)) `Oimp` ((delta `Oimp` epsilon) `Oimp` (zeta `Oimp` eta)) -> (alpha == delta && delta == zeta) && (beta == epsilon) && (gamma == eta)
  _                              -> False

-- Función que nos dice si una formula de PLI cumple el Axioma 3
esAxL3 :: PLI -> Bool
esAxL3 phi = case phi of
  ((alpha `Oimp` Bot) `Oimp` (beta `Oimp` Bot)) `Oimp` (((gamma `Oimp` Bot) `Oimp` delta) `Oimp` eta) -> (alpha == gamma && gamma == eta) && beta == delta
  _                              -> False

-- Para toda phi \in PLI, Bool -> phi 
esAxL4 :: PLI -> Bool
esAxL4 phi = case phi of
  Bot `Oimp` _ -> True
  _            -> False

-- Función que nos dice si una formula es una Axioma del sistema L
esAxiomaDeL :: PLI -> Bool
esAxiomaDeL phi = esAxL1 phi || esAxL2 phi || esAxL3 phi || esAxL4 phi

-- Función que nos dice si se aplico de manera correcta Modus Ponens
esModusPonens :: (PLI, PLI, PLI) -> Bool
esModusPonens (phi, chi, psi) = case (phi, chi, psi) of
  (alpha, beta `Oimp` gamma, delta) -> (alpha == beta) && (gamma == delta) 
  _ -> False
--
-- Teoremas numerados:
-- Def1. (n,(fn,pn)) es un teorema numerado (NumTeo) sii:
--              1) n in N
--              2) fn in PLI
--              3) pn es una prueba (sin premisas) en L
--              4) fn=formulaDelUltimoPaso(pn)
-- Def2. lTeo es una lista de teoremas numerados sii:
--          1) lTeo :: [NumTeo] 
--          2) \forall (n,fn,pn),(n',fn',pn') in lTeo: (n,fn,pn)=(n',fn',pn') => n=n'
type NumTeo = (Int,(PLI,[NumPaso])) 
--

type NumCor = (Int,(PLI, [PLI], [NumPaso]))

-- Reglas del sistema L
data ReglaL = Prem           -- Justificación por premisa
            | Ax             -- Justificación por un axioma
            | ModPon Int Int -- Justificación por aplicación de MP a dos formulas anteriores
            | Cor Int Int Int
--             | Teo Int [NumTeo]      -- TeoL n lTeo justifica a phi sii 
            | Teo Int        -- Justificación por teorema
                                    -- Si lTeo es una lista de teoremas numerados (ver Def2), 
                                    -- entonces, TeoL n justifica a phi, respecto a lTeo, sii 
                                    --      1) Existe (n,fn,pn) in lTeo: phi es una instancia de fn.
            deriving (Eq,Show)
-- Tipo Paso
-- Una fomula PLI y la Regla utilizada
type Paso = (PLI, ReglaL)

-- Tipo Numero de Paso
type NumPaso = (Int, Paso)

-- Nos regresa la formula del paso n
phiPasoNum :: Int -> [NumPaso] -> PLI
phiPasoNum i lpasos = case mpi of
  Just (phi, _) -> phi
  Nothing       -> error $ "phiPasoNum: indice fuera de rango."
  where
    mpi = lookup i lpasos
    
-- Nos regresa el último NumPaso de una lista
ultimoPaso :: [NumPaso] -> NumPaso
ultimoPaso lpasos
  | lpasos /= [] = (n,p)
  | otherwise = (0,(oTop,Prem))
  where
    (n,p) = last lpasos
--
checkPrem :: [PLI] -> [NumPaso] -> NumPaso -> Bool
-- Revisamos que phi sea parte de lprem
checkPrem lprem lpp p = 
    case p of
         (n, (phi, Prem))   ->     n == nU+1
                                && phi `elem` lprem 
         _                  -> False      
    where
    (nU,_) = ultimoPaso lpp
--
checkAx :: [NumPaso] -> NumPaso -> Bool
-- Revisamos que phi sea un axioma
checkAx lpp p = 
    case p of
         (n, (phi, Ax)) ->     n == nU+1
                            && esAxiomaDeL phi
         _              -> False
    where
    (nU,_) = ultimoPaso lpp
--
checkModPon :: Int->Int-> [NumPaso] -> NumPaso -> Bool
-- Revisamos que phi sea resultado de hacer modus ponens con i y j
checkModPon i j lpp p = 
    case p of
         (n, (phi, ModPon _ _)) ->     n == nU+1
                                    && esModusPonens (alpha, beta, phi)
         _                      -> False
    where
    (nU,_)  = ultimoPaso lpp
    alpha   = phiPasoNum i lpp
    beta    = phiPasoNum j lpp
--
--
esInstanciaSubs :: [(Indice,PLI)]-> PLI -> PLI -> (Bool,[(Indice,PLI)])
-- El segundo componente de (esInstanciaSubs subsL f g) indica si f es instancia de g, usando la lista de susticiones subsL.
-- La lista subsL acumula las susticiones que demuestran que f es instancia de g.
-- El Valor inicial de subsL es []: esInstanciaSubs [] f g.
-- REVISAR. Las instancias/susticiones siempre son delicadas.
esInstanciaSubs subsL f g = 
    case g of
        Bot         -> (f==Bot,subsL)
        Var n       -> case nSust of
                        Just gn -> -- Si ya existe una susticion para v_n: (n,gn):
                                    if f==gn -- Si f = la susticion que ya existe:
                                        then (True,subsL)   -- f es instancia de g
                                        else (False,subsL)  -- f no es instancia de g
                        Nothing -> -- Si no existe una susticion para v_n:
                                    (True,(n,f):subsL) -- f es instancia de g, y agrega la susticion.
                        where
                        nSust = lookup n subsL
        k `Oimp` l  -> case f of
                        k' `Oimp` l' -> if kkInst -- Si k' es instancia de k:
                                            then (esInstanciaSubs kkSubL l' l) -- revisa si l' es instancia de l
                                            else (kkInst,kkSubL) -- si no: f no es instancia de g
                                        where
                                        (kkInst,kkSubL) = esInstanciaSubs subsL k' k
                        _            -> (False,subsL)
--
esInstanciaDe :: PLI -> PLI -> Bool
-- REVISAR. Las instancias/susticiones siempre son delicadas.
esInstanciaDe f g = fst $ esInstanciaSubs [] f g


esInstanciaLDe :: PLI -> [PLI] -> Bool
esInstanciaLDe f gamma = or $ map (esInstanciaDe f) gamma

--
checkTeo :: Int -> [NumTeo] -> [NumPaso] -> NumPaso -> Bool
-- Precondition: lTeoP es una la lista de teoremas numerados (Ver Def1 y Def2).
-- Revisamos que phi es instancia del teorema m de lTeo, i.e. (m,(tm,pm)) in lTeo y phi es instancia de tm.
checkTeo m lTeo lpp p = 
    case p of
        (n,(phi,Teo _ ))    ->     n == nU+1
                                && phi `esInstanciaDe` tm
        _                   -> False
    where
    (nU,(_,_))  = ultimoPaso lpp
    mTeo        = lookup m lTeo
    tm          = case mTeo of
                    Just (fm,_) -> fm
                    Nothing     -> error $ "checkTeo: el teorema m no existe, m= "++show m
--

checkCor :: Int -> Int -> Int -> [NumCor] -> [NumPaso] -> NumPaso -> Bool
checkCor m i j lCor lpp p =
  case p of
    (n,(phi,Cor _ _ _)) ->   n == nU+1
                          && phi `esInstanciaDe` cm
                          && alpha `esInstanciaLDe` pcm
                          && beta `esInstanciaLDe` pcm
    _                          -> False
  where
    alpha   = phiPasoNum i lpp
    beta    = phiPasoNum j lpp
    (nU,(_,_))  = ultimoPaso lpp
    mCor        = lookup m lCor
    (cm, pcm)          = case mCor of
      Just (fm,pm,_) -> (fm,pm)
      Nothing     -> error $ "checkCor: el corolario m no existe, m= "++show m

-- --
checkPaso :: [NumTeo]-> [NumCor] -> [PLI]-> [NumPaso]-> NumPaso-> Bool
-- Revisa que el paso sea correcto.
-- lTeo lprem lpp p: Lista de teoremas, Lista de premisas, Lista de pasos, paso actual.
checkPaso lTeo lCor lprem lpp p@(_, (_, reglaDeL)) =
    case reglaDeL of
        Prem        -> checkPrem lprem lpp p
        Ax          -> checkAx lpp p
        ModPon i j  -> checkModPon i j lpp p
        Teo m       -> checkTeo m lTeo lpp p
        Cor n i j   -> checkCor n i j lCor lpp p
        --_               -> error $ "checkPaso: reglaDeL debe ser una regla de L, reglaDeL= "++show reglaDeL
--
-- Revisa que la prueba sea correcta
checkPrueba :: [NumTeo]-> [NumCor] -> [PLI] -> [NumPaso] -> Bool
checkPrueba lTeo lCor lprem lpasos = case lpasos of
  []      -> True -- Si la lista es vacía entonces es cierto
  _:_     -> checkPrueba lTeo lCor lprem lpp && checkPaso lTeo lCor lprem lpp p -- Hacemos recursión.
  where
    n   = length lpasos
    lpp = Prelude.take (n-1) lpasos
    p   = last lpasos
--
esTeoremaPrueba :: [NumTeo]-> [NumCor] -> PLI -> [NumPaso] -> Bool
-- esTeoremaPrueba lTeo phi lpp= true sii lpp es una prueba (lista de pasos) que testifica que {} |- phi .
-- Def. Sea phi in PLI. Decimos que phi es un teorema de L sii phi se deduce en L sin usar premisas.
esTeoremaPrueba lTeo lCor phi lpp =     phi == fN                -- phi es la formula del ultimo paso
                                && checkPrueba lTeo lCor [] lpp  -- lpp es una prueba (sin premisas).
                        where
                        (_, (fN, _))= last lpp

esCorolarioPrueba :: [NumTeo] -> [NumCor] -> PLI -> [PLI] -> [NumPaso] -> Bool
esCorolarioPrueba lTeo lCor phi gamma lpp =  phi == fN
                                     && checkPrueba lTeo lCor gamma lpp
                                     where
                                     (_, (fN, _)) = last lpp
--
--Muestra una lista de formulas.
showLphi :: [PLI] -> String
showLphi lphi= case lphi of
                    [f]     -> showPLI f
                    f:lf    -> showPLI f ++","++ showLphi lf
                    []      -> ""

-- Muesta la regla
showRegla :: [NumTeo] -> [NumCor] -> ReglaL -> String
showRegla lTeo lCor r = case r of
    Prem          -> "premisa"
    Ax            -> "axioma"
    ModPon i j    -> "Modus Ponens "++show i++","++show j
    Teo  m        -> "Teo"++show m ++":" ++showPLI teo
                    where
                    mTeo = lookup m lTeo
                    teo  = case mTeo of
                                Just (fm,_) -> fm
                                Nothing     -> error $ "showRegla: el teorema m no existe, m= "++show m
    Cor n k l     -> "Cor"++show n ++":" ++showPLI cor
                    where
                    mCor = lookup n lCor
                    cor = case mCor of
                      Just (cm,_,_) -> cm
                      Nothing       -> error $ "showRegla: el corolario n no existe, n= " ++show n
--
-- Muestra un paso indicando, mediante b, si es correcto, o no.
showNumPasoCheck :: [NumTeo]-> [NumCor] -> Int -> NumPaso -> Bool -> String
showNumPasoCheck lTeo lCor fSize (n,(phi, r)) b = "\t" ++ (show n) ++ ") " ++ fS ++ spaceAfterPhi ++ rS ++ checks
  where
    fS = showPLI phi
    spaceAfterPhi = " " ++ Prelude.take (fSize-(length fS)) (repeat ' ')
    rS = "\t" ++ (showRegla lTeo lCor r)
    checks = if b
      then ". Correcto"
      else ". Incorrecto"

-- Muestra los pasos de lpasos indicando si son correctos, o no.
-- Initial call: showLpasos fSize lprem [] lpasos
showLpasos :: Int -> [NumTeo]-> [NumCor] -> [PLI] -> [NumPaso] -> [NumPaso] -> IO ()
showLpasos fSize lTeo lCor lprem prevLp lpasos = case lpasos of
  []    -> putStr ""
  p:lps ->  do
            putStrLn $ showNumPasoCheck lTeo lCor fSize p (checkPaso lTeo lCor lprem prevLp p)
            showLpasos fSize lTeo lCor lprem (prevLp++[p]) lps


showCheckConclusion :: [NumTeo]-> [NumCor] -> [PLI] -> [NumPaso] -> PLI -> IO ()
showCheckConclusion lTeo lCor lpremisas lpasos phi =
  do
    putStrLn mensaje
    putStrLn ""
    where
      mensaje
        | not pruebaOK = "\t*** Hay pasos incorrectos. ***"
        | phi /= fN = "\t*** La ultima formula no es el objetivo: ***"++ (showPLI phi) ++" /= "++ (showPLI fN)
        | otherwise =  "\tCorrecto. Mediante el sistema L: "++ lpremS ++ " |- " ++ showPLI fN
      pruebaOK = checkPrueba lTeo lCor lpremisas lpasos
      (_,(fN,_)) = ultimoPaso lpasos
      lpremS = if lpremisas /= []
        then "{" ++ showLphi lpremisas ++"}"
        else ""
        
--
maxL :: Ord a => [a] -> a
maxL = foldr1 (\x y ->if x >= y then x else y)
--

esDeduccionEnL :: [NumTeo] -> [NumCor] -> [PLI] -> [NumPaso] -> PLI -> IO()
esDeduccionEnL lTeo lCor lpremisas lpasos phi =
  do
    showLpasos fSize lTeo lCor lpremisas [] lpasos
    showCheckConclusion lTeo lCor lpremisas lpasos phi
  where
    fSize = maxL [length (showPLI f) | (_,(f,_)) <- lpasos ]
