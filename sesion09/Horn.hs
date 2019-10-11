type Indice = Int

data Hatom  =  Htop | Hbot | Hvar Indice deriving (Eq, Show) 
-- Clausula de Horn: Premisa=[atomo1,...,atomoN] -> Conclusion=Atomo
data Fhorn  =   Himp [Hatom] Hatom
-- Conjuncion de formulas de Horn 
  | Hand Fhorn Fhorn  deriving (Eq, Show)                      



atomosMarcados :: [Hatom] -> [Hatom] -> Bool
atomosMarcados lm premisa = and [a `elem` lm | a <- premisa] 

marcaConclusiones :: [Hatom] -> [Fhorn] -> [Hatom]
marcaConclusiones lMarcados lcH = case lcH of
  [] -> lMarcados
  (Himp _ c):cHs -> marcaConclusiones (c:lMarcados) cHs
  _  -> error $ "marcaConclusiones: no es una clausula de Horn: "++show (head lcH)

clausulasHmarcables :: [Hatom] -> Fhorn -> [Fhorn]
clausulasHmarcables lMarcados phi = case phi of
  Himp premisa conclusion -> if (atomosMarcados lMarcados premisa) && (conclusion `notElem` lMarcados)
    then [phi]
    else []
  Hand f1 f2 -> clausulasHmarcables lMarcados f1 ++ clausulasHmarcables lMarcados f2

marcaFormulaHorn :: [Hatom] -> Fhorn -> [Hatom]
marcaFormulaHorn lMarcados phi =
  if cHornMarcables == []
  then lMarcados
  else marcaFormulaHorn lMarcadosNew phi
  where
    cHornMarcables  = clausulasHmarcables lMarcados phi
    lMarcadosNew    = marcaConclusiones lMarcados cHornMarcables

enSatHorn :: Fhorn -> Bool
enSatHorn phi = if Hbot `elem` (marcaFormulaHorn [Htop] phi)
  then False
  else True
