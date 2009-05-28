{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.TH
-- Copyright   :  (c) 2008--2009 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module contains Template Haskell code that can be used to
-- automatically generate the boilerplate code for the multiplate
-- library. The constructor information can be generated per datatype,
-- the rest per family of datatypes.
--
-----------------------------------------------------------------------------


module Generics.MultiRec.TH
  ( deriveConstructors,
    deriveFamily, deriveSystem,
    derivePF,
    deriveEl,
    deriveFam,
    deriveEqS
  ) where

import Generics.MultiRec.Base
import Generics.MultiRec.Constructor
import Language.Haskell.TH hiding (Fixity())
import Language.Haskell.TH.Syntax (Lift(..))
import Control.Monad

-- | Given a list of datatype names, derive datatypes and 
-- instances of class 'Constructor'.

deriveConstructors :: [Name] -> Q [Dec]
deriveConstructors =
  liftM concat . mapM constrInstance

-- | Given the name of the index GADT, the names of the
-- types in the family, and the name (as string) for the
-- pattern functor to derive, generate the 'Ix' and 'PF'
-- instances. /IMPORTANT/: It is assumed that the constructors
-- of the GADT have the same names as the datatypes in the
-- family.

deriveFamily :: Name -> [Name] -> String -> Q [Dec]
deriveFamily n ns pfn =
  do
    pf  <- derivePF pfn ns
    el  <- deriveEl n ns
    fam <- deriveFam n ns
    eq  <- deriveEqS n (map (mkName . nameBase) ns)
    return $ pf ++ el ++ fam ++ eq

-- | Compatibility. Use deriveFamily instead.

deriveSystem :: Name -> [Name] -> String -> Q [Dec]
deriveSystem = deriveFamily

-- | Derive only the 'PF' instance. Not needed if 'deriveFamily'
-- is used.

derivePF :: String -> [Name] -> Q [Dec]
derivePF pfn ns =
    fmap (:[]) $
    tySynD (mkName pfn) [] (foldr1 sum (map (pfType ns) ns))
  where
    sum :: Q Type -> Q Type -> Q Type
    sum a b = conT ''(:+:) `appT` a `appT` b

-- | Derive only the 'El' instances. Not needed if 'deriveFamily'
-- is used.

deriveEl :: Name -> [Name] -> Q [Dec]
deriveEl s ns =
  mapM (elInstance s) ns

-- | Dervie only the 'Fam' instance. Not needed if 'deriveFamily'
-- is used.

deriveFam :: Name -> [Name] -> Q [Dec]
deriveFam s ns =
  do
    fcs <- liftM concat $ zipWithM (mkFrom ns (length ns)) [0..] ns  
    tcs <- liftM concat $ zipWithM (mkTo   ns (length ns)) [0..] ns
    liftM (:[]) $
      instanceD (cxt []) (conT ''Fam `appT` conT s)
        [funD 'from fcs, funD 'to tcs]

-- | Derive only the 'EqS' instance. Not needed if 'deriveFamily'
-- is used.

deriveEqS :: Name -> [Name] -> Q [Dec]
deriveEqS s ns =
    liftM (:[]) $
    instanceD (cxt []) (conT ''EqS `appT` conT s)
      [funD 'eqS (map trueClause ns ++ [falseClause])]
  where
    trueClause n = clause [conP n [], conP n []] (normalB (conE 'Just `appE` conE 'Refl)) []
    falseClause  = clause [wildP,  wildP]        (normalB (conE 'Nothing)) []

constrInstance :: Name -> Q [Dec]
constrInstance n =
  do
    i <- reify n
    -- runIO (print i)
    let cs = case i of
               TyConI (DataD _ _ _ cs _) -> cs
               _ -> []
    ds <- mapM mkData cs
    is <- mapM mkInstance cs
    return $ ds ++ is

stripRecordNames :: Con -> Con
stripRecordNames (RecC n f) =
  NormalC n (map (\(_, s, t) -> (s, t)) f)
stripRecordNames c = c

mkData :: Con -> Q Dec
mkData (NormalC n _) =
  dataD (cxt []) (mkName (nameBase n)) [] [] [] 
mkData r@(RecC _ _) =
  mkData (stripRecordNames r)
mkData (InfixC t1 n t2) =
  mkData (NormalC n [t1,t2])

instance Lift Fixity where
  lift Prefix      = conE 'Prefix
  lift (Infix a n) = conE 'Infix `appE` [| a |] `appE` [| n |]

instance Lift Associativity where
  lift LeftAssociative  = conE 'LeftAssociative
  lift RightAssociative = conE 'RightAssociative
  lift NotAssociative   = conE 'NotAssociative

mkInstance :: Con -> Q Dec
mkInstance (NormalC n _) =
    instanceD (cxt []) (appT (conT ''Constructor) (conT $ mkName (nameBase n)))
      [funD 'conName [clause [wildP] (normalB (stringE (nameBase n))) []]]
mkInstance r@(RecC _ _) =
  mkInstance (stripRecordNames r)
mkInstance (InfixC t1 n t2) =
    do
      i <- reify n
      let fi = case i of
                 DataConI _ _ _ f -> convertFixity f
                 _ -> Prefix
      instanceD (cxt []) (appT (conT ''Constructor) (conT $ mkName (nameBase n)))
        [funD 'conName   [clause [wildP] (normalB (stringE (nameBase n))) []],
         funD 'conFixity [clause [wildP] (normalB [| fi |]) []]]
  where
    convertFixity (Fixity n d) = Infix (convertDirection d) n
    convertDirection InfixL = LeftAssociative
    convertDirection InfixR = RightAssociative
    convertDirection InfixN = NotAssociative

pfType :: [Name] -> Name -> Q Type
pfType ns n =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      i <- reify n
      let b = case i of
                TyConI (DataD _ _ _ cs _) ->
                  foldr1 sum (map (pfCon ns) cs)
                TyConI (TySynD t _ _) ->
                  conT ''K `appT` conT t
                _ -> error "unknown construct" 
      appT (appT (conT ''(:>:)) b) (conT $ mkName (nameBase n))
  where
    sum :: Q Type -> Q Type -> Q Type
    sum a b = conT ''(:+:) `appT` a `appT` b

pfCon :: [Name] -> Con -> Q Type
pfCon ns (NormalC n []) =
    appT (appT (conT ''C) (conT $ mkName (nameBase n))) (conT ''U)
pfCon ns (NormalC n fs) =
    appT (appT (conT ''C) (conT $ mkName (nameBase n))) (foldr1 prod (map (pfField ns . snd) fs))
  where
    prod :: Q Type -> Q Type -> Q Type
    prod a b = conT ''(:*:) `appT` a `appT` b
pfCon ns r@(RecC _ _) =
  pfCon ns (stripRecordNames r)
pfCon ns (InfixC t1 n t2) =
    pfCon ns (NormalC n [t1,t2])

pfField :: [Name] -> Type -> Q Type
pfField ns t@(ConT n) | n `elem` ns = conT ''I `appT` return t
pfField ns t                        = conT ''K `appT` return t

elInstance :: Name -> Name -> Q Dec
elInstance s n =
  instanceD (cxt []) (conT ''El `appT` conT s `appT` conT n)
    [mkProof n]

mkFrom :: [Name] -> Int -> Int -> Name -> Q [Q Clause]
mkFrom ns m i n =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapE e = lrE m i (conE 'Tag `appE` e)
      i <- reify n
      let dn = mkName (nameBase n)
      let b = case i of
                TyConI (DataD _ _ _ cs _) ->
                  zipWith (fromCon wrapE ns dn (length cs)) [0..] cs
                TyConI (TySynD t _ _) ->
                  [clause [conP dn [], varP (field 0)] (normalB (wrapE $ conE 'K `appE` varE (field 0))) []]
                _ -> error "unknown construct"
      return b

mkTo :: [Name] -> Int -> Int -> Name -> Q [Q Clause]
mkTo ns m i n =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapP p = lrP m i (conP 'Tag [p])
      i <- reify n
      let dn = mkName (nameBase n)
      let b = case i of
                TyConI (DataD _ _ _ cs _) ->
                  zipWith (toCon wrapP ns dn (length cs)) [0..] cs
                TyConI (TySynD t _ _) ->
                  [clause [conP dn [], wrapP $ conP 'K [varP (field 0)]] (normalB $ varE (field 0)) []]
                _ -> error "unknown construct" 
      return b

mkProof :: Name -> Q Dec
mkProof n =
  funD 'proof [clause [] (normalB (conE (mkName (nameBase n)))) []]

fromCon :: (Q Exp -> Q Exp) -> [Name] -> Name -> Int -> Int -> Con -> Q Clause
fromCon wrap ns n m i (NormalC cn []) =
    clause
      [conP n [], conP cn []]
      (normalB $ wrap $ lrE m i $ conE 'C `appE` (conE 'U)) []
fromCon wrap ns n m i (NormalC cn fs) =
    -- runIO (putStrLn ("constructor " ++ show ix)) >>
    clause
      [conP n [], conP cn (map (varP . field) [0..length fs - 1])]
      (normalB $ wrap $ lrE m i $ conE 'C `appE` foldr1 prod (zipWith (fromField ns) [0..] (map snd fs))) []
  where
    prod x y = conE '(:*:) `appE` x `appE` y
fromCon wrap ns n m i r@(RecC _ _) =
  fromCon wrap ns n m i (stripRecordNames r)
fromCon wrap ns n m i (InfixC t1 cn t2) =
  fromCon wrap ns n m i (NormalC cn [t1,t2])

toCon :: (Q Pat -> Q Pat) -> [Name] -> Name -> Int -> Int -> Con -> Q Clause
toCon wrap ns n m i (NormalC cn []) =
    clause
      [conP n [], wrap $ lrP m i $ conP 'C [conP 'U []]]
      (normalB $ conE cn) []
toCon wrap ns n m i (NormalC cn fs) =
    -- runIO (putStrLn ("constructor " ++ show ix)) >>
    clause
      [conP n [], wrap $ lrP m i $ conP 'C [foldr1 prod (zipWith (toField ns) [0..] (map snd fs))]]
      (normalB $ foldl appE (conE cn) (map (varE . field) [0..length fs - 1])) []
  where
    prod x y = conP '(:*:) [x,y]
toCon wrap ns n m i r@(RecC _ _) =
  toCon wrap ns n m i (stripRecordNames r)
toCon wrap ns n m i (InfixC t1 cn t2) =
  toCon wrap ns n m i (NormalC cn [t1,t2])

fromField :: [Name] -> Int -> Type -> Q Exp
fromField ns nr t@(ConT n) | n `elem` ns = conE 'I `appE` (conE 'I0 `appE` varE (field nr))
fromField ns nr t                        = conE 'K `appE` varE (field nr)

toField :: [Name] -> Int -> Type -> Q Pat
toField ns nr t@(ConT n) | n `elem` ns = conP 'I [conP 'I0 [varP (field nr)]]
toField ns nr t                        = conP 'K [varP (field nr)]

field :: Int -> Name
field n = mkName $ "f" ++ show n

lrP :: Int -> Int -> (Q Pat -> Q Pat)
lrP 1 0 p = p
lrP m 0 p = conP 'L [p]
lrP m i p = conP 'R [lrP (m-1) (i-1) p]

lrE :: Int -> Int -> (Q Exp -> Q Exp)
lrE 1 0 e = e
lrE m 0 e = conE 'L `appE` e
lrE m i e = conE 'R `appE` lrE (m-1) (i-1) e

