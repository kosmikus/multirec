{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.TH
-- Copyright   :  (c) 2008 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module contains Template Haskell code that can be used to
-- automatically generate the boilerplate code for the multiplate
-- library. The constructor information can be generated per datatype,
-- the rest per system of datatypes.
--
-----------------------------------------------------------------------------


module Generics.MultiRec.TH
  ( deriveConstructors,
    deriveSystem,
    derivePF,
    deriveIx
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
-- types in the system, and the name (as string) for the
-- pattern functor to derive, generate the 'Ix' and 'PF'
-- instances.

deriveSystem :: Name -> [Name] -> String -> Q [Dec]
deriveSystem n ns pfn =
  do
    pf <- derivePF "PFAST" ns
    ix <- deriveIx n ns
    return $ pf ++ ix

-- | Derive only the 'PF' instance. Not needed if 'deriveSystem'
-- is used.

derivePF :: String -> [Name] -> Q [Dec]
derivePF pfn ns =
    fmap (:[]) $
    tySynD (mkName pfn) [] (foldr1 sum (map (pfType ns) ns))
  where
    sum :: Q Type -> Q Type -> Q Type
    sum a b = conT ''(:+:) `appT` a `appT` b

-- | Derive only the 'Ix' instances. Not needed if 'deriveSystem'
-- is used.

deriveIx :: Name -> [Name] -> Q [Dec]
deriveIx s ns =
  zipWithM (ixInstance s ns (length ns)) [0..] ns

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

mkData :: Con -> Q Dec
mkData (NormalC n _) =
  dataD (cxt []) (mkName (nameBase n)) [] [] [] 
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
pfCon ns (NormalC n fs) =
    appT (appT (conT ''C) (conT $ mkName (nameBase n))) (foldr1 prod (map (pfField ns . snd) fs))
  where
    prod :: Q Type -> Q Type -> Q Type
    prod a b = conT ''(:*:) `appT` a `appT` b
pfCon ns (InfixC t1 n t2) =
    pfCon ns (NormalC n [t1,t2])

pfField :: [Name] -> Type -> Q Type
pfField ns t@(ConT n) | n `elem` ns = conT ''I `appT` return t
pfField ns t                        = conT ''K `appT` return t

ixInstance :: Name -> [Name] -> Int -> Int -> Name -> Q Dec
ixInstance s ns m i n =
  instanceD (cxt []) (conT ''Ix `appT` conT s `appT` conT n)
    [mkFrom ns n m i, mkTo ns n m i, mkIndex n]

mkFrom :: [Name] -> Name -> Int -> Int -> Q Dec
mkFrom ns n m i =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapE e = lrE m i (conE 'Tag `appE` e)
      i <- reify n
      let b = case i of
                TyConI (DataD _ _ _ cs _) ->
                  zipWith (fromCon wrapE ns (length cs)) [0..] cs
                TyConI (TySynD t _ _) ->
                  [clause [varP (field 0)] (normalB (wrapE $ conE 'K `appE` varE (field 0))) []]
                _ -> error "unknown construct" 
      funD 'from_ b 

mkTo :: [Name] -> Name -> Int -> Int -> Q Dec
mkTo ns n m i =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapP p = lrP m i (conP 'Tag [p])
      i <- reify n
      let b = case i of
                TyConI (DataD _ _ _ cs _) ->
                  zipWith (toCon wrapP ns (length cs)) [0..] cs
                TyConI (TySynD t _ _) ->
                  [clause [wrapP $ conP 'K [varP (field 0)]] (normalB $ varE (field 0)) []]
                _ -> error "unknown construct" 
      funD 'to_ b 

mkIndex :: Name -> Q Dec
mkIndex n =
  funD 'index [clause [] (normalB (conE (mkName (nameBase n)))) []]

fromCon :: (Q Exp -> Q Exp) -> [Name] -> Int -> Int -> Con -> Q Clause
fromCon wrap ns m i (NormalC n fs) =
    -- runIO (putStrLn ("constructor " ++ show ix)) >>
    clause
      [conP n (map (varP . field) [0..length fs - 1])]
      (normalB $ wrap $ lrE m i $ conE 'C `appE` foldr1 prod (zipWith (fromField ns) [0..] (map snd fs))) []
  where
    prod x y = conE '(:*:) `appE` x `appE` y
fromCon wrap ns m i (InfixC t1 n t2) =
  fromCon wrap ns m i (NormalC n [t1,t2])

toCon :: (Q Pat -> Q Pat) -> [Name] -> Int -> Int -> Con -> Q Clause
toCon wrap ns m i (NormalC n fs) =
    -- runIO (putStrLn ("constructor " ++ show ix)) >>
    clause
      [wrap $ lrP m i $ conP 'C [foldr1 prod (zipWith (toField ns) [0..] (map snd fs))]]
      (normalB $ foldl appE (conE n) (map (varE . field) [0..length fs - 1])) []
  where
    prod x y = conP '(:*:) [x,y]
toCon wrap ns m i (InfixC t1 n t2) =
  toCon wrap ns m i (NormalC n [t1,t2])

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

