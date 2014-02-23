{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE CPP             #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.MultiRec.TH
-- Copyright   :  (c) 2008--2010 Universiteit Utrecht
-- License     :  BSD3
--
-- Maintainer  :  generics@haskell.org
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module contains Template Haskell code that can be used to
-- automatically generate the boilerplate code for the multirec
-- library. The constructor information can be generated per datatype,
-- the rest per family of datatypes.
--
-----------------------------------------------------------------------------


module Generics.MultiRec.TH
  ( deriveAll,
    deriveConstructors,
    deriveFamily, deriveSystem,
    derivePF,
    deriveEl,
    deriveFam,
    deriveEqS
  ) where

import Generics.MultiRec.Base
import Language.Haskell.TH hiding (Fixity())
import Control.Applicative
import Control.Monad

-- | Given the name of the family index GADT, derive everything.
deriveAll :: Name -> Q [Dec]
deriveAll n =
  do
    info <- reify n
    -- runIO (print info)
    let ps  = init (extractParameters info)
    let nps = map (\ (n, ps) -> (remakeName n, ps)) (extractConstructorNames ps info)
    let ns  = map fst nps
    -- runIO (print nps)
    cs  <- deriveConstructors ns
    pf  <- derivePFInstance n ps nps
    el  <- deriveEl n ps nps
    fam <- deriveFam n ps ns
    eq  <- deriveEqS n ps ns
    return $ cs ++ pf ++ el ++ fam ++ eq

-- | Given a list of datatype names, derive datatypes and
-- instances of class 'Constructor'. Not needed if 'deriveAll'
-- is used.
deriveConstructors :: [Name] -> Q [Dec]
deriveConstructors =
  liftM concat . mapM constrInstance

-- | Compatibility. Use 'deriveAll' instead.
--
-- Given the name of the index GADT, the names of the
-- types in the family, and the name (as string) for the
-- pattern functor to derive, generate the 'Ix' and 'PF'
-- instances. /IMPORTANT/: It is assumed that the constructors
-- of the GADT have the same names as the datatypes in the
-- family.
{-# DEPRECATED deriveFamily "Use deriveAll instead." #-}
deriveFamily :: Name -> [Name] -> String -> Q [Dec]
deriveFamily n ns pfn =
  do
    pf  <- derivePF pfn ns
    el  <- deriveEl n [] (zip ns (repeat []))
    fam <- deriveFam n [] ns
    eq  <- deriveEqS n [] (map remakeName ns)
    return $ pf ++ el ++ fam ++ eq

-- | Compatibility. Use 'deriveAll' instead.
{-# DEPRECATED deriveSystem "Use deriveFamily instead" #-}
deriveSystem :: Name -> [Name] -> String -> Q [Dec]
deriveSystem = deriveFamily

-- | Derive only the 'PF' instance. Not needed if 'deriveAll'
-- is used.
derivePF :: String -> [Name] -> Q [Dec]
derivePF pfn ns =
    return <$>
    tySynD (mkName pfn) [] (foldr1 sum (map (pfType ns []) (zip ns (repeat []))))
  where
    sum :: Q Type -> Q Type -> Q Type
    sum a b = conT ''(:+:) `appT` a `appT` b

derivePFInstance :: Name -> [Name] -> [(Name, [Name])] -> Q [Dec]
derivePFInstance n ps nps = return <$> myTySynInst
  where
    sum :: Q Type -> Q Type -> Q Type
    sum a b = conT ''(:+:) `appT` a `appT` b
    tys = [foldl appT (conT n) (map varT ps)]
    ty  = foldr1 sum (map (pfType (map fst nps) ps) nps)
#if __GLASGOW_HASKELL__ > 706
    myTySynInst = tySynInstD ''PF (tySynEqn tys ty)
#else
    myTySynInst = tySynInstD ''PF tys ty
#endif

-- | Derive only the 'El' instances. Not needed if 'deriveAll'
-- is used.
deriveEl :: Name -> [Name] -> [(Name, [Name])] -> Q [Dec]
deriveEl s ps ns =
  mapM (elInstance s ps) ns

-- | Derive only the 'Fam' instance. Not needed if 'deriveAll'
-- is used.
deriveFam :: Name -> [Name] -> [Name] -> Q [Dec]
deriveFam s ps ns =
  do
    fcs <- liftM concat $ zipWithM (mkFrom ns (length ns)) [0..] ns
    tcs <- liftM concat $ zipWithM (mkTo   ns (length ns)) [0..] ns
    return <$>
      instanceD (cxt []) (conT ''Fam `appT` (foldl appT (conT s) (map varT ps)))
        [funD 'from fcs, funD 'to tcs]

-- | Derive only the 'EqS' instance. Not needed if 'deriveAll'
-- is used.
deriveEqS :: Name -> [Name] -> [Name] -> Q [Dec]
deriveEqS s ps ns =
    return <$>
    instanceD (cxt []) (conT ''EqS `appT` (foldl appT (conT s) (map varT ps)))
      [funD 'eqS (trues ++ falses)]
  where
    trueClause n = clause [conP n [], conP n []] (normalB (conE 'Just `appE` conE 'Refl)) []
    falseClause  = clause [wildP,  wildP]        (normalB (conE 'Nothing)) []
    trues        = map trueClause ns
    falses       = if length trues == 1 then [] else [falseClause]

-- | Process the reified info of the index GADT, and extract
-- its constructor names, which are also the names of the datatypes
-- that are part of the family.
extractConstructorNames :: [Name] -> Info -> [(Name, [Name])]
extractConstructorNames ps (TyConI (DataD _ _ _ cs _)) = concatMap extractFrom cs
  where
    extractFrom :: Con -> [(Name, [Name])]
    extractFrom (ForallC _ eqs c) = map (\ (n, _) -> (n, concatMap extractEq eqs)) (extractFrom c)
    extractFrom (InfixC _ n _)    = [(n, [])]
    extractFrom (RecC n _)        = [(n, [])]
    extractFrom (NormalC n [])    = [(n, [])]
    extractFrom _                 = []

    extractEq :: Pred -> [Name]
    extractEq (EqualP t1 t2) = filter (\ p -> p `elem` ps) (extractArgs t1 ++ extractArgs t2)
    extractEq _              = []

    extractArgs :: Type -> [Name]
    extractArgs (AppT x (VarT n)) = extractArgs x ++ [n]
    extractArgs (VarT n)          = [n]
    extractArgs _                 = []

extractConstructorNames _  _                           = []


-- | Process the reified info of the index GADT, and extract
-- its type parameters.
extractParameters :: Info -> [Name]
extractParameters (TyConI (DataD _ _ ns _ _)) = concatMap extractFromBndr ns
extractParameters (TyConI (TySynD _ ns _))    = concatMap extractFromBndr ns
extractParameters _                           = []

extractFromBndr :: TyVarBndr -> [Name]
extractFromBndr (PlainTV n)    = [n]
extractFromBndr (KindedTV n _) = [n]

-- | Turn a record-constructor into a normal constructor by just
-- removing all the field names.
stripRecordNames :: Con -> Con
stripRecordNames (RecC n f) =
  NormalC n (map (\(_, s, t) -> (s, t)) f)
stripRecordNames c = c

-- | Takes the name of a datatype (element of the family).
-- By reifying the datatype, we obtain its constructors.
-- For each constructor, we then generate a constructor-specific
-- datatype, and an instance of the 'Constructor' class.
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

-- | Given a constructor, create an empty datatype of
-- the same name.
mkData :: Con -> Q Dec
mkData (NormalC n _) =
  dataD (cxt []) (remakeName n) [] [] []
mkData r@(RecC _ _) =
  mkData (stripRecordNames r)
mkData (InfixC t1 n t2) =
  mkData (NormalC n [t1,t2])
mkData (ForallC _ _ c) =
  mkData c

fixity :: Fixity -> ExpQ
fixity Prefix      = conE 'Prefix
fixity (Infix a n) = conE 'Infix `appE` assoc a `appE` [| n |]

assoc :: Associativity -> ExpQ
assoc LeftAssociative  = conE 'LeftAssociative
assoc RightAssociative = conE 'RightAssociative
assoc NotAssociative   = conE 'NotAssociative

-- | Given a constructor, create an instance of the 'Constructor'
-- class for the datatype associated with the constructor.
mkInstance :: Con -> Q Dec
mkInstance (NormalC n _) =
    instanceD (cxt []) (appT (conT ''Constructor) (conT $ remakeName n))
      [funD 'conName [clause [wildP] (normalB (stringE (nameBase n))) []]]
mkInstance r@(RecC _ _) =
  mkInstance (stripRecordNames r)
mkInstance (ForallC _ _ c) =
  mkInstance c
mkInstance (InfixC t1 n t2) =
    do
      i <- reify n
      let fi = case i of
                 DataConI _ _ _ f -> convertFixity f
                 _ -> Prefix
      instanceD (cxt []) (appT (conT ''Constructor) (conT $ remakeName n))
        [funD 'conName   [clause [wildP] (normalB (stringE (nameBase n))) []],
         funD 'conFixity [clause [wildP] (normalB (fixity fi)) []]]
  where
    convertFixity (Fixity n d) = Infix (convertDirection d) n
    convertDirection InfixL = LeftAssociative
    convertDirection InfixR = RightAssociative
    convertDirection InfixN = NotAssociative

-- | Takes all the names of datatypes belonging to the family, and
-- a particular of these names. Produces the right hand side of the 'PF'
-- type family instance for this family.
pfType :: [Name] -> [Name] -> (Name, [Name]) -> Q Type
pfType ns ps (n, rs) =
    do
      i <- reify n
      let qs = extractParameters i
      -- runIO $ putStrLn $ "processing " ++ show n
      let b = case i of
                -- datatypes are nested binary sums of their constructors
                TyConI (DataD _ _ _ cs _) ->
                  foldr1 sum (map (pfCon ns (zip qs rs)) cs)
                -- type synonyms are always treated as constants
                TyConI (TySynD t _ _) ->
                  conT ''K `appT` foldl appT (conT t) (map varT rs)
                _ -> error "unknown construct"
      appT (appT (conT ''(:>:)) b) (foldl appT (conT $ remakeName n) (map varT rs))
  where
    sum :: Q Type -> Q Type -> Q Type
    sum a b = conT ''(:+:) `appT` a `appT` b

-- | Takes all the names of datatypes belonging to the family, and
-- a particular name of a constructor of one of the datatypes. Creates
-- the product structure for this constructor.
pfCon :: [Name] -> [(Name, Name)] -> Con -> Q Type
pfCon ns ps r@(RecC _ _) =
    pfCon ns ps (stripRecordNames r)
pfCon ns ps (InfixC t1 n t2) =
    pfCon ns ps (NormalC n [t1,t2])
pfCon ns ps (ForallC _ _ c) =
    pfCon ns ps c
pfCon ns ps (NormalC n []) =
    -- a constructor without arguments is represented using 'U'
    appT (appT (conT ''C) (conT $ remakeName n)) (conT ''U)
pfCon ns ps (NormalC n fs) =
    -- a constructor with arguments is a nested binary product
    appT (appT (conT ''C) (conT $ remakeName n))
         (foldr1 prod (map (pfField ns ps . snd) fs))
  where
    prod :: Q Type -> Q Type -> Q Type
    prod a b = conT ''(:*:) `appT` a `appT` b

-- | Takes all the names of datatypes belonging to the family, and
-- a particular type (that occurs as a field in one of these
-- datatypes). Produces the structure for this type. We have to
-- distinguish between recursive calls, compositions, and constants.
--
-- TODO: We currently treat all applications as compositions. However,
-- we can argue that applications should be treated as compositions only
-- if the entire construct cannot be treated as a constant.
pfField :: [Name] -> [(Name, Name)] -> Type -> Q Type
pfField ns ps t@(ConT n)
  | remakeName n `elem` ns             = conT ''I `appT` return t
pfField ns ps t
  | ConT n : a <- unApp t, remakeName n `elem` ns
                                       = conT ''I `appT` (foldl appT (conT n) (map rename a))
  where
    rename (VarT n)
      | Just p <- lookup n ps          = varT p
    rename t                           = return t
pfField ns ps t@(AppT f a)             = conT ''(:.:) `appT` return f `appT` pfField ns ps a
pfField ns ps t@(VarT n)
  | Just p <- lookup n ps              = {- runIO (print (ps, n)) >> -} conT ''K `appT` varT p
pfField ns ps t                        = conT ''K `appT` return t

unApp :: Type -> [Type]
unApp (AppT f a) = unApp f ++ [a]
unApp t          = [t]

elInstance :: Name -> [Name] -> (Name, [Name]) -> Q Dec
elInstance s ps (n, qs) =
  do
    -- runIO (print (ps, qs))
    instanceD (cxt []) (conT ''El `appT` (foldl appT (conT s) (map varT ps)) `appT` (foldl appT (conT n) (map varT qs)))
      [mkProof n]

mkFrom :: [Name] -> Int -> Int -> Name -> Q [Q Clause]
mkFrom ns m i n =
    do
      -- runIO $ putStrLn $ "processing " ++ show n
      let wrapE e = lrE m i (conE 'Tag `appE` e)
      i <- reify n
      let dn = remakeName n
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
      let dn = remakeName n
      let b = case i of
                TyConI (DataD _ _ _ cs _) ->
                  zipWith (toCon wrapP ns dn (length cs)) [0..] cs
                TyConI (TySynD t _ _) ->
                  [clause [conP dn [], wrapP $ conP 'K [varP (field 0)]] (normalB $ varE (field 0)) []]
                _ -> error "unknown construct"
      return b

mkProof :: Name -> Q Dec
mkProof n =
  funD 'proof [clause [] (normalB (conE (remakeName n))) []]

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
fromCon wrap ns n m i (ForallC _ _ c) =
  fromCon wrap ns n m i c

toCon :: (Q Pat -> Q Pat) -> [Name] -> Name -> Int -> Int -> Con -> Q Clause
toCon wrap ns n m i (NormalC cn []) =
    clause
      [conP n [], wrap $ lrP m i $ conP 'C [conP 'U []]]
      (normalB $ conE cn) []
toCon wrap ns n m i (NormalC cn fs) =
    -- runIO (putStrLn ("constructor " ++ show ix)) >>
    clause
      [conP n [], wrap $ lrP m i $ conP 'C [foldr1 prod (map (varP . field) [0..length fs - 1])]]
      (normalB $ foldl appE (conE cn) (zipWith (toField ns) [0..] (map snd fs))) []
  where
    prod x y = conP '(:*:) [x,y]
toCon wrap ns n m i r@(RecC _ _) =
  toCon wrap ns n m i (stripRecordNames r)
toCon wrap ns n m i (InfixC t1 cn t2) =
  toCon wrap ns n m i (NormalC cn [t1,t2])
toCon wrap ns n m i (ForallC _ _ c) =
  toCon wrap ns n m i c

fromField :: [Name] -> Int -> Type -> Q Exp
fromField ns nr t = [| $(fromFieldFun ns t) $(varE (field nr)) |]

fromFieldFun :: [Name] -> Type -> Q Exp
fromFieldFun ns t@(ConT n)
  | remakeName n `elem` ns   = [| I . I0 |]
fromFieldFun ns t
  | ConT n : a <- unApp t, remakeName n `elem` ns
                             = [| I . I0 |]
fromFieldFun ns t@(AppT f a) = [| D . fmap $(fromFieldFun ns a) |]
fromFieldFun ns t            = [| K |]

toField :: [Name] -> Int -> Type -> Q Exp
toField ns nr t = [| $(toFieldFun ns t) $(varE (field nr)) |]

toFieldFun :: [Name] -> Type -> Q Exp
toFieldFun ns t@(ConT n)
  | remakeName n `elem` ns = [| unI0 . unI |]
toFieldFun ns t
  | ConT n : a <- unApp t, remakeName n `elem` ns
                           = [| unI0 . unI |]
toFieldFun ns t@(AppT f a) = [| fmap $(toFieldFun ns a) . unD |]
toFieldFun ns t            = [| unK |]

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

-- Should we, under certain circumstances, maintain the module name?
remakeName :: Name -> Name
remakeName n = mkName (nameBase n)
