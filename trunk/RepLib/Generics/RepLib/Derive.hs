{-# LANGUAGE TemplateHaskell
           , UndecidableInstances
           , TypeOperators
           , ScopedTypeVariables
  #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib.Derive
-- License     :  TBD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Automatically derive representations and instance declarations
-- for user defined datatypes.
-- The typical use is
-- @
--     $(derive [''MyType1, ''MyType2])
-- @
--
-----------------------------------------------------------------------------


module Generics.RepLib.Derive (
	derive, derive_abstract
) where

import Generics.RepLib.R
import Generics.RepLib.R1
import Language.Haskell.TH
import Data.List (foldl')
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Data.Type.Equality

import Control.Monad (replicateM, zipWithM)
import Control.Arrow ((***), second)
import Control.Applicative ((<$>))

-- | Given a type, produce its representation.
repty :: Type -> Exp
repty ty = SigE (VarE (mkName "rep")) ((ConT ''R) `AppT` ty)

rName :: Name -> Name
rName n =
 case nameBase n of
    "(,,,,,,)" -> mkName ("rTup7")
    "(,,,,,)" -> mkName ("rTup6")
    "(,,,,)" -> mkName ("rTup5")
    "(,,,)" -> mkName ("rTup4")
    "(,,)" -> mkName ("rTup3")
    "(,)" -> mkName ("rTup2")
    c      -> mkName ("r" ++ c)

rName1 :: Name -> Name
rName1 n =
 case nameBase n of
    "(,,,,,,)" -> mkName ("rTup7_1")
    "(,,,,,)" -> mkName ("rTup6_1")
    "(,,,,)" -> mkName ("rTup5_1")
    "(,,,)" -> mkName ("rTup4_1")
    "(,,)" -> mkName ("rTup3_1")
    "(,)" -> mkName ("rTup2_1")
    c      -> mkName ("r" ++ c ++ "1")

-------------------------------------------------------------------------------------------------------
-- Generate the representation for a data constructor.
-- As our representation of data constructors evolves, so must this definition.
--    Currently, we don't handle data constructors with record components.

-- | Generate an R-type constructor representation.
repcon :: TypeInfo ->     -- information about the type
          ConstrInfo ->   -- information about the constructor
          Q Exp
repcon info constr
  | null (constrCxt constr) = [| Just $con |]
  | otherwise               = gadtCase (typeParams info) constr con
  where args = map (return . repty . fieldType) . constrFields $ constr
        mtup = foldr (\ t tl -> [| $(t) :+: $(tl) |]) [| MNil |] args
        con  = [| Con $(remb constr) $(mtup) |]

gadtCase :: [TyVarBndr] -> ConstrInfo -> Q Exp -> Q Exp
gadtCase tyVars constr conQ = do
  con      <- [| Just $conQ |]
  (m, pat) <- typeRefinements tyVars constr
  n        <- [| Nothing |]
  return $ CaseE m
    [ Match pat (NormalB con) []
    , Match WildP (NormalB n) []
    ]

      -- have to do the above in this long annoying explicit way
      -- because splicing patterns is not supported.

typeRefinements :: [TyVarBndr] -> ConstrInfo -> Q (Exp, Pat)
typeRefinements tyVars constr =
      fmap ((TupE *** TupP) . unzip)
    . sequence
    . map genRefinement
    . extractParamEqualities tyVars
    $ constrCxt constr

extractParamEqualities :: [TyVarBndr] -> Cxt -> [(Name, Type)]
extractParamEqualities tyVars = filterWith extractLHSVars
                              . filterWith extractEq
  where extractEq :: Pred -> Maybe (Type, Type)
        extractEq (EqualP ty1 ty2)  = Just (ty1, ty2)
        extractEq _                 = Nothing

        extractLHSVars (VarT n, t2) | any ((==n) . tyVarBndrName) tyVars = Just (n,t2)
        extractLHSVars _            = Nothing
        -- Note, assuming here that equalities involving type parameters
        -- will always have the type parameter on the LHS...

        filterWith :: (a -> Maybe b) -> [a] -> [b]
        filterWith f = catMaybes . map f

genRefinement :: (Name, Type) -> Q (Exp, Pat)
genRefinement (n, ty) = do
  let (con, args) = decomposeTy ty
  case args of
    [] -> do e <- [| eqT (rep :: R $(varT n)) $(return $ repty ty) |]
             p <- [p| Just Refl |]
             return (e,p)
    _  -> do e <- [| $(varE (mkName $ "destr" ++ show (length args)))
                     (rep :: R $(varT n))
                     (rep :: R $(appUnits con (length args)))
                  |]
             p <- conP (mkName $ "Result" ++ show (length args))
                       [sigP [p| Refl |] [t| $(varT n) :=: $(return ty) |] ]
             return (e,p)

-- | Decompose a type into a constructor and a list of arguments.
decomposeTy :: Type -> (Type, [Type])
decomposeTy (AppT t1 t2) = second (++[t2]) (decomposeTy t1)
decomposeTy t = (t, [])

-- | Apply a type constructor to a certain number of copies of the
-- unit type.
appUnits :: Type -> Int -> Q Type
appUnits ty n = do
  u <- [t| () |]
  return $ foldl' AppT ty (replicate n u)

-- the "from" function that coerces from an "a" to the arguments
rfrom :: ConstrInfo -> Q Exp
rfrom constr = do
  vars <- mapM (const (newName "x")) (constrFields constr)
  outvar <- newName "y"
  let nm = (simpleName . constrName $ constr)
  let outpat :: Pat
      outpat = ConP nm (map VarP vars)
      outbod :: Exp
      outbod = foldr (\v tl -> (ConE (mkName (":*:"))) `AppE` (VarE v) `AppE` tl)
               (ConE 'Nil) vars
      success = Match outpat (NormalB ((ConE 'Just) `AppE` outbod)) []
      outcase x = if isOnlyConstr constr
                    then CaseE x [success]
                    else CaseE x
                           [success, Match WildP  (NormalB (ConE 'Nothing)) [] ]
  return (LamE [VarP outvar] (outcase (VarE outvar)))

-- to component of th embedding
rto :: ConstrInfo -> Q Exp
rto constr =
  do vars <- mapM (const (newName "x")) (constrFields constr)
     let topat = foldr (\v tl -> InfixP  (VarP v) (mkName ":*:") tl)
                         (ConP 'Nil []) vars
         tobod = foldl' (\tl v -> tl `AppE` (VarE v))
                       (ConE (simpleName . constrName $ constr))
                       vars
     return (LamE [topat] tobod)

-- the embedding record
remb :: ConstrInfo -> Q Exp
remb constr =
    [| Emb  { name   = $(stringName . simpleName . constrName $ constr),
              to     = $(rto constr),
              from   = $(rfrom constr),
              labels = Nothing,
              fixity = Nonfix } |]

repDT :: Name -> [Name] -> Q Exp
repDT nm param =
      do str <- stringName nm
         let reps = foldr (\p f ->
                             (ConE (mkName ":+:")) `AppE`
                             repty (VarT p) `AppE`
                             f)
                          (ConE 'MNil) param
         [| DT $(return str) $(return reps) |]

data Flag = Abs | Conc

-- Create an "R" representation for a given type constructor

repr :: Flag -> Name -> Q [Dec]
repr f n = do info' <- reify n
              case info' of
               TyConI d -> do
                  let dInfo      = typeInfo d
                      paramNames = map tyVarBndrName (typeParams dInfo)
                      nm         = typeName dInfo
                      constrs    = typeConstrs dInfo
                  baseT <- conT nm
                  -- the type that we are defining, applied to its parameters.
                  let ty = foldl' (\x p -> x `AppT` (VarT p)) baseT paramNames
                  -- the representations of the paramters, as a list
                  -- representations of the data constructors
                  rcons <- mapM (repcon dInfo) constrs
                  body  <- case f of
                     Conc -> [| Data $(repDT nm paramNames)
                                     (catMaybes $(return (ListE rcons))) |]
                     Abs  -> [| Abstract $(repDT nm paramNames) |]
                  let ctx = map (\p -> ClassP (mkName "Rep") [VarT p]) paramNames
                  let rTypeName :: Name
                      rTypeName = rName n
                      rSig :: Dec
                      rSig = SigD rTypeName (ForallT (map PlainTV paramNames)
                                                     ctx ((ConT (mkName "R"))
         	                                          `AppT` ty))
                      rType :: Dec
                      rType = ValD (VarP rTypeName) (NormalB body) []
                  let inst  = InstanceD ctx ((ConT (mkName "Rep")) `AppT` ty)
                                 [ValD (VarP (mkName "rep")) (NormalB (VarE rTypeName)) []]

                  return [rSig, rType, inst]

reprs :: Flag -> [Name] -> Q [Dec]
reprs f ns = concat <$> mapM (repr f) ns

--------------------------------------------------------------------------------------------
--- Generating the R1 representation

-- The difficult part of repr1 is that we need to paramerize over reps for types that
-- appear as arguments of constructors, as well as the reps of parameters.

-- The constructor for the R1 representation takes one argument
-- corresponding to each constructor, providing contexts for the
-- arguments to that constructor.  Some of them are just (tuples of)
-- applications of ctx to some type.  However, for GADT constructors,
-- the argument is a polymorphic function which takes an equality
-- proof (in order to refine one or more type parameters) and then
-- returns some contexts.  For example, for
--
-- data Foo a where
--   Bar  :: Int -> Foo Int
--   Bar2 :: Foo b -> Foo [b]
--   Bar3 :: Foo c -> Foo d -> Foo (c,d)
--
-- we have
--
-- rFoo1 ::
-- forall ctx a. Rep a =>
-- ctx Int ->
-- (forall b. a :=: [b] -> ctx (Foo b)) ->
-- (forall c d. a :=: (c,d) -> (ctx (Foo c), ctx (Foo d))) ->
-- R1 ctx (Foo a)

data CtxParam = CtxParam { cpName    :: Name            -- The argument name
                         , cpType    :: Type            -- The argument type
                         , cpEqs     :: [(Name, Type)]  -- Required equality proofs
                         , cpPayload :: Type            -- What you get after supplying
                                                        -- the proofs
                         }

-- | Generate the context parameters (see above) for a given type.
ctx_params :: TypeInfo ->      -- information about the type we are defining
              Name ->          -- name of the type variable "ctx"
              [ConstrInfo] ->  -- information about the type's constructors
            Q [CtxParam]
ctx_params tyInfo ctxName constrs = mapM (genCtxParam ctxName tyInfo) constrs

-- | Generate a context parameter for a single constructor.
genCtxParam :: Name -> TypeInfo -> ConstrInfo -> Q CtxParam
genCtxParam ctxName tyInfo constr = newName "c" >>= \c -> return (CtxParam c pType eqs payload)
  where allEqs = extractParamEqualities (typeParams tyInfo) (constrCxt constr)
        eqs    = filter (not . S.null . tyFV . snd) allEqs
        pType | null eqs  = payload
              | otherwise = guarded
        payload = mkTupleT . map ((VarT ctxName `AppT`) . fieldType) . constrFields $ constr
        guarded = ForallT vars [] (foldr (AppT . AppT ArrowT) payload proofs)
        vars    = map PlainTV $ concatMap (S.toList . tyFV . snd) eqs
        proofs  = map mkProof eqs
        mkProof (n, ty) = AppT (AppT (ConT (mkName ":=:")) (VarT n)) ty

mkTupleT :: [Type] -> Type
mkTupleT tys = foldl' AppT (TupleT (length tys)) tys

-- | Compute the free type variables of a type.
tyFV :: Type -> S.Set Name
tyFV (ForallT vs _ ty) = tyFV ty `S.difference` (S.fromList . map tyVarBndrName $ vs)
tyFV (VarT n)          = S.singleton n
tyFV (ConT _)          = S.empty
tyFV (TupleT _)        = S.empty
tyFV ArrowT            = S.empty
tyFV ListT             = S.empty
tyFV (AppT ty1 ty2)    = tyFV ty1 `S.union` tyFV ty2
tyFV (SigT ty _)       = tyFV ty

repcon1 :: TypeInfo            -- information about the type
        -> CtxParam            -- corresponding context parameter
        -> ConstrInfo          -- info about the constructor
        -> Q Exp
repcon1 info ctxParam constr = do
  cs      <- replicateM (length . constrFields $ constr) (newName "c")
  let conBody = caseE (applyPfs ctxParam)
                [ match (tupP . map varP $ cs) (normalB con) [] ]
      args    = map varE cs
      mtup    = foldr (\ t tl -> [| $(t) :+: $(tl) |]) [| MNil |] args
      con     = [| Con $(remb constr) $(mtup) |]
  case (null (constrCxt constr)) of
    True -> [| Just $con |]
    _    -> gadtCase (typeParams info) constr conBody

-- | Apply a context parameter to the right number of equality proofs
--   to get out the promised context.
applyPfs :: CtxParam -> Q Exp
applyPfs (CtxParam { cpName = n, cpEqs = eqs }) =
  appsE (varE n : replicate (length eqs) [| Refl |])

-- Generate a parameterized representation of a type
repr1 :: Flag -> Name -> Q [Dec]
repr1 f n = do info' <- reify n
               case info' of
                TyConI d -> do
                  let dInfo      = typeInfo d
                      paramNames = map tyVarBndrName (typeParams dInfo)
                      nm         = typeName dInfo
                      constrs    = typeConstrs dInfo
                  -- the type that we are defining, applied to its parameters.
                  let ty = foldl' (\x p -> x `AppT` (VarT p)) (ConT nm) paramNames
                  let rTypeName = rName1 n

                  ctx <- newName "ctx"
                  ctxParams <- case f of
                                    Conc -> ctx_params dInfo ctx constrs
                                    Abs  -> return []

                  r1Ty <- [t| $(conT $ mkName "R1") $(varT ctx) $(return ty) |]
                  let ctxRep = map (\p -> ClassP (mkName "Rep") [VarT p]) paramNames
                      rSig = SigD rTypeName
                               (ForallT
                                 (map PlainTV (ctx : paramNames))
                                 ctxRep
                                 (foldr (AppT . AppT ArrowT) r1Ty (map cpType ctxParams))
                               )

                  rcons <- zipWithM (repcon1 dInfo) ctxParams constrs
                  body  <- case f of
                             Conc -> [| Data1 $(repDT nm paramNames)
                                              (catMaybes $(return (ListE rcons))) |]
                             Abs  -> [| Abstract1 $(repDT nm paramNames) |]

                  let rhs = LamE (map (VarP . cpName) ctxParams) body

                      rDecl = ValD (VarP rTypeName) (NormalB rhs) []

                  decs <- repr f n
                  return (decs ++ [rSig, rDecl {- , inst -} ])

{-
                  -- the recursive call of the rep function
                  let e1 = foldl' (\a r -> a `AppE` (VarE r)) (VarE rTypeName) paramNames
                  let e2 = foldl' (\a (x,_,_) -> a `AppE` (VarE x)) e1 ctxParams


                  let ctxRep = map (\p -> ClassP (mkName "Rep") [VarT p]) paramNames
                      ctxRec = map (\(_,t,_) -> ClassP ''Sat [t]) ctxParams

                      -- appRep t = foldl' (\a p -> a `AppE` (VarE 'rep)) t param
                      appRec t = foldl' (\a _ -> a `AppE` (VarE 'dict)) t ctxParams

                  let inst  = InstanceD (ctxRep ++ ctxRec)
                                ((ConT ''Rep1) `AppT` (VarT ctx) `AppT` ty)
                                [ValD (VarP (mkName "rep1"))
                                  (NormalB (appRec (VarE rTypeName))) []]
-}


repr1s :: Flag -> [Name] -> Q [Dec]
repr1s f ns = concat <$> mapM (repr1 f) ns

-- | Generate representations (both basic and parameterized) for a list of
-- types.
derive :: [Name] -> Q [Dec]
derive = repr1s Conc

-- | Generate abstract representations for a list of types.
derive_abstract :: [Name] -> Q [Dec]
derive_abstract = repr1s Abs

--------------------------------------------------------------------------------------



--- Helper functions

stringName :: Name -> Q Exp
stringName n = return (LitE (StringL (nameBase n)))

data TypeInfo = TypeInfo { typeName    :: Name
                         , typeParams  :: [TyVarBndr]
                         , typeConstrs :: [ConstrInfo]
                         }

data ConstrInfo = ConstrInfo { constrName    :: Name   -- careful, this is NOT
                                                       -- simplified; may need to
                                                       -- call simpleName first
                             , constrBinders :: [TyVarBndr]
                             , constrCxt     :: Cxt
                             , constrFields  :: [FieldInfo]
                             , isOnlyConstr  :: Bool  -- is this the only
                                                      -- constructor of its type?
                             }

mkConstr :: Name -> ConstrInfo
mkConstr nm = ConstrInfo nm [] [] [] False

data FieldInfo = FieldInfo { fieldName :: Maybe Name
                           , fieldType :: Type
                           }

typeInfo :: Dec -> TypeInfo
typeInfo d = case d of
    (DataD _ _ _ _ _) ->
      TypeInfo (getName d) (paramsA d) (consA d)
    (NewtypeD _ _ _ _ _) ->
      TypeInfo (getName d) (paramsA d) (consA d)
    _ -> error ("derive: not a data type declaration: " ++ show d)

  where
    getName (DataD _ n _ _ _)     = n
    getName (NewtypeD _ n _ _ _)  = n
    getName x                     = error $ "Impossible! " ++ show x ++ " is neither data nor newtype"

    paramsA (DataD _ _ ps _ _)    = ps
    paramsA (NewtypeD _ _ ps _ _) = ps

    consA (DataD _ _ _ cs _)      = rememberOnly $ map conA cs
    consA (NewtypeD _ _ _ c _)    = rememberOnly $ [ conA c ]

    conA (NormalC c xs)           = (mkConstr c)
                                      { constrFields  = map normalField xs }

    conA (RecC c xs)              = (mkConstr c)
                                      { constrFields  = map recField xs }

    conA (InfixC t1 c t2)         = (mkConstr c)
                                      { constrFields  = map normalField [t1, t2] }

    conA (ForallC bdrs cx con)    = let c' = conA con
                                    in  c' { constrBinders = bdrs ++ constrBinders c'
                                           , constrCxt = cx ++ constrCxt c'
                                           }

    normalField x                 = FieldInfo
                                    { fieldName = Nothing
                                    , fieldType = snd x
                                    }
    recField (n, _, t)            = FieldInfo
                                    { fieldName = Just $ simpleName n
                                    , fieldType = t
                                    }

rememberOnly :: [ConstrInfo] -> [ConstrInfo]
rememberOnly [con] = [con { isOnlyConstr = True }]
rememberOnly cons  = cons

simpleName :: Name -> Name
simpleName nm =
   let s = nameBase nm
   in case dropWhile (/=':') s of
        []          -> mkName s
        _:[]        -> mkName s
        _:t         -> mkName t

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n
