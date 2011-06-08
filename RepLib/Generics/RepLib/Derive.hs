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
import Data.List (nub, foldl')
import Data.Maybe (catMaybes)
import Data.Type.Equality

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

repcon :: Type ->  -- The type that this is a constructor for (applied to all of its parameters)
          TypeInfo ->    -- information about the type
          ConstrInfo ->  -- information about the contstructor
	  Q Exp
repcon d info constr
  | null (constrCxt constr) = [| Just $con |]
  | otherwise               = gadtCase (typeParams info) constr con
  where rargs = foldr (\ t tl -> [| $(return $ repty t) :+: $(tl) |])
                      [| MNil |]
                      (map fieldType . constrFields $ constr)
        con   = [| Con $(remb d constr) $(rargs) |]

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
      -- because I don't know how to splice in a pattern =(

      -- this fails with an error:

      -- [| case $(matcher constr) of
      --     $(successCase constr) ->
      --     _                     -> Nothing }
      -- |]

      -- Generics/RepLib/Derive.hs:78:7:
      --    Parse error in pattern: $(successCase constr)

typeRefinements :: [TyVarBndr] -> ConstrInfo -> Q (Exp, Pat)
typeRefinements tyVars constr =
      fmap ((TupE *** TupP) . unzip)
    . sequence
    . map genRefinement
    . catMaybes . map extractLHSVars
    . catMaybes . map extractEq
    $ constrCxt constr
  where extractEq (EqualP ty1 ty2)  = Just (ty1, ty2)
        extractEq _                 = Nothing

        extractLHSVars (VarT n, t2) | any ((==n) . tyVarBndrName) tyVars = Just (n,t2)
        extractLHSVars _            = Nothing
        -- Note, assuming here that equalities involving type parameters
        -- will always have the type parameter on the LHS...

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
rfrom :: Type -> ConstrInfo -> Q Exp
rfrom _ constr = do
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
rto :: Type -> ConstrInfo -> Q Exp
rto _ constr =
  do vars <- mapM (const (newName "x")) (constrFields constr)
     let topat = foldr (\v tl -> InfixP  (VarP v) (mkName ":*:") tl)
                         (ConP 'Nil []) vars
         tobod = foldl' (\tl v -> tl `AppE` (VarE v))
                       (ConE (simpleName . constrName $ constr))
                       vars
     return (LamE [topat] tobod)

-- the embedding record
remb :: Type -> ConstrInfo -> Q Exp
remb d constr =
    [| Emb  { name   = $(stringName . simpleName . constrName $ constr),
              to     = $(rto d constr),
              from   = $(rfrom d constr),
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
                  rcons <- mapM (repcon ty dInfo) constrs
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

ctx_params :: Type ->    -- type we are defining
              Name ->    -- name of the type variable "ctx"
              [ConstrInfo] ->
            Q [(Name, Type, Type)]
				-- name of termvariable "pt"
            -- (ctx t)
            -- t
ctx_params _ty ctxName constrs = do
   let tys = nub . map fieldType . concatMap constrFields $ constrs
   mapM (\t -> do n <- newName "p"
                  let ctx_t = (VarT ctxName) `AppT` t
                  return (n, ctx_t, t)) tys

lookupName :: Type -> [(Name, Type, Type)] -> [(Name, Type, Type)] ->  Name
lookupName t l ((n, _t1, t2):rest) = if t == t2 then n else lookupName t l rest
lookupName t l [] = error ("lookupName: Cannot find type " ++ show t ++ " in " ++ show l)

repcon1 :: Type                               -- result type of the constructor
          -> Exp                              -- recursive call (rList1 ra pa)
          -> [(Name,Type,Type)]               -- ctxParams
          -> ConstrInfo
          -> Q Exp
repcon1 d rd1 ctxParams constr =
       let rec = foldr (\ ty tl ->
                         let expQ = (VarE (lookupName ty ctxParams ctxParams))
                         in [| $(return expQ) :+: $(tl) |])
                       [| MNil |]
                       (map fieldType . constrFields $ constr)
       in  [| Con $(remb d constr) $(rec) |]

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
                                    Conc -> ctx_params ty ctx constrs
                                    Abs  -> return []

                  -- parameters to the rep function
                  -- let rparams = map (\p -> SigP (VarP p) ((ConT ''R) `AppT` (VarT p))) param
                  let cparams = map (\(x,t,_) -> SigP (VarP x) t) ctxParams

                  -- the recursive call of the rep function
                  let e1 = foldl' (\a r -> a `AppE` (VarE r)) (VarE rTypeName) paramNames
                  let e2 = foldl' (\a (x,_,_) -> a `AppE` (VarE x)) e1 ctxParams

                  -- the representations of the parameters, as a list
                  -- representations of the data constructors
                  rcons <- mapM (repcon1 ty e2 ctxParams) constrs
                  body  <- case f of
                            Conc -> [| Data1 $(repDT nm paramNames)
                                           $(return (ListE rcons)) |]
                            Abs  -> [| Abstract1 $(repDT nm paramNames) |]

                  let rhs = LamE (cparams) body
{-                    rhs_type = ForallT (ctx:param) rparams
                                  (foldr (\ (p,t) ret -> `ArrowT` `AppT` t `AppT` ret) ty params) -}
                      rTypeDecl = ValD (VarP rTypeName) (NormalB rhs) []


                  let ctxRep = map (\p -> ClassP (mkName "Rep") [VarT p]) paramNames
                      ctxRec = map (\(_,t,_) -> ClassP ''Sat [t]) ctxParams

                      -- appRep t = foldl' (\a p -> a `AppE` (VarE 'rep)) t param
                      appRec t = foldl' (\a _ -> a `AppE` (VarE 'dict)) t ctxParams

                  let inst  = InstanceD (ctxRep ++ ctxRec)
                                ((ConT ''Rep1) `AppT` (VarT ctx) `AppT` ty)
                                [ValD (VarP (mkName "rep1"))
                                  (NormalB (appRec (VarE rTypeName))) []]

                  let rSig = SigD rTypeName (ForallT (map PlainTV (ctx : paramNames)) ctxRep
                              (foldr (\(_,p,_) x -> (ArrowT `AppT` p `AppT` x))
                                     ((ConT (mkName "R1")) `AppT` (VarT ctx) `AppT` ty)
                                     ctxParams))
                  decs <- repr f n
                  return (decs ++ [rSig, rTypeDecl, inst])


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
