{-# LANGUAGE TemplateHaskell
           , UndecidableInstances
           , TypeOperators
           , ScopedTypeVariables
           , GADTs
           , GeneralizedNewtypeDeriving
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
import Language.Haskell.TH hiding (Con)
import qualified Language.Haskell.TH as TH (Con)
import Language.Haskell.TH.Syntax (Quasi(..))
import Data.List (foldl', nub)
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Data.Type.Equality

import Control.Monad (replicateM, zipWithM, liftM, liftM2, when)
import Control.Monad.Writer (WriterT, MonadWriter(..), runWriterT, lift)
import Control.Arrow ((***), second)
import Control.Applicative ((<$>))

import Unsafe.Coerce

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

----------------------------------------------------------------------------------

-- Q-like monad which also remembers a Set of Int values.  We use this
-- to keep track of which Res/destr definitions we end up needing
-- while generating constructor representations.

newtype QN a = QN { unQN :: WriterT (S.Set Int) Q a }
  deriving (Functor, Monad, MonadWriter (S.Set Int))

liftQN :: Q a -> QN a
liftQN = QN . lift

runQN :: QN a -> Q (a, S.Set Int)
runQN = runWriterT . unQN

instance Quasi QN where
  qNewName s            = liftQN $ qNewName s
  qReport b s           = liftQN $ qReport b s
  qRecover              = error "qRecover not implemented for QN"
  qReify n              = liftQN $ qReify n
  qClassInstances n tys = liftQN $ qClassInstances n tys
  qLocation             = liftQN qLocation
  qRunIO io             = liftQN $ qRunIO io                       

-- Generate the representation for a data constructor.
-- As our representation of data constructors evolves, so must this definition.
--    Currently, we don't handle data constructors with record components.

-- | Generate an R-type constructor representation.
repcon :: TypeInfo ->     -- information about the type
          ConstrInfo ->   -- information about the constructor
          QN Exp
repcon info constr
  | null (constrCxt constr) = liftQN [| Just $con |]
  | otherwise               = gadtCase (typeParams info) constr con
  where args = map (return . repty . fieldType) . constrFields $ constr
        mtup = foldr (\ t tl -> [| $(t) :+: $(tl) |]) [| MNil |] args
        con  = [| Con $(remb constr) $(mtup) |]

gadtCase :: [TyVarBndr] -> ConstrInfo -> Q Exp -> QN Exp
gadtCase tyVars constr conQ = do
  con      <- liftQN [| Just $conQ |]
  (m, pat) <- typeRefinements tyVars constr
  n        <- liftQN [| Nothing |]
  return $ CaseE m
    [ Match pat (NormalB con) []
    , Match WildP (NormalB n) []
    ]

typeRefinements :: [TyVarBndr] -> ConstrInfo -> QN (Exp, Pat)
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

-- The third result is the arity of the type constructor, hence the N
-- of the required ResN/destrN declarations.
genRefinement :: (Name, Type) -> QN (Exp, Pat)
genRefinement (n, ty) = do
  let (con, args) = decomposeTy ty
  when (not (null args)) $ tell $ S.singleton (length args)
  liftQN $ case args of
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
                  (rcons, ks) <- runQN $ mapM (repcon dInfo) constrs

                  ress <- case f of
                            Conc -> deriveRess ks
                            Abs  -> return []
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

                  return $ ress ++ [rSig, rType, inst]

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
                         , cpTyVars  :: [Name]          -- *All* type variable arguments to the type
                                                        -- (not just ones requiring equality proofs);
                                                        -- needed when generating special Sat classes
                         , cpPayload :: Type            -- What you get after supplying
                                                        -- the proofs
                         , cpPayloadElts :: [Type]      -- individual elements in
                                                        -- the payload
                         , cpCtxName :: Name
                         , cpSat     :: Maybe (Name, Name)
                            -- names of the special Sat-like class and
                            -- its dictionary method for this
                            -- constructor
                         }

-- | Generate the context parameters (see above) for a given type.
ctx_params :: TypeInfo ->      -- information about the type we are defining
              Name ->          -- name of the type variable "ctx"
              [ConstrInfo] ->  -- information about the type's constructors
            Q [CtxParam]
ctx_params tyInfo ctxName constrs = mapM (genCtxParam ctxName tyInfo) constrs

-- | Generate a context parameter for a single constructor.
genCtxParam :: Name -> TypeInfo -> ConstrInfo -> Q CtxParam
genCtxParam ctxName tyInfo constr
    = newName "c" >>= \c -> return (CtxParam c pType eqs tvars payload payloadElts ctxName Nothing)
  where allEqs = extractParamEqualities (typeParams tyInfo) (constrCxt constr)
        eqs    = filter (not . S.null . tyFV . snd) allEqs
        tvars  = map tyVarBndrName . typeParams $ tyInfo
        pType | null eqs  = payload
              | otherwise = guarded
        payloadElts = map ((VarT ctxName `AppT`) . fieldType) . constrFields $ constr
        payload = mkTupleT payloadElts
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
    True -> [| Just $conBody |]
    _    -> fst <$> (runQN $ gadtCase (typeParams info) constr conBody)

-- | Apply a context parameter to the right number of equality proofs
--   to get out the promised context.
applyPfs :: CtxParam -> Q Exp
applyPfs (CtxParam { cpName = n, cpEqs = eqs }) =
  appsE (varE n : replicate (length eqs) [| Refl |])

genSatClass :: CtxParam -> Q (CtxParam, [Dec])
genSatClass ctxParam | null (cpEqs ctxParam) = return (ctxParam, [])
                     | otherwise = do
  satNm  <- newName "Sat"
  dictNm <- newName "dict"

  let ctx = cpCtxName ctxParam
      eqs = cpEqs ctxParam
      tvs = cpTyVars ctxParam
      satClass = ClassD [] satNm (PlainTV ctx : map PlainTV tvs) []
                   [SigD dictNm (cpType ctxParam)]

      satInstHead = foldl' AppT (ConT satNm) (VarT ctx : map tvOrEqType tvs)
      tvOrEqType a = case lookup a eqs of
                       Just t  -> t
                       Nothing -> VarT a

      satInst  = InstanceD
                   (map (ClassP ''Sat . (:[])) (cpPayloadElts ctxParam))
                   satInstHead
                   [ValD (VarP dictNm)
                         (NormalB (LamE (replicate (length eqs) (ConP 'Refl []))
                                        (TupE (replicate (length (cpPayloadElts ctxParam))
                                                         (VarE 'dict)
                                              )
                                        )
                                  )
                         )
                         []
                   ]

  nms <- replicateM (length tvs) (newName "a")
  err <- [| error "Impossible Sat instance!" |]

  let defSatInst = InstanceD [] (foldl' AppT (ConT satNm) (map VarT (ctx : nms)))
                     [ValD (VarP dictNm)
                           (NormalB (LamE (replicate (length eqs) (ConP 'Refl [])) err))
                           []
                     ]

  return (ctxParam { cpSat = Just (satNm, dictNm) }, [satClass, satInst, defSatInst])

genSatClasses :: [CtxParam] -> Q ([CtxParam], [Dec])
genSatClasses ps = (second concat . unzip) <$> mapM genSatClass ps

-- XXX look at Basics.hs -- tree example.  The context for recursive
-- subtrees ends up getting duplicated.  Need to nub out something so
-- that doesn't happen.

-- Generate a parameterized representation of a type
repr1 :: Flag -> Name -> Q [Dec]
repr1 f n = do
  info' <- reify n
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

     r1Ty <- [t| $(conT $ ''R1) $(varT ctx) $(return ty) |]
     let ctxRep = map (\p -> ClassP (''Rep) [VarT p]) paramNames
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

     -- generate a Sat-like class for each constructor requiring
     -- equality proofs
     (ctxParams', satClasses) <- genSatClasses ctxParams
     let mkCtxRec c = case cpSat c of
                        Nothing    -> map (ClassP ''Sat . (:[])) (cpPayloadElts c)
                        Just (s,_) -> [ClassP s (map VarT (cpCtxName c : paramNames))]
         ctxRec = nub $ concatMap mkCtxRec ctxParams'
         mkDictArg c = case cpSat c of
                         Just (_,dn) -> VarE dn
                         Nothing     -> TupE (replicate (length (cpPayloadElts c)) (VarE 'dict))
         dicts  = map mkDictArg ctxParams'

     inst <- instanceD (return $ ctxRep ++ ctxRec)
                       (conT ''Rep1 `appT` varT ctx `appT` (return ty))
                       [valD (varP 'rep1) (normalB (appsE (varE rTypeName
                                                           : map return dicts))) []]

     -- generate the Rep instances as well
     decs <- repr f n
     return (decs ++ [rSig, rDecl] ++ satClasses ++ [inst])

repr1s :: Flag -> [Name] -> Q [Dec]
repr1s f ns = concat <$> mapM (repr1 f) ns

-- | Generate representations (both basic and parameterized) for a list of
--   types.
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


----------------------------------------------------------------
--  Generating ResN types with associated destructor functions
----------------------------------------------------------------

{- Derive declarations of the form

data Res2 c2 a where
  Result2   :: (Rep d, Rep e) => a :=: (c2 d e) -> Res2 c2 a
  NoResult2 :: Res2 c2 a

destr2 :: R a -> R (c2 d e) -> Res2 c2 a
destr2 (Data (DT s1 ((rd :: R d) :+: (re :: R e) :+: MNil)) _)
       (Data (DT s2 _) _)
  | s1 == s2  = Result2 (unsafeCoerce Refl :: a :=: (c2 d e))
  | otherwise = NoResult2
destr2 _ _ = NoResult2

   for taking apart applications of type constructors of arity n.
-}

deriveRess :: S.Set Int -> Q [Dec]
deriveRess = S.fold (liftM2 (++) . deriveResMaybe) (return [])

deriveResMaybe :: Int -> Q [Dec]
deriveResMaybe n = recover 
                     (deriveRes n) 
                     (reify (mkName $ "Res" ++ show n) >> return [])

deriveRes :: Int -> Q [Dec]
deriveRes n | n < 0 = error "deriveRes should only be called with positive arguments"
deriveRes n = do
  c  <- newName "c"
  a  <- newName "a"
  bs <- replicateM n (newName "b")
  liftM (deriveResData n c a bs:) (deriveResDestr n c a bs)

deriveResData :: Int -> Name -> Name -> [Name] -> Dec
deriveResData n c a bs =
  DataD [] (mkName $ "Res" ++ show n) (map PlainTV [c,a])
        [deriveResultCon n c a bs, deriveNoResultCon n] []

deriveResultCon :: Int -> Name -> Name -> [Name] -> TH.Con
deriveResultCon n c a bs =
    ForallC
      (map PlainTV bs)
      (map (ClassP ''Rep . (:[]) . VarT) bs)
      (NormalC (mkName $ "Result" ++ show n)
        [(NotStrict, deriveResultEq c a bs)]
      )

deriveResultEq :: Name     -- Tyvar representing the type to be deconstructed
               -> Name     -- Constructor tyvar
               -> [Name]   -- Argument tyvars
               -> Type
deriveResultEq c a bs = AppT (AppT (ConT (mkName ":=:")) (VarT a))
                             (appsT (VarT c) bs)

deriveNoResultCon :: Int -> TH.Con
deriveNoResultCon n = NormalC (mkName $ "NoResult" ++ show n) []

deriveResDestr :: Int -> Name -> Name -> [Name] -> Q [Dec]
deriveResDestr n c a bs = do
  let sig = deriveResDestrSig n c a bs
  decl <- deriveResDestrDecl n c a (length bs)
  return [sig, decl]

deriveResDestrSig :: Int -> Name -> Name -> [Name] -> Dec
deriveResDestrSig n c a bs =
  SigD (mkName $ "destr" ++ show n)
       (ForallT (map PlainTV $ [c,a] ++ bs) []
         ( (AppT (ConT ''R) (VarT a)) `arr`
           (AppT (ConT ''R) (appsT (VarT c) bs)) `arr`
           (AppT (AppT (ConT (mkName $ "Res" ++ show n)) (VarT c)) (VarT a))
         )
       )

deriveResDestrDecl :: Int -> Name -> Name -> Int -> Q Dec
deriveResDestrDecl n c a bNum = do
  [s1, s2] <- replicateM 2 (newName "s")
  bs <- replicateM bNum (newName "b")
  return $
    FunD
      (mkName $ "destr" ++ show n)
      [ Clause
          [ deriveResDestrLPat s1 bs
          , deriveResDestrRPat s2
          ]
          (GuardedB
             [ ( NormalG (AppE (AppE (VarE '(==)) (VarE s1)) (VarE s2))
               , AppE (ConE (mkName $ "Result" ++ show n))
                      (SigE (AppE (VarE 'unsafeCoerce) (ConE 'Refl))
                            (deriveResultEq c a bs)
                      )
               )
             , ( NormalG (VarE 'otherwise)
               , ConE (mkName $ "NoResult" ++ show n)
               )
             ]
          )
          []
      , Clause
          [ WildP, WildP ]
          (NormalB (ConE (mkName $ "NoResult" ++ show n)))
          []
      ]

-- (Data (DT s1 ((_ :: R b1') :+: (_ :: R b2') :+: MNil)) _)
deriveResDestrLPat :: Name -> [Name] -> Pat
deriveResDestrLPat s1 bs = 
  ConP 'Data
  [ ConP 'DT
    [ VarP s1
    , foldr (\p l -> InfixP p '(:+:) l) (ConP 'MNil [])
            (map (SigP WildP . AppT (ConT ''R) . VarT) bs)
    ]
  , WildP
  ]

-- (Data (DT s2 _) _)
deriveResDestrRPat :: Name -> Pat
deriveResDestrRPat s2 = 
  ConP 'Data
  [ ConP 'DT [ VarP s2, WildP ]
  , WildP
  ]

infixr 5 `arr`
arr :: Type -> Type -> Type
arr t1 t2 = AppT (AppT ArrowT t1) t2

appsT :: Type -> [Name] -> Type
appsT t []     = t
appsT t (n:ns) = appsT (AppT t (VarT n)) ns

