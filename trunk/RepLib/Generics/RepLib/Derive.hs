-- OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances -ddump-splices --

{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Derive
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
import Data.List (nub)

-- | Given a type, produce its representation.

-- Note, that the representation of a type variable "a" is (rep :: R a) so Rep a must be
-- in the context
repty :: Type -> Q Exp
repty (ForallT _ _ _) = error "cannot rep"
repty (VarT n) = return (SigE (VarE (mkName "rep")) ((ConT ''R) `AppT` (VarT n)))
repty (AppT t1 _t2) = (repty t1) -- `AppE` (repty t2)
repty (ConT n) = do
  info <- reify n
  case info of
    TyConI (TySynD _n' _vars t) -> repty t
    _ ->
     return $
      case nameBase n of
       "Int"     -> (ConE 'Int)
       "Char"    -> (ConE 'Char)
       "Float"   -> (ConE 'Float)
       "Double"  -> (ConE 'Double)
       "Rational"-> (ConE 'Rational)
       "Integer" -> (ConE 'Integer)
       "IOError" -> (ConE 'IOError)
       "IO"      -> (ConE 'IO)
       "[]"      -> (VarE 'rList)  --- don't know why this isn't ListT
       "String"  -> (VarE 'rList)
       _         -> (VarE (rName n))
repty (TupleT i)
  | i <= 7    = return $ VarE (mkName $ "rTup" ++ show i)
  | otherwise = error $ "Why on earth are you using " ++ (show i) ++ "-tuples??"

repty (ArrowT)   = return (ConE 'Arrow)
repty (ListT)    = return (VarE 'rList)


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
-- represent a data constructor.
-- As our representation of data constructors evolves, so must this definition.
--    Currently, we don't handle data constructors with record components

repcon :: Bool ->  -- Is this the ONLY constructor for the datatype
          Type ->  -- The type that this is a constructor for (applied to all of its parameters)
          (Name, [(Maybe Name, Type)]) ->  -- data constructor name * list of [record name * type]
	  Q Exp
repcon single d (nm, sttys) =
	 let rargs = foldr (\ (_,t) tl ->
		 [| $(repty t) :+: $(tl) |]) [| MNil |] sttys in
		 [| Con $(remb single d (nm,sttys)) $(rargs) |]

-- the "from" function that coerces from an "a" to the arguments
rfrom :: Bool ->  -- does this datatype have only a single constructor
          Type ->  -- the datatype itself
          (Name, [(Maybe Name, Type)]) ->  -- data constructor name, list of parameters with record names
          Q Exp
rfrom single _ (nm, sttys) = do
       vars <- mapM (\_ -> newName "x") sttys
       outvar <- newName "y"
       let outpat :: Pat
           outpat = ConP nm (map VarP vars)
           outbod :: Exp
           outbod = foldr (\v tl -> (ConE (mkName (":*:"))) `AppE` (VarE v) `AppE` tl)
                    (ConE 'Nil) vars
           success = Match outpat (NormalB ((ConE 'Just) `AppE` outbod)) []
           outcase x = if single then
							  CaseE x [success]
							  else
							  CaseE x
                       [success, Match WildP  (NormalB (ConE 'Nothing)) [] ]
       return (LamE [VarP outvar] (outcase (VarE outvar)))

-- to component of th embedding
rto :: Type -> (Name, [(Maybe Name, Type)]) -> Q Exp
rto _ (nm,sttys) =
  do vars <- mapM (\_ -> newName "x") sttys
     let topat = foldr (\v tl -> InfixP  (VarP v) (mkName ":*:") tl)
                         (ConP 'Nil []) vars
         tobod = foldl (\tl v -> tl `AppE` (VarE v)) (ConE nm) vars
     return (LamE [topat] tobod)

-- the embedding record
remb :: Bool -> Type -> (Name, [(Maybe Name, Type)]) -> Q Exp
remb single d (nm, sttys) =
    [| Emb  { name   = $(stringName nm),
              to     = $(rto d (nm,sttys)),
              from   = $(rfrom single d (nm,sttys)),
              labels = Nothing,
              fixity = Nonfix } |]

repDT :: Name -> [Name] -> Q Exp
repDT nm param =
      do str <- stringName nm
         let reps = foldr (\p f ->
									  (ConE (mkName ":+:")) `AppE`
									     (SigE (VarE (mkName "rep"))
											((ConT ''R) `AppT` (VarT p)))  `AppE` f)
						  (ConE 'MNil) param
         [| DT $(return str) $(return reps) |]

data Flag = Abs | Conc

-- Create an "R" representation for a given type constructor

repr :: Flag -> Name -> Q [Dec]
repr f n = do info' <- reify n
              case info' of
               TyConI d -> do
                  (nm, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
                  let paramNames = map tyVarBndrName param
                  baseT <- conT nm
                  -- the type that we are defining, applied to its parameters.
                  let ty = foldl (\x p -> x `AppT` (VarT p)) baseT paramNames
                  -- the representations of the paramters, as a list
                  -- representations of the data constructors
                  rcons <- mapM (repcon (length terms == 1) ty) terms
                  body  <- case f of
                     Conc -> [| Data $(repDT nm paramNames) $(return (ListE rcons)) |]
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
reprs f ns = foldl (\qd n -> do decs1 <- repr f n
                                decs2 <- qd
                                return (decs1 ++ decs2)) (return []) ns

--------------------------------------------------------------------------------------------
--- Generating the R1 representation

-- The difficult part of repr1 is that we need to paramerize over recs for types that
-- appear in the constructors, as well as the reps of parameters.

ctx_params :: Type ->    -- type we are defining
              Name ->    -- name of the type variable "ctx"
				  [(Name, [(Maybe Name, Type)])] -> -- list of constructor names
				                                    -- and the types of their arguments (plus record labels)
            Q [(Name, Type, Type)]
				-- name of termvariable "pt"
            -- (ctx t)
            -- t
ctx_params _ty ctxName l = do
   let tys = nub (map snd (foldr (++) [] (map snd l)))
   mapM (\t -> do n <- newName "p"
                  let ctx_t = (VarT ctxName) `AppT` t
                  return (n, ctx_t, t)) tys

lookupName :: Type -> [(Name, Type, Type)] -> [(Name, Type, Type)] ->  Name
lookupName t l ((n, _t1, t2):rest) = if t == t2 then n else lookupName t l rest
lookupName t l [] = error ("lookupName: Cannot find type " ++ show t ++ " in " ++ show l)

repcon1 :: Type                               -- result type of the constructor
          -> Bool
          -> Exp                              -- recursive call (rList1 ra pa)
          -> [(Name,Type,Type)]               -- ctxParams
          -> (Name, [(Maybe Name, Type)])     -- name of data constructor + args
          -> Q Exp
repcon1 d single rd1 ctxParams (nm, sttys) =
       let rec = foldr (\ (_,t) tl ->
                    let expQ = (VarE (lookupName t ctxParams ctxParams))
                    in [| $(return expQ) :+: $(tl) |]) [| MNil |] sttys in
       [| Con $(remb single d (nm,sttys)) $(rec) |]

-- Generate a parameterized representation of a type
repr1 :: Flag -> Name -> Q [Dec]
repr1 f n = do info' <- reify n
               case info' of
                TyConI d -> do
                  (nm, param, _, terms) <- typeInfo ((return d) :: Q Dec)
                  let paramNames = map tyVarBndrName param
                  -- the type that we are defining, applied to its parameters.
                  let ty = foldl (\x p -> x `AppT` (VarT p)) (ConT nm) paramNames
                  let rTypeName = rName1 n

                  ctx <- newName "ctx"
                  ctxParams <- case f of
                                    Conc -> ctx_params ty ctx terms
                                    Abs  -> return []

                  -- parameters to the rep function
                  -- let rparams = map (\p -> SigP (VarP p) ((ConT ''R) `AppT` (VarT p))) param
                  let cparams = map (\(x,t,_) -> SigP (VarP x) t) ctxParams

                  -- the recursive call of the rep function
                  let e1 = foldl (\a r -> a `AppE` (VarE r)) (VarE rTypeName) paramNames
                  let e2 = foldl (\a (x,_,_) -> a `AppE` (VarE x)) e1 ctxParams

                  -- the representations of the parameters, as a list
                  -- representations of the data constructors
                  rcons <- mapM (repcon1 ty (length terms == 1) e2 ctxParams) terms
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

                      -- appRep t = foldl (\a p -> a `AppE` (VarE 'rep)) t param
                      appRec t = foldl (\a _ -> a `AppE` (VarE 'dict)) t ctxParams

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


repr1s f ns = foldl (\qd n -> do decs1 <- repr1 f n
                                 decs2 <- qd
                                 return (decs1 ++ decs2)) (return []) ns

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

---  from SYB III code....

typeInfo :: DecQ -> Q (Name, [TyVarBndr], [([TyVarBndr], Cxt, Name, Int)], [(Name, [(Maybe Name, Type)])])
typeInfo m =
     do d <- m
        case d of
           (DataD _ _ _ _ _) ->
            return $ (getName d, paramsA d, consA d, termsA d)
           (NewtypeD _ _ _ _ _) ->
            return $ (getName d, paramsA d, consA d, termsA d)
           _ -> error ("derive: not a data type declaration: " ++ show d)

     where
        consA (DataD _ _ _ cs _)    = map conA cs
        consA (NewtypeD _ _ _ c _)  = [ conA c ]

        paramsA (DataD _ _ ps _ _) = ps
        paramsA (NewtypeD _ _ ps _ _) = ps

        termsA (DataD _ _ _ cs _) = map termA cs
        termsA (NewtypeD _ _ _ c _) = [ termA c ]

        termA (NormalC c xs)        = (c, map (\x -> (Nothing, snd x)) xs)
        termA (RecC c xs)           = (c, map (\(n, _, t) -> (Just $ simpleName n, t)) xs)
        termA (InfixC t1 c t2)      = (c, [(Nothing, snd t1), (Nothing, snd t2)])
        termA (ForallC _ _ n)       = termA n

        conA (NormalC c xs)         = ([], [], simpleName c, length xs)
        conA (RecC c xs)            = ([], [], simpleName c, length xs)
        conA (InfixC _ c _)         = ([], [], simpleName c, 2)
        conA (ForallC bdrs cx con) = let (bdrs', cx', n, l) = conA con
                                      in  (bdrs ++ bdrs', cx ++ cx', n, l)

        getName (DataD _ n _ _ _)      = n
        getName (NewtypeD _ n _ _ _)   = n
        getName d                      = error $ show d

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
