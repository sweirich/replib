-- OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances -ddump-splices --

{-# LANGUAGE TemplateHaskell, UndecidableInstances #-} 

-----------------------------------------------------------------------------
-- |
-- Module      :  Derive
-- Copyright   :  (c) The University of Pennsylvania, 2006
-- License     :  TBD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- code to automatically derive representations and instance declarations 
-- for user defined datatypes. 
--
--
-----------------------------------------------------------------------------


module Data.RepLib.Derive (
	repr, reprs, repr1, repr1s, derive
) where

import Data.RepLib.R 
import Data.RepLib.R1 
import Language.Haskell.TH
import Data.List (nub)
import Data.Tuple


-- Given a type, produce its representation. 
-- Note, that the representation of a type variable "a" is (rep :: R a) so Rep a must be 
-- in the context
repty :: Type -> Exp
repty (ForallT _ _ _) = error "cannot rep"
repty (VarT n) = (SigE (VarE (mkName "rep")) ((ConT ''R) `AppT` (VarT n)))
repty (AppT t1 t2) = (repty t1) -- `AppE` (repty t2)
repty (ConT n) = 
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
      c         -> (VarE (rName n))
-- repty (TupleT 2) = (VarE (mkName "rTup2"))
repty (TupleT i) = error "urk"
repty (ArrowT)   = (ConE 'Arrow)
repty (ListT)    = (VarE 'rList)
 

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
repcon single d (name, sttys) = 
	 let rargs = foldr (\ (_,t) tl -> 
		 [| $(return (repty t)) :+: $(tl) |]) [| MNil |] sttys in
		 [| Con $(remb single d (name,sttys)) $(rargs) |]

-- the "from" function that coerces from an "a" to the arguments
rfrom :: Bool ->  -- does this datatype have only a single constructor
          Type ->  -- the datatype itself
          (Name, [(Maybe Name, Type)]) ->  -- data constructor name, list of parameters with record names
          Q Exp
rfrom single d (name, sttys) = do
       vars <- mapM (\_ -> newName "x") sttys
       outvar <- newName "y"
       let outpat :: Pat
           outpat = ConP name (map VarP vars)
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
rto d (name,sttys) =  
  do vars <- mapM (\_ -> newName "x") sttys
     let topat = foldr (\v tl -> InfixP  (VarP v) (mkName ":*:") tl)
                         (ConP 'Nil []) vars
         tobod = foldl (\tl v -> tl `AppE` (VarE v)) (ConE name) vars           
     return (LamE [topat] tobod) 

-- the embedding record
remb :: Bool -> Type -> (Name, [(Maybe Name, Type)]) -> Q Exp
remb single d (name, sttys) = 
    [| Emb  { name   = $(stringName name), 
              to     = $(rto d (name,sttys)), 
              from   = $(rfrom single d (name,sttys)),
              labels = Nothing,
              fixity = Nonfix } |]

repDT :: Name -> [Name] -> Q Exp
repDT name param = 
      do str <- stringName name
         let reps = foldr (\p f -> 
									  (ConE (mkName ":+:")) `AppE`
									     (SigE (VarE (mkName "rep")) 
											((ConT ''R) `AppT` (VarT p)))  `AppE` f)
						  (ConE 'MNil) param
         [| DT $(return str) $(return reps) |]

-- Create an "R" representation for a given type constructor
repr :: Name -> Q [Dec]
repr n = do info' <- reify n
            case info' of 
               TyConI d -> do
                  (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec) 
                  let paramNames = map tyVarBndrName param
                  baseT <- conT name                      
                  -- the type that we are defining, applied to its parameters.
                  let ty = foldl (\x p -> x `AppT` (VarT p)) baseT paramNames
                  -- the representations of the paramters, as a list
                  -- representations of the data constructors
                  rcons <- mapM (repcon (length terms == 1) ty) terms
                  body  <- [| Data $(repDT name paramNames) $(return (ListE rcons)) |]
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

reprs :: [Name] -> Q [Dec]
reprs ns = foldl (\qd n -> do decs1 <- repr n 
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
ctx_params ty ctxName l = do 
   let tys = nub (map snd (foldr (++) [] (map snd l))) 
   mapM (\t -> do n <- newName "p"
                  let ctx_t = (VarT ctxName) `AppT` t
                  return (n, ctx_t, t)) tys    

lookupName :: Type -> [(Name, Type, Type)] -> [(Name, Type, Type)] ->  Name
lookupName t l ((n, t1, t2):rest) = if t == t2 then n else lookupName t l rest
lookupName t l [] = error ("lookupName: Cannot find type " ++ show t ++ " in " ++ show l)

repcon1 :: Type                               -- result type of the constructor       
   		  -> Bool
          -> Exp                              -- recursive call (rList1 ra pa)
          -> [(Name,Type,Type)]               -- ctxParams 
          -> (Name, [(Maybe Name, Type)])     -- name of data constructor + args
          -> Q Exp
repcon1 d single rd1 ctxParams (name, sttys) = 
       let rec = foldr (\ (_,t) tl -> 
                    let expQ = (VarE (lookupName t ctxParams ctxParams))
                    in [| $(return expQ) :+: $(tl) |]) [| MNil |] sttys in
       [| Con $(remb single d (name,sttys)) $(rec) |]

repr1 :: Name -> Q [Dec]
repr1 n = do info' <- reify n
             case info' of
               TyConI d -> do
                  (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec) 
                  let paramNames = map tyVarBndrName param
                  -- the type that we are defining, applied to its parameters.                      
                  let ty = foldl (\x p -> x `AppT` (VarT p)) (ConT name) paramNames
                  let rTypeName = rName1 n

                  ctx <- newName "ctx"
                  ctxParams <- ctx_params ty ctx terms
                               
                  -- parameters to the rep function
                  -- let rparams = map (\p -> SigP (VarP p) ((ConT ''R) `AppT` (VarT p))) param
                  let cparams = map (\(n,t,_) -> SigP (VarP n) t) ctxParams              

                  -- the recursive call of the rep function
                  let e1 = foldl (\a r -> a `AppE` (VarE r)) (VarE rTypeName) paramNames
                  let e2 = foldl (\a (n,_,_) -> a `AppE` (VarE n)) e1 ctxParams

                  -- the representations of the parameters, as a list
                  -- representations of the data constructors
                  rcons <- mapM (repcon1 ty (length terms == 1) e2 ctxParams) terms
                  body  <- [| Data1 $(repDT name paramNames) 
                                    $(return (ListE rcons)) |]
                           
                  let rhs = LamE (cparams) body
{-                    rhs_type = ForallT (ctx:param) rparams 
                                  (foldr (\ (p,t) ret -> `ArrowT` `AppT` t `AppT` ret) ty params) -}
                      rTypeDecl = ValD (VarP rTypeName) (NormalB rhs) [] 


                  let ctxRep = map (\p -> ClassP (mkName "Rep") [VarT p]) paramNames
                      ctxRec = map (\(_,t,_) -> ClassP ''Sat [t]) ctxParams

                      -- appRep t = foldl (\a p -> a `AppE` (VarE 'rep)) t param
                      appRec t = foldl (\a p -> a `AppE` (VarE 'dict)) t ctxParams

                  let inst  = InstanceD (ctxRep ++ ctxRec)
                                ((ConT ''Rep1) `AppT` (VarT ctx) `AppT` ty)
                                [ValD (VarP (mkName "rep1"))
                                  (NormalB (appRec (VarE rTypeName))) []]

                  let rSig = SigD rTypeName (ForallT (map PlainTV (ctx : paramNames)) ctxRep
                              (foldr (\(_,p,_) f -> (ArrowT `AppT` p `AppT` f))
                                     ((ConT (mkName "R1")) `AppT` (VarT ctx) `AppT` ty)
                                     ctxParams))
                  decs <- repr n
                  return (decs ++ [rSig, rTypeDecl, inst])


repr1s :: [Name] -> Q [Dec]


repr1s ns = foldl (\qd n -> do decs1 <- repr1 n 
                               decs2 <- qd
                               return (decs1 ++ decs2)) (return []) ns
derive = repr1s

--------------------------------------------------------------------------------------



--- Helper functions

stringName :: Name -> Q Exp
stringName n = return (LitE (StringL (nameBase n)))

---  from SYB III code....

typeInfo :: DecQ -> Q (Name, [TyVarBndr], [(Name, Int)], [(Name, [(Maybe Name, Type)])])
typeInfo m =
     do d <- m
        case d of
           d@(DataD _ _ _ _ _) ->
            return $ (name d, paramsA d, consA d, termsA d)
           d@(NewtypeD _ _ _ _ _) ->
            return $ (name d, paramsA d, consA d, termsA d)
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

        conA (NormalC c xs)         = (simpleName c, length xs)
        conA (RecC c xs)            = (simpleName c, length xs)
        conA (InfixC _ c _)         = (simpleName c, 2)

        name (DataD _ n _ _ _)      = n
        name (NewtypeD _ n _ _ _)   = n
        name d                      = error $ show d

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
