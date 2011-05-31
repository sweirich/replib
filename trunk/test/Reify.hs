{-# LANGUAGE TemplateHaskell #-}

module Reify where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

doReify :: Name -> Q [Dec]
doReify n = do
  (TyConI dec) <- reify n
  -- let s = show $
  --         case info of
  --           TyConI dec ->
  --             case dec of
  --               (DataD _ _ _ cs _) ->
  --                 map conA cs
  let s = show (typeInfo dec)
  [d| str = $(lift s) |]

typeInfo :: Dec -> (Name, [TyVarBndr], [([TyVarBndr], Cxt, Name, Int)], [(Name, [(Maybe Name, Type)])])
typeInfo d = case d of
    (DataD _ _ _ _ _) ->
      (getName d, paramsA d, consA d, termsA d)
    (NewtypeD _ _ _ _ _) ->
      (getName d, paramsA d, consA d, termsA d)
    _ -> error ("derive: not a data type declaration: " ++ show d)

  where
    consA (DataD _ _ _ cs _)      = map conA cs
    consA (NewtypeD _ _ _ c _)    = [ conA c ]

    paramsA (DataD _ _ ps _ _)    = ps
    paramsA (NewtypeD _ _ ps _ _) = ps

    termsA (DataD _ _ _ cs _)     = map termA cs
    termsA (NewtypeD _ _ _ c _)   = [ termA c ]

    termA (NormalC c xs)          = (c, map (\x -> (Nothing, snd x)) xs)
    termA (RecC c xs)             = (c, map (\(n, _, t) -> (Just $ simpleName n, t)) xs)
    termA (InfixC t1 c t2)        = (c, [(Nothing, snd t1), (Nothing, snd t2)])
    termA (ForallC _ _ n)         = termA n

    conA (NormalC c xs)           = ([], [], simpleName c, length xs)
    conA (RecC c xs)              = ([], [], simpleName c, length xs)
    conA (InfixC _ c _)           = ([], [], simpleName c, 2)
    conA (ForallC bdrs cx con)    = let (bdrs', cx', n, l) = conA con
                                    in  (bdrs ++ bdrs', cx ++ cx', n, l)

    getName (DataD _ n _ _ _)     = n
    getName (NewtypeD _ n _ _ _)  = n
    getName x                     = error $ show x

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
