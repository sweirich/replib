{-# LANGUAGE UndecidableInstances, OverlappingInstances, IncoherentInstances,
    ExistentialQuantification, ScopedTypeVariables, EmptyDataDecls,
    MultiParamTypeClasses, FlexibleInstances, FlexibleContexts
  #-}

-----------------------------------------------------------------------------
-- 
-- Module      :  Data.RepLib.Unify
-- Copyright   :  (c) Ben Kavanagh 2008
-- License     :  BSD
-- 
-- Maintainer  :  Ben Kavanagh (ben.kavanagh@gmail.com)
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Generic unification with Replib
--
-----------------------------------------------------------------------------


module Data.RepLib.Unify
where

import Data.RepLib.R 
import Data.RepLib.R1
import Data.RepLib.RepAux
import Data.RepLib.PreludeReps()
import Control.Monad.State
import Control.Monad.Error

data Proxy a 


----------------- Unification -------------------------

-- unify takes an equality constraint (from a pool of constraints) and processes it. 
-- if there is a variable we do an occurs check and if passes add the assignment and apply
-- to the current substitution/constraints. otherwise it either matches leafs w/equality or decomposes
-- function terms (constructors) to produce additional constraints. So it takes a substitution
-- and a set of constraints and returns a new substitution, and a new set of constraints, 
-- with the possibility of failure. 


-- just use string errors for now.
type UnifyError = String


-- Error/State monad for unification. This version does not abstract the monad. 
type UM n a b = ErrorT UnifyError (State (UnificationState n a)) b


data UnifySubD n a b = UnifySubD { unifyStepD :: Proxy (n, a) -> b -> b -> UM n a (),
				   substD:: n -> a -> b -> b,
				   occursCheckD :: n -> Proxy a -> b -> Bool}

instance (Unify n a b, Subst n a b, Occurs n a b) => Sat (UnifySubD n a b) where
    dict = UnifySubD {unifyStepD = unifyStep, substD = subst, occursCheckD = occursCheck}


data UConstraint n a = forall b. UC (UnifySubD n a b) b b
data UnificationState n a = UState {uConstraints :: [UConstraint n a],
				    uSubst :: [(n, a)]}



-- Unification Step

class (Eq n, Show n, Show a, Show b, HasVar n a) => Unify n a b where
    unifyStep :: Proxy (n, a) -> b -> b -> UM n a ()

-- Generic unify instance
instance (Eq n, Show n, Show a, Show b, HasVar n a, Rep1 (UnifySubD n a) b) => Unify n a b where
    unifyStep = unifyStepR1 rep1

				 
-- | Generic unifyStep. almost identical to polymorphic equality
unifyStepR1 :: (Eq n, Show n, Show a, Show b, HasVar n a) => R1 (UnifySubD n a) b -> Proxy (n, a) -> b -> b -> UM n a ()
unifyStepR1 Int1 _       =  unifyStepEq
unifyStepR1 Char1 _      =  unifyStepEq
unifyStepR1 Integer1 _   =  unifyStepEq
unifyStepR1 Float1 _     =  unifyStepEq
unifyStepR1 Double1 _    =  unifyStepEq
unifyStepR1 (Data1 _ cons) dum = 
    \ x y ->                          
       let loop (Con rcd rec : rest) = 
              case (from rcd x, from rcd y) of 
	         (Just p1, Just p2) -> addConstraintsRL1 rec dum p1 p2 
		 (Nothing, Nothing) -> loop rest
		 (_,_) -> throwError (strMsg $ "constructor mismatch when trying to match " ++ show x ++ " = " ++ show y)   
	   in loop cons
unifyStepR1 r1 _ = \_ _ -> throwError (strMsg ("unifyStepR1 unhandled generic type constructor"))



addConstraintsRL1 ::  MTup (UnifySubD n a) l -> Proxy (n, a) -> l -> l -> UM n a ()
addConstraintsRL1 MNil _ Nil Nil = return ()
addConstraintsRL1 (r :+: rl) (dum :: Proxy (n, a)) (p1 :*: t1) (p2 :*: t2) =
  do queueConstraint $ UC r p1 p2
     addConstraintsRL1 rl dum t1 t2


unifyStepEq x y = if x == y 
		    then return ()
		    else throwError $ strMsg ("unify failed when testing equality for " ++ show x ++ " = " ++ show y)    -- " show x ++ " /= " ++ show y)


-- a a instance
instance (Eq n, Show n, Show a, HasVar n a, Rep1 (UnifySubD n a) a) => Unify n a a where
    unifyStep (dum :: Proxy (n, a)) (a1::a) a2 =
	case ((is_var a1) :: Maybe n, (is_var a2) :: Maybe n) of
	    (Just n1, Just n2) ->  if n1 == n2
				     then return ()
				     else addSub n1 ((var n2) :: a); 
	    (Just n1, _) -> addSub n1 a2
	    (_, Just n2) ->  addSub n2 a1
	    (_, _) -> unifyStepR1 rep1 dum a1 a2
	where 
        addSub n t = extendSubstitution (n, t) 


dequeueConstraint :: UM n a (Maybe (UConstraint n a))
dequeueConstraint = do s <- get 
		       case s of (UState [] _) -> return Nothing
				 (UState (x : xs) sub) -> do put $ UState xs sub 
							     return $ Just x
   
queueConstraint ::  UConstraint n a -> UM n a ()
queueConstraint eq = modify (\ (UState xs sub) -> (UState (eq : xs) sub))


-- 
-- I know of three ways to extend subst. 
-- 1. Just extend the list. 
--    this does not remove instances of the variable assigned from the remaining 
--    substitution. This means that when doing occurs checks will 
--    need to unfold the substitution as you step down the tree. This is done lazily
--    but repeat unfoldings will very often be necessary. 
-- 2. Apply the sub everywhere in the current sub/constraints and then extend the list. This
--    Does unnecessary work by unfolding nodes that may never be examined but does not repeat
--    work. 
-- 3. Just extend the list but construct the terms from references (graph datatype) so
--    that when unfolding substitution lazily during occurs check, no further unfolding will
--    be necessary once completed. This is more efficient but not as straightforward to 
--    analyse.
-- 
-- I use (2) 

extendSubstitution ::  (HasVar n a, Eq n, Show n, Show a, Rep1 (UnifySubD n a) a) => (n, a) -> UM n a ()        -- (could fail with occurs check)
extendSubstitution asgn@((n :: n), (a :: a)) =
    if (occursCheck n (undefined :: Proxy a) a)
       then throwError $ "occurs check failed when extending sub with " ++ (show n) ++ " = " ++ (show a)
       else do (UState xs sub) <- get
 	       let sub' = [(n', subst n a a') | (n', a') <- sub]                            -- these might have side effects if we want to handle binding via freshmonad.
               let xs' = [UC d (substD d n a b1) (substD d n a b2) | (UC d b1 b2) <- xs]
               put (UState xs' (asgn : sub'))






-- Solving unification = 1) initialise problem, 2) run rewrites until no constraints or error.
solveUnification :: (HasVar n a, Eq n, Show n, Show a, Rep1 (UnifySubD n a) a) => [(a, a)] -> Maybe [(n, a)]
solveUnification (eqs :: [(a, a)]) = 
    case r of Left e -> error e
	      Right _ -> Just $ uSubst final
    where
    (r, final) = runState (runErrorT rwConstraints) (UState cs [])
    cs = [(UC dict a1 a2) | (a1, a2) <- eqs]
    rwConstraints :: UM n a ()
    rwConstraints = do c <- dequeueConstraint
		       case c of Just (UC d a1 a2) -> do result <- unifyStepD d (undefined :: Proxy (n, a)) a1 a2
							 rwConstraints
				 Nothing -> return ()



-- To offer this I have to turn on -fallow-overlapping-instances. This rejects the a a instance of the dictionary, 
-- choosing the more general a b instance instead. Thus this can only be used when a /= b, for example Term, OuterTerm
-- in the example testcase. because the instances chosen for dict here are different than above I cannot reduce
-- solveUnification to a call to solveUnification'. Please forgive the code duplication. ugh.

solveUnification' :: (HasVar n a, Eq n, Show n, Show a, Show b, Rep1 (UnifySubD n a) b) => Proxy (n, a) -> [(b, b)] -> Maybe [(n, a)]
solveUnification' (dum :: Proxy (n, a)) (eqs :: [(b, b)]) = 
    case r of Left e -> error e
	      Right _ -> Just $ uSubst final
    where
    (r, final) = runState (runErrorT rwConstraints) (UState cs [])
    cs = [(UC dict a1 a2) | (a1, a2) <- eqs]
    rwConstraints :: UM n a ()
    rwConstraints = do c <- dequeueConstraint
		       case c of Just (UC d a1 a2) -> do result <- unifyStepD d dum a1 a2
							 rwConstraints
				 Nothing -> return ()




class HasVar a b where
    is_var :: b -> Maybe a     -- retrieve the name of a variable
    var :: a -> b              -- inject name as a variable



-- Generic substitution without binding. (No freshness monad required)
-- substitute [a -> t] t'. 
class Subst a t t' where
    subst ::  a -> t -> t' -> t'

-- generic instance
instance Rep1 (UnifySubD a t) t' => Subst a t t' where
    subst = substR1 rep1

-- generic subst.
substR1 :: Rep1 (UnifySubD a t) t' => R1 (UnifySubD a t) t' -> a -> t -> t' -> t'
substR1 r (a::a) (t::t) t' = gmapT1 (\cb b -> substD cb a t b) t'

-- a a instance
instance (Eq a, HasVar a t, Rep1 (UnifySubD a t) t) => Subst a t t where
    subst a t t' = if is_var t' == Just a 
		  then t 
		  else gmapT1 (\cb b -> substD cb a t b) t'


-- Generic Occurs checking
class Occurs n a b where
    occursCheck :: n -> Proxy a -> b -> Bool
		   
-- generic instance
instance Rep1 (UnifySubD n a) b => Occurs n a b where
    occursCheck = occursCheckR1 rep1

-- generic subst.
occursCheckR1 :: Rep1 (UnifySubD n a) b => R1 (UnifySubD n a) b -> n -> Proxy a -> b -> Bool
occursCheckR1 r (n::n) pa b = or $ gmapQ1 (\cb b -> occursCheckD cb n pa b) b

-- a a instance.
instance (Eq n, HasVar n a, Rep1 (UnifySubD n a) a) => Occurs n a a where
    occursCheck n pa a = if is_var a == Just n 
		  then True 
		  else or $ gmapQ1 (\cb b -> occursCheckD cb n pa b) a


