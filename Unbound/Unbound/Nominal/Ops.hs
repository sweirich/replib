module Unbound.Nominal.Ops where

import Unbound.Nominal.Alpha
import Unbound.Nominal.Types

rec :: (Alpha p) => p -> Rec p
rec = Rec

unrec :: (Alpha p) => Rec p -> p
unrec (Rec p) = p

embed :: (Alpha t) => t -> Embed t
embed = Embed

unembed :: (Alpha t) => Embed t -> t
unembed (Embed t) = t

rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind = Rebind

unrebind :: (Alpha a, Alpha b) => Rebind a b -> (a, b)
unrebind (Rebind p q) = (p, q)
