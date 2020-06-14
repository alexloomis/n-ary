module Data.NAry.Hetero

import Data.Vect
import Data.HVect

%access public export
%default total

-- public export
data NAry : Vect n Type -> Type -> Type where
  Const : b -> NAry Nil b
  Uncurry : (a -> NAry ts b) -> NAry (a :: ts) b

-- Need better name
-- public export
iden : NAry Nil b -> b
iden (Const b) = b

-- Need better name
-- public export
curry : NAry (t :: ts) b -> t -> NAry ts b
curry (Uncurry f) = f

-- export
vectApply : NAry ts b -> HVect ts -> b
vectApply (Const b) Nil = b
vectApply (Uncurry f) (x::xs) = vectApply (f x) xs

-- export
compose : NAry (b :: bs) c -> NAry as b -> NAry (as ++ bs) c
compose g (Const b) = curry g b
compose g (Uncurry f) = Uncurry $ compose g . f

-- export
interface ToNAry a b c where
  toN : a -> b -> c

-- Base case
ToNAry (a -> b) a (NAry Nil b) where
  toN f a = Const $ f a

-- Inductive step
ToNAry f a (NAry ts b) => ToNAry (c -> f) c (NAry (a::ts) b) where
  toN f a = Uncurry . toN $ f a

-- We can eat extra arguments
ToNAry b a (NAry Nil b) where
  toN b a = Const b

namespace Nullary
  -- export
  toNAry : b -> NAry Nil b
  toNAry = Const

-- export
toNAry : ToNAry f a (NAry ts b) => f -> NAry (a :: ts) b
toNAry f = Uncurry $ toN f

-- public export
interface FromNAry f b where
  fromNAry : f -> b

-- Base case
FromNAry (NAry Nil b) b where
  fromNAry (Const b) = b

-- Inductive step
FromNAry (NAry ts b) c => FromNAry (NAry (t :: ts) b) (t -> c) where
  fromNAry (Uncurry f) = fromNAry . f

nullary : b -> NAry Nil b
nullary = toNAry

unary : (a -> b) -> NAry [a] b
unary = toNAry

binary : (a -> b -> c) -> NAry [a,b] c
binary = toNAry

trinary : (a -> b -> c -> d) -> NAry [a,b,c] d
trinary = toNAry

-- These can all use fromNAry,
-- but the type checker is much less finicky with these.
unNullary : NAry Nil b -> b
unNullary = iden

unUnary : NAry [a] b -> (a -> b)
unUnary = (iden .) . curry

unBinary : NAry [a,b] c -> (a -> b -> c)
unBinary = (unUnary .) . curry

unTrinary : NAry [a,b,c] d -> (a -> b -> c -> d)
unTrinary = (unBinary .) . curry

