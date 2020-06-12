module Data.NAry.Hetero

import Data.Vect
import Data.HVect

%access public export

-- public export
data NAry : Vect n Type -> Type -> Type where
  Const : b -> NAry Nil b
  Uncurry : (a -> NAry ts b) -> NAry (a :: ts) b

-- public export
iden : NAry Nil b -> b
iden (Const b) = b

-- call apply instead?
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
compose g (Uncurry f) = Uncurry $ flip (flip compose . f) g

-- binary : (a -> b -> c) -> NAry [a,b] c
-- binary = ?binary_rhs

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

FromNAry (NAry Nil b) b where
  fromNAry (Const b) = b

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

{-
test0 : NAry [] Integer
test0 = toNAry 0

test2 : Nat -> String -> Nat
test2 = fromNAry $ toNAry (\n, s => Prelude.Strings.length s + n)

test3 : NAry [Bool, Nat, String] Nat
test3 = toNAry f
  where
    f : Bool -> Nat -> String -> Nat
    f b i s = if b then i else length s
    -}

