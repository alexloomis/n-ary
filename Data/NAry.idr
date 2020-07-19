module Data.NAry

import Data.Vect
import Data.HVect
import Control.Isomorphism

%access export
%default total

||| Functions that take `n` parameters.
|||
||| @n the arity of the function.
||| @ts the argument types
||| @t the return type
public export
data NAry : (ts : Vect n Type) -> (t : Type) -> Type where
  Result : b -> NAry Nil b
  Uncurry : (a -> NAry ts b) -> NAry (a :: ts) b

-- Need better name
iden : NAry Nil b -> b
iden (Result b) = b

-- Need better name?
curry : NAry (t :: ts) b -> t -> NAry ts b
curry (Uncurry f) = f

partApply : NAry (ts ++ us) v -> HVect ts -> NAry us v
partApply f Nil = f
partApply (Uncurry f) (x :: xs) = partApply (f x) xs

-- rw : a = b -> a -> b

-- vectApply f = iden . partApply f
-- gives a type mismatch between
-- NAry ts b
-- and
-- NAry (ts ++ []) b
vectApply : NAry ts b -> HVect ts -> b
vectApply (Result b) Nil = b
vectApply (Uncurry f) (x::xs) = vectApply (f x) xs

compose : NAry (b :: bs) c -> NAry as b -> NAry (as ++ bs) c
compose g (Result b) = curry g b
compose g (Uncurry f) = Uncurry $ compose g . f

interface ToNAry a b c where
  toN : a -> b -> c

-- Base case
ToNAry (a -> b) a (NAry Nil b) where
  toN f a = Result $ f a

-- Inductive step
ToNAry f a (NAry ts b) => ToNAry (c -> f) c (NAry (a::ts) b) where
  toN f a = Uncurry . toN $ f a

-- We could automatically eat extra arguments, but choose not to.
-- ToNAry b a (NAry Nil b) where
  -- toN b a = Result b

namespace Nullary
  toNAry : b -> NAry Nil b
  toNAry = Result

toNAry : ToNAry f a (NAry ts b) => f -> NAry (a :: ts) b
toNAry f = Uncurry $ toN f

public export
interface FromNAry f b where
  fromNAry : f -> b

-- Base case
FromNAry (NAry Nil b) b where
  fromNAry (Result b) = b

-- Inductive step
FromNAry (NAry ts b) c => FromNAry (NAry (t :: ts) b) (t -> c) where
  fromNAry (Uncurry f) = fromNAry . f

-- Error messages are nicer with the narrower type.
nullary : b -> NAry Nil b
nullary = toNAry

unary : (a -> b) -> NAry [a] b
unary = toNAry

binary : (a -> b -> c) -> NAry [a,b] c
binary = toNAry

trinary : (a -> b -> c -> d) -> NAry [a,b,c] d
trinary = toNAry

-- Error messages are nicer with the narrower type.
unNullary : NAry Nil b -> b
unNullary = fromNAry

unUnary : NAry [a] b -> (a -> b)
unUnary = fromNAry

unBinary : NAry [a,b] c -> (a -> b -> c)
unBinary = fromNAry

unTrinary : NAry [a,b,c] d -> (a -> b -> c -> d)
unTrinary = fromNAry

-----------
-- Properties of functions.

postulate private fnExt: {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

fnAp : {f : a -> b} -> x = y -> f x = f y
fnAp prf = rewrite prf in Refl

private
lambdaId : {f : a -> b} -> (\y => f y) = f
lambdaId = fnExt (\x => Refl)

private
lambdaEq : {f, g : a -> b} -> f = g -> (\y => f y) = g
lambdaEq pf = rewrite pf in lambdaId

subId : {f : a -> b} -> {g : b -> b} -> ((y : b) -> g y = y)
  -> (z : a) -> g (f z) = f z
subId {f} p x = p (f x)

private
fnIso : Iso b c -> Iso (a -> b) (a -> c)
fnIso (MkIso bc cb bcb cbc) = MkIso (bc .) (cb .) left right
  where
    left f = fnExt (\y => bcb (f y))
    right f = fnExt (\y => cbc (f y))

-----------
-- Isomorphisms

isoIden : Iso b (NAry Nil b)
isoIden = MkIso Result iden resultIden idenResult
  where
    idenResult x = Refl
    resultIden (Result x) = Refl

isoCurry : Iso (t -> NAry ts b) (NAry (t::ts) b)
isoCurry = MkIso Uncurry curry uncurryCurry curryUncurry
  where
    uncurryCurry (Uncurry f) = Refl
    curryUncurry x = Refl

private
isoUnary : Iso (a -> b) (NAry [a] b)
isoUnary = isoTrans (fnIso isoIden) isoCurry

private
isoBinary : Iso (a -> b -> c) (NAry [a,b] c)
isoBinary = isoTrans (fnIso isoUnary) isoCurry
-- and so on...

-----------
-- Application to a vector

vectApply0 : vectApply (nullary a) Nil = a
vectApply0 = Refl

vectApply1 : vectApply (unary g) [a] = g a
vectApply1 = Refl

vectApply2 : vectApply (binary g) [a,b] = g a b
vectApply2 = Refl

vectApply4 : {g : a' -> b' -> c' -> d' -> e'}
  -> vectApply (toNAry g) [a,b,c,d] = g a b c d
vectApply4 = Refl
-- and so on...

-----------

||| fromNAry is the left inverse to toNAry
|||
||| The other order is not true in general.
||| Consider that we could have
|||
||| `f : NAry [a] b`
|||
||| `fromNAry f : a -> b`
|||
||| `toNAry . fromNAry $ f : NAry Nil (a -> b)`
|||
||| However, if the types are the same, equality might still hold.
fromToNAry : {f : a -> b -> c -> d} -> fromNAry (toNAry f) = f
fromToNAry = Refl

-- toFromNAry : {f : NAry [a] b} -> the (NAry [a] b) (unary (unUnary f)) = f
-- toFromNAry {f = Uncurry g} = fnAp {f = Uncurry} ?p0

-----------
-- Composition

compose1 : {f : a -> b} -> {g : b -> c}
  -> vectApply (compose (toNAry g) (unary f)) [x] = g (f x)
compose1 = Refl

compose2 : {f : a -> b} -> {g : b -> c}
  -> vectApply (toNAry (g . f)) [x] = g (f x)
compose2 = Refl

-- toNAry (g . f) = compose (toNAry g) (toNAry f)
private
compose1' : {f : a -> b} -> {g : b -> c}
  -> toNAry (g . f) = compose (toNAry g) (the (NAry [a] b) (toNAry f))
compose1' {f} = fnAp {f = Uncurry} Refl

private
lem1 : {g : b -> NAry Nil c} -> {f : NAry Nil b}
  -> compose (Uncurry g) f = g (iden f)
lem1 {f = Result x} = Refl

private
lem2 : {x : NAry Nil c} -> {y : NAry Nil c} -> x = y -> x = toNAry (iden y)
lem2 {y} p = rewrite p in sym (toFrom isoIden y)

private
lem3 : {g : b -> NAry Nil c} -> {f : NAry Nil b}
  -> compose (Uncurry g) f = toNAry (iden (g (iden f)))
lem3 {g} {f} = lem2 (lem1 {g} {f})
-- lem3 {g} {f} = rewrite lem1 {g} {f} in sym (toFrom isoIden (g (iden f)))

private
lem4 : {f : NAry [a] b} -> {g : NAry [b] c}
  -> compose g f = toNAry (unUnary g . unUnary f)
lem4 {f = Uncurry f} {g = Uncurry g}
  = fnAp {f = Uncurry} (fnExt (\y => lem3 {f = f y}))

-- fromNAry (compose g f) = fromNAry g . fromNAry f
private
compose2' : {f : NAry [a] b} -> {g : NAry [b] c}
  -> fromNAry (compose g f) = the (b -> c) (fromNAry g) . fromNAry f
compose2' {f} {g} = fnAp {f = unUnary} (lem4 {f} {g})

