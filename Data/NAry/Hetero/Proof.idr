module Data.NAry.Hetero.Proof

import Control.Isomorphism
import Data.NAry.Hetero
import Data.NAry.Hetero as H
import Data.Vect
import Data.HVect

-----------
-- Properties of functions.

postulate fn_ext: {f, g : a -> b} -> ((x : a) -> f x = g x) -> f = g

fn_ap : {f : a -> b} -> x = y -> f x = f y
fn_ap prf = rewrite prf in Refl

lambda_id : {f : a -> b} -> (\y => f y) = f
lambda_id = fn_ext (\x => Refl)

lambda_eq : {f, g : a -> b} -> f = g -> (\y => f y) = g
lambda_eq pf = rewrite pf in lambda_id

sub_id : {f : a -> b} -> {g : b -> b} -> ((y : b) -> g y = y)
  -> (z : a) -> g (f z) = f z
sub_id {f} p x = p (f x)

fn_iso : Iso b c -> Iso (a -> b) (a -> c)
fn_iso (MkIso bc cb bcb cbc) = MkIso (bc .) (cb .) left right
  where
    left f = fn_ext (\y => bcb (f y))
    right f = fn_ext (\y => cbc (f y))

-----------
-- Isomorphisms

const_iden : (x : NAry Nil b) -> H.Const (iden x) = x
const_iden (Const x) = Refl

iso_iden : Iso b (NAry Nil b)
iso_iden = MkIso Const iden const_iden iden_const
  where
    iden_const x = Refl

iso_curry : Iso (t -> NAry ts b) (NAry (t::ts) b)
iso_curry = MkIso Uncurry curry uncurry_curry curry_uncurry
  where
    uncurry_curry (Uncurry f) = Refl
    curry_uncurry x = Refl

iso_unary : Iso (a -> b) (NAry [a] b)
iso_unary = isoTrans (fn_iso iso_iden) iso_curry

iso_binary : Iso (a -> b -> c) (NAry [a,b] c)
iso_binary = isoTrans (fn_iso iso_unary) iso_curry

-----------

vect_apply_0 : vectApply (nullary a) Nil = a
vect_apply_0 = Refl

vect_apply_1 : vectApply (unary g) [a] = g a
vect_apply_1 = Refl

vect_apply_2 : vectApply (binary g) [a,b] = g a b
vect_apply_2 = Refl

vect_apply_3 : vectApply (trinary g) [a,b,c] = g a b c
vect_apply_3 = Refl

vect_apply_4 : {g : a' -> b' -> c' -> d' -> e'}
  -> vectApply (toNAry g) [a,b,c,d] = g a b c d
vect_apply_4 = Refl
-- and so on...

-----------

compose_1 : {f : a -> b} -> {g : b -> c}
  -> toNAry (g . f) = compose (toNAry g) (unary f)
compose_1 {f} {g} = fn_ap {f = Uncurry} Refl

{-
lem : {g : b -> NAry Nil c} -> {f : a -> NAry Nil b} -> (x : a)
  -> compose (Uncurry g) (f x) = g (iden (f x))
lem {g} {f} x = ?p2
-}

compose_2 : {f : NAry [a] b} -> {g : NAry [b] c} -> {x : a}
  -> {auto p : (y : NAry Nil d) -> H.Const (iden y) = y}
  -> compose g f = unary (unUnary g . unUnary f)
compose_2 {f = Uncurry f} {g = Uncurry g} {x} {p}
  = fn_ap {f = Uncurry} (fn_ext ?p1)

{-
compose_2 : {f : NAry [a] b} -> {g : NAry [b] c} -> {x : a}
  -> (unUnary g . unUnary f) x = unUnary (compose g f) x
compose_2 {f} {g}
  = ?p2
  -}

