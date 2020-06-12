module Data.NAry.Hetero.Proof

import Data.NAry.Hetero
import Data.NAry.Hetero as H
import Data.Vect
import Data.HVect

const_iden : {x : NAry Nil a} -> Const (iden x) = x
const_iden {x = Const b} = Refl

iden_const : iden (Const x) = x
iden_const = Refl

uncurry_curry : {x : NAry (t :: ts) b} -> Uncurry (H.curry x) = x
uncurry_curry {x = Uncurry f} = Refl

curry_uncurry : H.curry (Uncurry x) = x
curry_uncurry = Refl

from_nary_to_nary : {f : a} -> fromNAry (toNAry f) = f
from_nary_to_nary = Refl

-- This is much harder since fromNAry has to many possible return types.
-- to_nary_from_nary = ?to_nary_from_nary_rhs
to_nary_from_nary_0 : {f : NAry Nil b} -> toNAry (fromNAry f) = f
to_nary_from_nary_0 {f = Const a} = Refl

vect_apply_0 : vectApply (nullary a) Nil = a
vect_apply_0 = Refl

vect_apply_1 : vectApply (unary g) [a] = g a
vect_apply_1 = Refl

vect_apply_2 : vectApply (binary g) [a,b] = g a b
vect_apply_2 = Refl

vect_apply_3 : vectApply (trinary g) [a,b,c] = g a b c
vect_apply_3 = Refl

-- Essentially `toNAry (g . f) = compose (toNAry g) (toNAry f)`.
to_nary_compose : {f : a -> b} -> {g : b -> c}
  -> vectApply (toNAry (g . f)) [x] = vectApply (compose (toNAry g) (unary f)) [x]
to_nary_compose = Refl

helper : (x : Vect n a) -> x ++ Nil = x
helper Nil = Refl
helper (y::ys) = rewrite helper ys in Refl

-- compose_from_nary : {f : NAry [a] b} -> {g : NAry [b] c}
  -- -> fromNAry g . fromNAry f = fromNAry (compose g f)

