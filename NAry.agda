{-# OPTIONS --rewriting #-}

module NAry where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Nat
open import Data.Vec
open import Function
open import Relation.Binary.PropositionalEquality

+zero : {n : ℕ} → n + zero ≡ n
+zero {n = zero}  = refl
+zero {n = suc _} = cong suc +zero

{-# REWRITE +zero #-}

++[] : ∀ {a} {A : Set a} {n : ℕ} {As : Vec A n} → As ++ [] ≡ As
++[] {As = []} = refl
++[] {As = A ∷ _} = cong (A ∷_) ++[]

{-# REWRITE ++[] #-}

data NAry : {n : ℕ} → Vec Set n → Set → Set where
  constant : {B : Set} → B → NAry [] B
  uncurry : {A B : Set} {n : ℕ} {As : Vec Set n} → (A → NAry As B) → NAry (A ∷ As) B

data HVec : {n : ℕ} → Vec Set n → Set where
  [] : HVec []
  _∷_ : {A : Set} {n : ℕ} {As : Vec Set n} → A → HVec As → HVec (A ∷ As)

result : {B : Set} → NAry [] B → B
result (constant b) = b

curry : {B A : Set} {n : ℕ} {As : Vec Set n} → NAry (A ∷ As) B → A → NAry As B
curry (uncurry f) = f

compose : {B C : Set} {m n : ℕ} {As : Vec Set m} {Bs : Vec Set n}
  → NAry (B ∷ Bs) C → NAry As B → NAry (As ++ Bs) C
compose g (constant b) = curry g b
compose g (uncurry f) = uncurry (compose g ∘ f)

partApply : {C : Set} {m n : ℕ} {As : Vec Set m} {Bs : Vec Set n}
  → NAry (As ++ Bs) C → HVec As → NAry Bs C
partApply f [] = f
partApply (uncurry f) (a ∷ as) = partApply (f a) as

fullApply : {B : Set} {n : ℕ} {As : Vec Set n} → NAry As B → HVec As → B
fullApply f = result ∘ partApply f

record ToNAry (A B  : Set) : Set where
  field
    toNAry : A → B

open ToNAry {{...}} public

instance
  baseCaseTo : {B : Set} → ToNAry B (NAry [] B)
  baseCaseTo = record {toNAry = constant }

  indStepTo : {A B F : Set} {n : ℕ} {As : Vec Set n} → {{ToNAry F (NAry As B)}}
    → ToNAry (A → F) (NAry (A ∷ As) B)
  indStepTo = record {toNAry = λ f → uncurry (λ a → toNAry (f a) )}

toNullary : {B : Set} → B → NAry [] B
toNullary = toNAry

toUnary : {A B : Set} → (A → B) → NAry (A ∷ []) B
toUnary = toNAry

toBinary : {A B C : Set} → (A → B → C) → NAry (A ∷ B ∷ []) C
toBinary = toNAry

record FromNAry (A B : Set) : Set where
  field
    fromNAry : A → B

open FromNAry {{...}} public

instance
  baseCaseFrom : {B : Set} → FromNAry (NAry [] B) B
  baseCaseFrom = record {fromNAry = result}

  indStepFrom : {A B F : Set} {n : ℕ} {As : Vec Set n} → {{FromNAry (NAry As B) F}}
    → FromNAry (NAry (A ∷ As) B) (A → F)
  indStepFrom = record {fromNAry = (fromNAry ∘_) ∘ curry}

fromNullary : {B : Set} → NAry [] B → B
fromNullary = fromNAry

fromUnary : {A B : Set} → NAry (A ∷ []) B → A → B
fromUnary = fromNAry

fromBinary : {A B C : Set} → NAry (A ∷ B ∷ []) C → A → B → C
fromBinary = fromNAry

