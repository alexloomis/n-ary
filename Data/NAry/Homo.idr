module NAry.Homo

import Data.Vect

export
data NAry : Nat -> Type -> Type -> Type where
  Const : b -> NAry Z a b
  Uncurry : (a -> NAry n a b) -> NAry (S n) a b

export
apply : NAry n a b -> Vect n a -> b
apply (Const b) [] = b
apply (Uncurry f) (x::xs) = apply (f x) xs

export
interface ToNAry a b c where
  toN : a -> b -> c

-- Base case
ToNAry (a -> b) a (NAry 0 a b) where
  toN f a = Const $ f a

-- Inductive step
ToNAry f a (NAry n a b) => ToNAry (a -> f) a (NAry (S n) a b) where
  toN f a = Uncurry . toN $ f a

-- We can eat extra arguments.
ToNAry b a (NAry 0 a b) where
  toN b a = Const b

namespace Nullary
  export
  toNAry : b -> NAry Z a b
  toNAry = Const

export
toNAry : ToNAry f a (NAry n a b) => f -> NAry (S n) a b
toNAry f = Uncurry $ toN f

test3 : NAry 3 Integer (Integer -> Integer)
test3 = toNAry (\w,x,y,z => w + x*y + z)

test4 : Integer
test4 = toNAry (\w,x,y,z => w + x*y + z) `apply` [1,2,3,4]

test5 : NAry 5 Integer Integer
test5 = toNAry (\w,x,y,z => w + x*y + z)

-- ToNAry a (Vect 0 b) a where
  -- toN = const

-- ToNAry a (Vect n b) c => ToNAry (b -> a) (Vect (S n) b) c where
  -- toN f (x :: xs) = toN (f x) xs

-- test2 : Vect 2 Integer -> Integer
-- test2 xs = toN (+) xs

-- test4 : Vect 4 Integer -> Integer
-- test4 = toN (\w,x,y,z => w + x*y + z)

