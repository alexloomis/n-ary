module Data.Vect.Hetero

import Data.Vect

-- Heterogenous vectors.
public export
data HVect : Vect n Type -> Type where
  Nil : HVect Nil
  (::) : a -> HVect ts -> HVect (a :: ts)

public export
interface Homogenous (ts : Vect n Type) a where
  toVect : HVect ts -> Vect n a

Homogenous Nil a where
  toVect = const Nil

Homogenous ts a => Homogenous (a :: ts) a where
  toVect (x :: xs) = x :: toVect xs

