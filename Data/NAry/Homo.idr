module NAry.Homo

import Data.Vect
import Data.NAry as H

data NAry : Nat -> Type -> Type -> Type where
  fromHetero : H.NAry (replicate n a) b -> NAry n a b

