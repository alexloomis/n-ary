module NAry.Homo

import Data.Vect
import Data.NAry.Hetero as H

data NAry : Nat -> Type -> Type -> Type where
  fromHetero : H.NAry (replicate n a) b -> NAry n a b

