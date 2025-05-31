module Data.Zahl.Decidable

import Data.Zahl
import Control.Function
import Decidable.Equality

public export
Injective Zahl.Pos where
  injective Refl = Refl

public export
Injective Zahl.Neg where
  injective Refl = Refl

public export
DecEq Zahl where
  decEq Zero Zero = Yes Refl
  decEq Zero (Pos _) = No $ \Refl impossible
  decEq Zero (Neg _) = No $ \Refl impossible
  decEq (Pos _) Zero = No $ \Refl impossible
  decEq (Pos p1) (Pos p2) = decEqCong $ decEq p1 p2
  decEq (Pos _) (Neg _) = No $ \Refl impossible
  decEq (Neg _) Zero = No $ \Refl impossible
  decEq (Neg _) (Pos _) = No $ \Refl impossible
  decEq (Neg q1) (Neg q2) = decEqCong $ decEq q1 q2

