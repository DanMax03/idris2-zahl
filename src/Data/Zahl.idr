module Data.Zahl

%default total

public export
data Zahl : Type where
  Zero : Zahl
  Pos : (p : Nat) -> Zahl
  Neg : (q : Nat) -> Zahl

%name Zahl a

public export
zahlToInteger : Zahl -> Integer
zahlToInteger Zero = 0
zahlToInteger (Pos k) = natToInteger (S k)
zahlToInteger (Neg k) = -(natToInteger (S k))

----------------------------------------
--             Interfaces             --
----------------------------------------

public export
Num Zahl where
  Zero + b = b
  a + Zero = a
  (Pos p1) + (Pos p2) = Pos (S p1 + S p2)
  (Pos p1) + (Neg q2) = case compare p1 q2 of
                             LT => Neg (q2 `minus` S p1)
                             EQ => Zero
                             GT => Pos (p1 `minus` S q2)
  (Neg q1) + (Pos p2) = case compare q1 p2 of
                             LT => Pos (p2 `minus` S q1)
                             EQ => Zero
                             GT => Neg (q1 `minus` S p2)
  (Neg q1) + (Neg q2) = Neg (S q1 + S q2)

  Zero * b = Zero
  a * Zero = Zero
  (Pos p1) * (Pos p2) = Pos (S p1 * S p2)
  (Pos p1) * (Neg q2) = Neg (S p1 * S q2)
  (Neg q1) * (Pos p2) = Neg (S q1 * S p2)
  (Neg q1) * (Neg q2) = Pos (S q1 * S q2)

  fromInteger x = if x == 0
                     then Zero
                     else if x > 0
                             then Pos (fromInteger (x - 1))
                             else Neg (fromInteger (x + 1))

public export
Neg Zahl where
  a - b = a + (negate b)

  negate Zero = Zero
  negate (Pos p) = Neg p
  negate (Neg q) = Pos q

public export
Abs Zahl where
  abs (Neg q) = Pos q
  abs a = a

-- TODO: make inductive?
public export
Integral Zahl where
  div a b = fromInteger $ div (zahlToInteger a) (zahlToInteger b)
  mod a b = fromInteger $ mod (zahlToInteger a) (zahlToInteger b)

public export
Semigroup Zahl where
  (<+>) = (+)

public export
Monoid Zahl where
  neutral = Zero

public export
Eq Zahl where
  Zero == Zero = True
  (Pos p1) == (Pos p2) = p1 == p2
  (Neg q1) == (Neg q2) = q1 == q2
  a == b = False

public export
Ord Zahl where
  compare Zero Zero = EQ
  compare Zero (Pos _) = LT
  compare Zero (Neg _) = GT
  compare (Pos _) Zero = GT
  compare (Pos p1) (Pos p2) = compare p1 p2
  compare (Pos _) (Neg _) = GT
  compare (Neg _) Zero = LT
  compare (Neg _) (Pos _) = LT
  compare (Neg q1) (Neg q2) = compare q2 q1

public export
Show Zahl where
  show Zero = "0"
  show (Pos p) = show $ S p
  show (Neg q) = "-\{show $ S q}"

----------------------------------------
--               Casts                --
----------------------------------------

public export
Cast Nat Zahl where
  cast Z = Zero
  cast (S n) = Pos n

public export
Cast Integer Zahl where
  cast = fromInteger

public export
Cast Zahl Integer where
  cast = zahlToInteger

public export
Cast Zahl String where
  cast = show

