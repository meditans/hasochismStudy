-- * A Variety of Quantifiers

{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}

module Lib where

-- ** Let's see some extensions

data Nat = Z | S Nat deriving (Show, Eq, Ord)

data Vec :: Nat -> * -> * where
  V0   ::                 Vec Z     x
  (:>) :: x -> Vec n x -> Vec (S n) x

infixr 4 :>

type family (m :: Nat) :+ (n :: Nat) :: Nat
type instance Z :+ n = n
type instance (S m) :+ n = S (m :+ n)

vappend :: Vec m x -> Vec n x -> Vec (m :+ n) x
vappend V0 ys = ys
vappend (x :> xs) ys = x :> (vappend xs ys)


-- Now let's say we want to reverse appending:
-- vchop :: Vec (m :+ n) -> (Vec m x, Vec n x)

-- The problem with the function above is that we need m at run time, and
-- explicitly. But forall in haskell is only for implicit and static things. The
-- solution to this conundrum is ~singleton GADTs~.

data Natty :: Nat -> * where
  Zy :: Natty Z
  Sy :: Natty n -> Natty (S n)

vchop :: Natty m -> Vec (m :+ n) x -> (Vec m x, Vec n x)
vchop Zy     xs        = (V0, xs)
vchop (Sy n) (x :> xs) = let (ys, zs) = vchop n xs in (x :> ys, zs)

-- Now for a further disturbance:

-- #+BEGIN_EXAMPLE
-- vtake :: Natty m -> Vec (m :+ n) x -> Vec m x
-- vtake Zy     xs        = V0
-- vtake (Sy n) (x :> xs) = let ys = vtake n xs in x :> ys
-- #+END_EXAMPLE

-- Please detail why this code is not compilable.

-- Our problem is then that we have some static data, which has to be made
-- explicit. So we just define:

data Proxy :: κ -> * where
  Proxy :: Proxy i

vtake :: Natty m -> Proxy n -> Vec (m :+ n) x -> Vec m x
vtake Zy     n xs        = V0
vtake (Sy m) n (x :> xs) = x :> vtake m n xs

-- Another example of implicit quantification used statically to compute a type
-- but erased at run time:

type family Arity (n :: Nat) (x :: *) :: *
type instance Arity Z x = x
type instance Arity (S n) x = x -> Arity n x

varity :: Arity n x -> Vec n x -> x
varity x V0 = x
varity fxAnx (x :> xs) = varity (fxAnx x) xs

