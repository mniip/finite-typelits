--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite
-- Copyright   :  (C) 2015 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE TypeOperators, DataKinds, TypeFamilies, FlexibleContexts, ExistentialQuantification, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
module Data.Finite
    (
        Finite,
        packFinite, packFiniteProxy,
        finite, finiteProxy,
        getFinite, finites, finitesProxy,
        equals, cmp,
        natToFinite,
        weaken, strengthen, shift, unshift,
        weakenN, strengthenN, shiftN, unshiftN,
        weakenProxy, strengthenProxy, shiftProxy, unshiftProxy,
        add, sub, multiply,
        combineSum, combineProduct,
        separateSum, separateProduct,
        finite0Absurd, FiniteNat(..), finiteNatVal,
        isValidFinite
    )
    where

import Data.Maybe
import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits
import Unsafe.Coerce

import Data.Finite.Internal

-- | Convert an 'Integer' into a 'Finite', returning 'Nothing' if the input is out of bounds.
packFinite :: forall n. KnownNat n => Integer -> Maybe (Finite n)
packFinite x = if x < natVal (Proxy @n) && x >= 0
                  then Just $ Finite x
                  else Nothing

-- | Same as 'packFinite' but with a proxy argument to avoid type signatures.
packFiniteProxy :: forall n proxy. KnownNat n => proxy n -> Integer -> Maybe (Finite n)
packFiniteProxy _ = packFinite

-- | Same as 'finite' but with a proxy argument to avoid type signatures.
finiteProxy :: forall n proxy. KnownNat n => proxy n -> Integer -> Finite n
finiteProxy _ = finite

-- | Generate a list of length @n@ of all elements of @'Finite' n@.
finites :: forall n. KnownNat n => [Finite n]
finites = Finite <$> [0..natVal (Proxy @n) - 1]

-- | Same as 'finites' but with a proxy argument to avoid type signatures.
finitesProxy :: forall n proxy. KnownNat n => proxy n -> [Finite n]
finitesProxy _ = finites

-- | Test two different types of finite numbers for equality.
equals :: forall n m. Finite n -> Finite m -> Bool
equals (Finite x) (Finite y) = x == y
infix 4 `equals`

-- | Compare two different types of finite numbers.
cmp :: forall n m. Finite n -> Finite m -> Ordering
cmp (Finite x) (Finite y) = x `compare` y

-- | Convert a type-level literal into a 'Finite'.
natToFinite :: forall n m proxy. (KnownNat n, n + 1 <= m) => proxy n -> Finite m
natToFinite p = Finite $ natVal p

-- | Add one inhabitant in the end.
weaken :: forall n. Finite n -> Finite (n + 1)
weaken = weakenProxy (Proxy @1)

-- | Remove one inhabitant from the end. Returns 'Nothing' if the input was the removed inhabitant.
strengthen :: forall n. KnownNat n => Finite (n + 1) -> Maybe (Finite n)
strengthen = strengthenProxy (Proxy @1)

-- | Add one inhabitant in the beginning, shifting everything up by one.
shift :: forall n. Finite n -> Finite (n + 1)
shift = shiftProxy (Proxy @1)

-- | Remove one inhabitant from the beginning, shifting everything down by one. Returns 'Nothing' if the input was the removed inhabitant.
unshift :: forall n. Finite (n + 1) -> Maybe (Finite n)
unshift = unshiftProxy (Proxy @1)

-- m comes before n in the following because it's more likely the expanded size needs to be explict than the input size.
-- | Add multiple inhabitants in the end.
weakenN :: forall m n. n <= m => Finite n -> Finite m
weakenN (Finite x) = Finite x

-- | Remove multiple inhabitants from the end. Returns 'Nothing' if the input was one of the removed inhabitants.
strengthenN :: forall m n. (KnownNat n, n <= m) => Finite m -> Maybe (Finite n)
strengthenN (Finite x) = if x < natVal (Proxy @n)
                            then Just $ Finite x
                            else Nothing

-- | Add multiple inhabitant in the beginning, shifting everything up by the amount of inhabitants added.
shiftN :: forall m n. (KnownNat (m - n), n <= m) => Finite n -> Finite m
shiftN (Finite x) = Finite $ x + natVal (Proxy @(m - n))

-- | Remove multiple inhabitants from the beginning, shifting everything down by the amount of inhabitants removed. Returns 'Nothing' if the input was one of the removed inhabitants.
unshiftN :: forall m n. (KnownNat (m - n), n <= m) => Finite m -> Maybe (Finite n)
unshiftN (Finite x) = if x < natVal (Proxy @(m - n))
                         then Nothing
                         else Just $ Finite $ x - natVal (Proxy @(m - n))

addMeansGTE :: forall n k. (n <=? (n + k)) :~: True
addMeansGTE = unsafeCoerce Refl
addInvWithAdd :: forall n k. (n + k - n) :~: k
addInvWithAdd = unsafeCoerce Refl

weakenProxy :: forall k n proxy. proxy k -> Finite n -> Finite (n + k)
weakenProxy _ = case addMeansGTE @n @k of Refl -> weakenN

strengthenProxy :: forall n k proxy. KnownNat n => proxy k -> Finite (n + k) -> Maybe (Finite n)
strengthenProxy _ = case addMeansGTE @n @k of Refl -> strengthenN

shiftProxy :: forall n k proxy. KnownNat k => proxy k -> Finite n -> Finite (n + k)
shiftProxy _ = case (addMeansGTE @n @k, addInvWithAdd @n @k) of (Refl, Refl) -> shiftN

unshiftProxy :: forall n k proxy. KnownNat k => proxy k -> Finite (n + k) -> Maybe (Finite n)
unshiftProxy _ = case (addMeansGTE @n @k, addInvWithAdd @n @k) of (Refl, Refl) -> unshiftN

-- | Add two 'Finite's.
add :: forall n m. Finite n -> Finite m -> Finite (n + m - 1)
add (Finite x) (Finite y) = Finite $ x + y

-- | Subtract two 'Finite's. Returns 'Left' for negative results, and 'Right' for positive results. Note that this function never returns @'Left' 0@.
sub :: Finite n -> Finite m -> Either (Finite m) (Finite n)
sub (Finite x) (Finite y) = if x >= y
    then Right $ Finite $ x - y
    else Left $ Finite $ y - x

-- | Multiply two 'Finite's.
multiply :: Finite n -> Finite m -> Finite ((n - 1) * (m - 1) + 1)
multiply (Finite x) (Finite y) = Finite $ x * y

-- | 'Left'-biased (left values come first) disjoint union of finite sets.
combineSum :: forall l r. KnownNat l => Either (Finite l) (Finite r) -> Finite (l + r)
combineSum (Left  (Finite l)) = Finite l
combineSum (Right (Finite r)) = Finite $ r + natVal (Proxy @l)

-- | 'fst'-biased (fst is the inner, and snd is the outer iteratee) product of finite sets.
combineProduct :: forall l r. KnownNat l => (Finite l, Finite r) -> Finite (l * r)
combineProduct (Finite l, Finite r) = Finite $ l + r * natVal (Proxy @l)

-- | Take a 'Left'-biased disjoint union apart.
separateSum :: forall l r. KnownNat l => Finite (l + r) -> Either (Finite l) (Finite r)
separateSum (Finite x) = if x >= natVal (Proxy @l)
                            then Right $ Finite $ x - natVal (Proxy @l)
                            else Left $ Finite x

-- | Take a 'fst'-biased product apart.
separateProduct :: forall l r. KnownNat l => Finite (l * r) -> (Finite l, Finite r)
separateProduct (Finite x) = (Finite fst, Finite snd)
  where (fst, snd) = x `quotRem` natVal (Proxy @l)

-- | Witness to the fact that @'Finite' 0@ has no values.
finite0Absurd :: forall a. Finite 0 -> a
finite0Absurd f@(Finite _) = error $ "finite0Absurd: impossible; called with " ++ show f

-- | Representation of the unknown type-level number inside a @'Finite' n@
data FiniteNat n = forall m. (m + 1 <= n, KnownNat m) => FiniteNat (Proxy m)
-- | Witness to the fact that a @'Finite' n@ contains some number @m@ where @0 <= m < n@.
finiteNatVal :: forall n. Finite n -> FiniteNat n
finiteNatVal f@(Finite m) = case someNatVal m of
                                 Just (SomeNat (p :: Proxy m)) -> case unsafeCoerce Refl :: ((m + 1) <=? n) :~: True of Refl -> FiniteNat p
                                 Nothing -> error $ "finiteNatVal: impossible negative " ++ show f

-- | Verifies that a given 'Finite' is valid. Should always return 'True' unles you bring the @Data.Finite.Internal.Finite@ constructor into the scope, or use 'Unsafe.Coerce.unsafeCoerce' or other nasty hacks
isValidFinite :: forall n. KnownNat n => Finite n -> Bool
isValidFinite (Finite x) = x < natVal (Proxy @n) && x >= 0
