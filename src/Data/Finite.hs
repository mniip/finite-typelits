--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite
-- Copyright   :  (C) 2015 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE TypeOperators, DataKinds, TypeFamilies, FlexibleContexts #-}
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
        isValidFinite
    )
    where

import Data.Maybe
import GHC.TypeLits

import Data.Finite.Internal

-- | Convert an 'Integer' into a 'Finite', returning 'Nothing' if the input is out of bounds.
packFinite :: KnownNat n => Integer -> Maybe (Finite n)
packFinite x = result
    where
        result = if x < natVal (fromJust result) && x >= 0
            then Just $ Finite x
            else Nothing

-- | Same as 'packFinite' but with a proxy argument to avoid type signatures.
packFiniteProxy :: KnownNat n => proxy n -> Integer -> Maybe (Finite n)
packFiniteProxy _ = packFinite

-- | Same as 'finite' but with a proxy argument to avoid type signatures.
finiteProxy :: KnownNat n => proxy n -> Integer -> Finite n
finiteProxy _ = finite

-- | Generate a list of length @n@ of all elements of @'Finite' n@.
finites :: KnownNat n => [Finite n]
finites = results
  where
    results = Finite <$> [0 .. (natVal (head results) - 1)]

-- | Same as 'finites' but with a proxy argument to avoid type signatures.
finitesProxy :: KnownNat n => proxy n -> [Finite n]
finitesProxy _ = finites

-- | Test two different types of finite numbers for equality.
equals :: Finite n -> Finite m -> Bool
equals (Finite x) (Finite y) = x == y
infix 4 `equals`

-- | Compare two different types of finite numbers.
cmp :: Finite n -> Finite m -> Ordering
cmp (Finite x) (Finite y) = x `compare` y

-- | Convert a type-level literal into a 'Finite'.
natToFinite :: (KnownNat n, KnownNat m, n + 1 <= m) => proxy n -> Finite m
natToFinite p = Finite $ natVal p

-- | Add one inhabitant in the end.
weaken :: Finite n -> Finite (n + 1)
weaken (Finite x) = Finite x

-- | Remove one inhabitant from the end. Returns 'Nothing' if the input was the removed inhabitant.
strengthen :: KnownNat n => Finite (n + 1) -> Maybe (Finite n)
strengthen (Finite x) = result
    where
        result = if x < natVal (fromJust result)
            then Just $ Finite x
            else Nothing

-- | Add one inhabitant in the beginning, shifting everything up by one.
shift :: Finite n -> Finite (n + 1)
shift (Finite x) = Finite (x + 1)

-- | Remove one inhabitant from the beginning, shifting everything down by one. Returns 'Nothing' if the input was the removed inhabitant.
unshift :: Finite (n + 1) -> Maybe (Finite n)
unshift (Finite x) = if x < 1
    then Nothing
    else Just $ Finite $ x - 1

-- | Add multiple inhabitants in the end.
weakenN :: (n <= m) => Finite n -> Finite m
weakenN (Finite x) = Finite x

-- | Remove multiple inhabitants from the end. Returns 'Nothing' if the input was one of the removed inhabitants.
strengthenN :: (KnownNat n, n <= m) => Finite m -> Maybe (Finite n)
strengthenN (Finite x) = result
    where
        result = if x < natVal (fromJust result)
            then Just $ Finite x
            else Nothing

-- | Add multiple inhabitant in the beginning, shifting everything up by the amount of inhabitants added.
shiftN :: (KnownNat n, KnownNat m, n <= m) => Finite n -> Finite m
shiftN fx@(Finite x) = result
    where
        result = Finite $ x + natVal result - natVal fx

-- | Remove multiple inhabitants from the beginning, shifting everything down by the amount of inhabitants removed. Returns 'Nothing' if the input was one of the removed inhabitants.
unshiftN :: (KnownNat n, KnownNat m, n <= m) => Finite m -> Maybe (Finite n)
unshiftN fx@(Finite x) = result
    where
        result = if x < natVal fx - natVal (fromJust result)
            then Nothing
            else Just $ Finite $ x - natVal fx + natVal (fromJust result)

weakenProxy :: proxy k -> Finite n -> Finite (n + k)
weakenProxy _ (Finite x) = Finite x

strengthenProxy :: KnownNat n => proxy k -> Finite (n + k) -> Maybe (Finite n)
strengthenProxy p (Finite x) = result
    where
        result = if x < natVal (fromJust result)
            then Just $ Finite x
            else Nothing

shiftProxy :: KnownNat k => proxy k -> Finite n -> Finite (n + k)
shiftProxy p (Finite x) = Finite $ x + natVal p

unshiftProxy :: KnownNat k => proxy k -> Finite (n + k) -> Maybe (Finite n)
unshiftProxy p (Finite x) = if x < natVal p
    then Nothing
    else Just $ Finite $ x - natVal p

-- | Add two 'Finite's.
add :: Finite n -> Finite m -> Finite (n + m)
add (Finite x) (Finite y) = Finite $ x + y

-- | Subtract two 'Finite's. Returns 'Left' for negative results, and 'Right' for positive results. Note that this function never returns @'Left' 0@.
sub :: Finite n -> Finite m -> Either (Finite m) (Finite n)
sub (Finite x) (Finite y) = if x >= y
    then Right $ Finite $ x - y
    else Left $ Finite $ y - x

-- | Multiply two 'Finite's.
multiply :: Finite n -> Finite m -> Finite (n * m)
multiply (Finite x) (Finite y) = Finite $ x * y

getLeftType :: Either a b -> a
getLeftType = error "getLeftType"

-- | 'Left'-biased (left values come first) disjoint union of finite sets.
combineSum :: KnownNat n => Either (Finite n) (Finite m) -> Finite (n + m)
combineSum (Left (Finite x)) = Finite x
combineSum efx@(Right (Finite x)) = Finite $ x + natVal (getLeftType efx)

-- | 'fst'-biased (fst is the inner, and snd is the outer iteratee) product of finite sets.
combineProduct :: KnownNat n => (Finite n, Finite m) -> Finite (n * m)
combineProduct (fx@(Finite x), Finite y) = Finite $ x + y * natVal fx

-- | Take a 'Left'-biased disjoint union apart.
separateSum :: KnownNat n => Finite (n + m) -> Either (Finite n) (Finite m)
separateSum (Finite x) = result
    where
        result = if x >= natVal (getLeftType result)
            then Right $ Finite $ x - natVal (getLeftType result)
            else Left $ Finite x

-- | Take a 'fst'-biased product apart.
separateProduct :: KnownNat n => Finite (n * m) -> (Finite n, Finite m)
separateProduct (Finite x) = result
    where
        result = (Finite $ x `mod` natVal (fst result), Finite $ x `div` natVal (fst result))

-- | Verifies that a given 'Finite' is valid. Should always return 'True' unles you bring the @Data.Finite.Internal.Finite@ constructor into the scope, or use 'Unsafe.Coerce.unsafeCoerce' or other nasty hacks
isValidFinite :: KnownNat n => Finite n -> Bool
isValidFinite fx@(Finite x) = x < natVal fx && x >= 0

-- | Interpret an 'Integer' as a member of a congruency class of @(`mod`
-- n)@
--
-- Essentially 'fromInteger' precomposed with 'mod'.
modClass :: KnownNat n => Integer -> Finite n
modClass x = result
  where
    result = Finite (x `mod` natVal result)
