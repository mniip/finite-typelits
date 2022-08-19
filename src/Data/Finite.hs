--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite
-- Copyright   :  (C) 2015-2022 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Finite
    (
        Finite,
        packFinite, packFiniteProxy,
        finite, finiteProxy,
        getFinite, finites, finitesProxy,
        modulo, moduloProxy,
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

import Data.Coerce
import Data.Proxy
import GHC.TypeLits

import Data.Finite.Internal

-- | Convert an 'Integer' into a 'Finite', returning 'Nothing' if the input is
-- out of bounds.
packFinite :: forall n. KnownNat n => Integer -> Maybe (Finite n)
packFinite x
    | x < n && x >= 0 = Just $ Finite x
    | otherwise = Nothing
    where n = natVal (Proxy :: Proxy n)

-- | Same as 'packFinite' but with a proxy argument to avoid type signatures.
packFiniteProxy
    :: forall n proxy. KnownNat n
    => proxy n -> Integer -> Maybe (Finite n)
packFiniteProxy _ = packFinite

-- | Same as 'finite' but with a proxy argument to avoid type signatures.
finiteProxy :: forall n proxy. KnownNat n => proxy n -> Integer -> Finite n
finiteProxy _ = finite

-- | Generate a list of length @n@ of all elements of @'Finite' n@.
finites :: forall n. KnownNat n => [Finite n]
finites = Finite `fmap` [0 .. n - 1]
    where n = natVal (Proxy :: Proxy n)

-- | Same as 'finites' but with a proxy argument to avoid type signatures.
finitesProxy :: forall n proxy. KnownNat n => proxy n -> [Finite n]
finitesProxy _ = finites

-- | Produce the 'Finite' that is congruent to the given integer modulo @n@.
modulo :: forall n. KnownNat n => Integer -> Finite n
modulo x
    | n == 0 = error "modulo: division by zero"
    | otherwise = Finite $ x `mod` n
    where n = natVal (Proxy :: Proxy n)

-- | Same as 'modulo' but with a proxy argument to avoid type signatures.
moduloProxy :: forall n proxy. KnownNat n => proxy n -> Integer -> Finite n
moduloProxy _ = modulo

-- | Test two different types of finite numbers for equality.
equals :: forall n m. Finite n -> Finite m -> Bool
equals = coerce ((==) :: Integer -> Integer -> Bool)
infix 4 `equals`

-- | Compare two different types of finite numbers.
cmp :: forall n m. Finite n -> Finite m -> Ordering
cmp = coerce (compare :: Integer -> Integer -> Ordering)

-- | Convert a type-level literal into a 'Finite'.
natToFinite
    :: forall n m proxy. (KnownNat n, KnownNat m, n + 1 <= m)
    => proxy n -> Finite m
natToFinite p = Finite $ natVal p

-- | Add one inhabitant in the end.
weaken :: forall n. Finite n -> Finite (n + 1)
weaken = coerce

-- | Remove one inhabitant from the end. Returns 'Nothing' if the input was the
-- removed inhabitant.
strengthen :: forall n. KnownNat n => Finite (n + 1) -> Maybe (Finite n)
strengthen (Finite x)
    | x < n = Just $ Finite x
    | otherwise = Nothing
    where n = natVal (Proxy :: Proxy n)

-- | Add one inhabitant in the beginning, shifting everything up by one.
shift :: forall n. Finite n -> Finite (n + 1)
shift (Finite x) = Finite $ x + 1

-- | Remove one inhabitant from the beginning, shifting everything down by one.
-- Returns 'Nothing' if the input was the removed inhabitant.
unshift :: forall n. Finite (n + 1) -> Maybe (Finite n)
unshift (Finite x)
    | x < 1 = Nothing
    | otherwise = Just $ Finite $ x - 1

-- | Add multiple inhabitants in the end.
weakenN :: forall n m. (n <= m) => Finite n -> Finite m
weakenN = coerce

-- | Remove multiple inhabitants from the end. Returns 'Nothing' if the input
-- was one of the removed inhabitants.
strengthenN :: forall n m. KnownNat m => Finite n -> Maybe (Finite m)
strengthenN (Finite x)
    | x < m = Just $ Finite x
    | otherwise = Nothing
    where m = natVal (Proxy :: Proxy m)

-- | Add multiple inhabitants in the beginning, shifting everything up by the
-- amount of inhabitants added.
shiftN :: forall n m. (KnownNat n, KnownNat m, n <= m) => Finite n -> Finite m
shiftN (Finite x) = Finite $ x - n + m
    where
        n = natVal (Proxy :: Proxy n)
        m = natVal (Proxy :: Proxy m)

-- | Remove multiple inhabitants from the beginning, shifting everything down by
-- the amount of inhabitants removed. Returns 'Nothing' if the input was one of
-- the removed inhabitants.
unshiftN :: forall n m. (KnownNat n, KnownNat m) => Finite n -> Maybe (Finite m)
unshiftN (Finite x)
    | x < n - m = Nothing
    | otherwise = Just $ Finite $ x - n + m
    where
        n = natVal (Proxy :: Proxy n)
        m = natVal (Proxy :: Proxy m)

weakenProxy :: forall n k proxy. proxy k -> Finite n -> Finite (n + k)
weakenProxy _ = coerce

strengthenProxy
    :: forall n k proxy. KnownNat n
    => proxy k -> Finite (n + k) -> Maybe (Finite n)
strengthenProxy _ (Finite x)
    | x < n = Just $ Finite x
    | otherwise = Nothing
    where n = natVal (Proxy :: Proxy n)

shiftProxy
    :: forall n k proxy. KnownNat k
    => proxy k -> Finite n -> Finite (n + k)
shiftProxy _ (Finite x) = Finite $ x + k
    where k = natVal (Proxy :: Proxy k)

unshiftProxy
    :: forall n k proxy. KnownNat k
    => proxy k -> Finite (n + k) -> Maybe (Finite n)
unshiftProxy _ (Finite x)
    | x < k = Nothing
    | otherwise = Just $ Finite $ x - k
    where k = natVal (Proxy :: Proxy k)

-- | Add two 'Finite's.
add :: forall n m. Finite n -> Finite m -> Finite (n + m)
add (Finite x) (Finite y) = Finite $ x + y

-- | Subtract two 'Finite's. Returns 'Left' for negative results, and 'Right'
-- for positive results. Note that this function never returns @'Left' 0@.
sub :: forall n m. Finite n -> Finite m -> Either (Finite m) (Finite n)
sub (Finite x) (Finite y)
    | x >= y = Right $ Finite $ x - y
    | otherwise = Left $ Finite $ y - x

-- | Multiply two 'Finite's.
multiply :: forall n m. Finite n -> Finite m -> Finite (n GHC.TypeLits.* m)
multiply (Finite x) (Finite y) = Finite $ x * y

-- | 'Left'-biased (left values come first) disjoint union of finite sets.
combineSum
    :: forall n m. KnownNat n
    => Either (Finite n) (Finite m) -> Finite (n + m)
combineSum (Left (Finite x)) = Finite x
combineSum (Right (Finite x)) = Finite $ x + n
    where n = natVal (Proxy :: Proxy n)

-- | 'fst'-biased (fst is the inner, and snd is the outer iteratee) product of
-- finite sets.
combineProduct
    :: forall n m. KnownNat n
    => (Finite n, Finite m) -> Finite (n GHC.TypeLits.* m)
combineProduct (Finite x, Finite y) = Finite $ x + y * n
    where n = natVal (Proxy :: Proxy n)

-- | Take a 'Left'-biased disjoint union apart.
separateSum
    :: forall n m. KnownNat n
    => Finite (n + m) -> Either (Finite n) (Finite m)
separateSum (Finite x)
    | x >= n = Right $ Finite $ x - n
    | otherwise = Left $ Finite x
    where n = natVal (Proxy :: Proxy n)

-- | Take a 'fst'-biased product apart.
separateProduct
    :: forall n m. KnownNat n
    => Finite (n GHC.TypeLits.* m) -> (Finite n, Finite m)
separateProduct (Finite x) = (Finite $ x `mod` n, Finite $ x `div` n)
    where n = natVal (Proxy :: Proxy n)

-- | Verifies that a given 'Finite' is valid. Should always return 'True' unless
-- you bring the @Data.Finite.Internal.Finite@ constructor into the scope, or
-- use 'Unsafe.Coerce.unsafeCoerce' or other nasty hacks.
isValidFinite :: forall n. KnownNat n => Finite n -> Bool
isValidFinite (Finite x) = x < n && x >= 0
    where n = natVal (Proxy :: Proxy n)
