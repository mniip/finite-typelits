--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite.Integral
-- Copyright   :  (C) 2015-2022 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Finite.Integral
    (
        SaneIntegral, Limited, KnownIntegral, intVal,
        withIntegral,
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
        combineSum, combineZero, combineProduct, combineOne, combineExponential,
        separateSum, separateZero, separateProduct, separateOne,
        separateExponential,
        isValidFinite
    )
    where

import Data.Coerce
import Data.List
import Data.Proxy
import Data.Void
import GHC.TypeLits

import Data.Finite.Internal.Integral

-- | Convert an @a@ into a @'Finite' a@, returning 'Nothing' if the input is
-- out of bounds.
packFinite
    :: forall n a. (SaneIntegral a, KnownIntegral a n)
    => a -> Maybe (Finite a n)
packFinite x
    | x < n && x >= 0 = Just $ Finite x
    | otherwise = Nothing
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE packFinite #-}

-- | Same as 'packFinite' but with a proxy argument to avoid type signatures.
packFiniteProxy
    :: forall n a proxy. (SaneIntegral a, KnownIntegral a n)
    => proxy n -> a -> Maybe (Finite a n)
packFiniteProxy _ = packFinite
{-# INLINABLE packFiniteProxy #-}

-- | Same as 'finite' but with a proxy argument to avoid type signatures.
finiteProxy
    :: forall n a proxy. (SaneIntegral a, KnownIntegral a n)
    => proxy n -> a -> Finite a n
finiteProxy _ = finite
{-# INLINABLE finiteProxy #-}

-- | Generate an ascending list of length @n@ of all elements of @'Finite' a n@.
finites :: forall n a. (SaneIntegral a, KnownIntegral a n) => [Finite a n]
finites = Finite `fmap` takeWhile (< n) [0..]
    -- [0 .. n - 1] does not work if n is 0 of an unsigned type
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE finites #-}

-- | Same as 'finites' but with a proxy argument to avoid type signatures.
finitesProxy
    :: forall n a proxy. (SaneIntegral a, KnownIntegral a n)
    => proxy n -> [Finite a n]
finitesProxy _ = finites
{-# INLINABLE finitesProxy #-}

-- | Produce the 'Finite' that is congruent to the given integer modulo @n@.
modulo :: forall n a. (SaneIntegral a, KnownIntegral a n) => a -> Finite a n
modulo x
    | n == 0 = error "modulo: division by zero"
    | otherwise = Finite $ x `mod` n
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE modulo #-}

-- | Same as 'modulo' but with a proxy argument to avoid type signatures.
moduloProxy
    :: forall n a proxy. (SaneIntegral a, KnownIntegral a n)
    => proxy n -> a -> Finite a n
moduloProxy _ = modulo
{-# INLINABLE moduloProxy #-}

-- | Test two different types of finite numbers for equality.
equals :: forall n m a. Eq a => Finite a n -> Finite a m -> Bool
equals = coerce ((==) :: a -> a -> Bool)
infix 4 `equals`
{-# INLINABLE equals #-}

-- | Compare two different types of finite numbers.
cmp :: forall n m a. Ord a => Finite a n -> Finite a m -> Ordering
cmp = coerce (compare :: a -> a -> Ordering)
{-# INLINABLE cmp #-}

-- | Convert a type-level literal into a 'Finite'.
natToFinite
    :: forall n m a proxy.
        (SaneIntegral a, KnownIntegral a n, Limited a m, n + 1 <= m)
    => proxy n -> Finite a m
natToFinite p = Finite $ intVal p
{-# INLINABLE natToFinite #-}

-- | Add one inhabitant in the end.
weaken :: forall n a. Limited a (n + 1) => Finite a n -> Finite a (n + 1)
weaken = coerce
{-# INLINABLE weaken #-}

-- | Remove one inhabitant from the end. Returns 'Nothing' if the input was the
-- removed inhabitant.
strengthen
    :: forall n a. (SaneIntegral a, KnownIntegral a n)
    => Finite a (n + 1) -> Maybe (Finite a n)
strengthen (Finite x)
    | x < n = Just $ Finite x
    | otherwise = Nothing
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE strengthen #-}

-- | Add one inhabitant in the beginning, shifting everything up by one.
shift
    :: forall n a. (SaneIntegral a, Limited a (n + 1))
    => Finite a n -> Finite a (n + 1)
shift (Finite x) = Finite $ x + 1
{-# INLINABLE shift #-}

-- | Remove one inhabitant from the beginning, shifting everything down by one.
-- Returns 'Nothing' if the input was the removed inhabitant.
unshift :: forall n a. SaneIntegral a => Finite a (n + 1) -> Maybe (Finite a n)
unshift (Finite x)
    | x < 1 = Nothing
    | otherwise = Just $ Finite $ x - 1
{-# INLINABLE unshift #-}

-- | Add multiple inhabitants in the end.
weakenN :: forall n m a. (n <= m, Limited a m) => Finite a n -> Finite a m
weakenN = coerce
{-# INLINABLE weakenN #-}

-- | Remove multiple inhabitants from the end. Returns 'Nothing' if the input
-- was one of the removed inhabitants.
strengthenN
    :: forall n m a. (SaneIntegral a, KnownIntegral a m, Limited a m)
    => Finite a n -> Maybe (Finite a m)
strengthenN (Finite x)
    | x < m = Just $ Finite x
    | otherwise = Nothing
    where m = intVal (Proxy :: Proxy m)
{-# INLINABLE strengthenN #-}

-- | Add multiple inhabitants in the beginning, shifting everything up by the
-- amount of inhabitants added.
shiftN
    :: forall n m a.
        ( SaneIntegral a
        , KnownIntegral a n
        , KnownIntegral a m
        , n <= m
        )
    => Finite a n -> Finite a m
shiftN (Finite x) = Finite $ x + (m - n)
    where
        n = intVal (Proxy :: Proxy n)
        m = intVal (Proxy :: Proxy m)
{-# INLINABLE shiftN #-}

-- | Remove multiple inhabitants from the beginning, shifting everything down by
-- the amount of inhabitants removed. Returns 'Nothing' if the input was one of
-- the removed inhabitants.
unshiftN
    :: forall n m a.
        (SaneIntegral a, KnownIntegral a n, KnownIntegral a m, Limited a m)
    => Finite a n -> Maybe (Finite a m)
unshiftN (Finite x)
    | m >= n = Just $ Finite $ x + (m - n)
    | x < n - m = Nothing
    | otherwise = Just $ Finite $ x - (n - m)
    where
        n = intVal (Proxy :: Proxy n)
        m = intVal (Proxy :: Proxy m)
{-# INLINABLE unshiftN #-}

weakenProxy
    :: forall n k a proxy. (Limited a (n + k))
    => proxy k -> Finite a n -> Finite a (n + k)
weakenProxy _ = coerce
{-# INLINABLE weakenProxy #-}

strengthenProxy
    :: forall n k a proxy. (SaneIntegral a, KnownIntegral a n)
    => proxy k -> Finite a (n + k) -> Maybe (Finite a n)
strengthenProxy _ (Finite x)
    | x < n = Just $ Finite x
    | otherwise = Nothing
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE strengthenProxy #-}

shiftProxy
    :: forall n k a proxy.
        (SaneIntegral a, KnownIntegral a k, Limited a (n + k))
    => proxy k -> Finite a n -> Finite a (n + k)
shiftProxy _ (Finite x) = Finite $ x + k
    where k = intVal (Proxy :: Proxy k)
{-# INLINABLE shiftProxy #-}

unshiftProxy
    :: forall n k a proxy. (SaneIntegral a, KnownIntegral a k)
    => proxy k -> Finite a (n + k) -> Maybe (Finite a n)
unshiftProxy _ (Finite x)
    | x < k = Nothing
    | otherwise = Just $ Finite $ x - k
    where k = intVal (Proxy :: Proxy k)
{-# INLINABLE unshiftProxy #-}

-- | Add two 'Finite's.
add
    :: forall n m a. (SaneIntegral a, Limited a (n + m))
    => Finite a n -> Finite a m -> Finite a (n + m)
add (Finite x) (Finite y) = Finite $ x + y
{-# INLINABLE add #-}

-- | Subtract two 'Finite's. Returns 'Left' for negative results, and 'Right'
-- for positive results. Note that this function never returns @'Left' 0@.
sub
    :: forall n m a. SaneIntegral a
    => Finite a n -> Finite a m -> Either (Finite a m) (Finite a n)
sub (Finite x) (Finite y)
    | x >= y = Right $ Finite $ x - y
    | otherwise = Left $ Finite $ y - x
{-# INLINABLE sub #-}

-- | Multiply two 'Finite's.
multiply
    :: forall n m a. (SaneIntegral a, Limited a (n GHC.TypeLits.* m))
    => Finite a n -> Finite a m -> Finite a (n GHC.TypeLits.* m)
multiply (Finite x) (Finite y) = Finite $ x * y
{-# INLINABLE multiply #-}

-- | 'Left'-biased (left values come first) disjoint union of finite sets.
combineSum
    :: forall n m a. (SaneIntegral a, KnownIntegral a n, Limited a (n + m))
    => Either (Finite a n) (Finite a m) -> Finite a (n + m)
combineSum (Left (Finite x)) = Finite x
combineSum (Right (Finite x)) = Finite $ x + n
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE combineSum #-}

-- | Witness that 'combineSum' preserves units: @0@ is the unit of
-- 'GHC.TypeLits.+', and 'Void' is the unit of 'Either'.
combineZero :: forall a. Void -> Finite a 0
combineZero = absurd
{-# INLINABLE combineZero #-}

-- | 'fst'-biased (fst is the inner, and snd is the outer iteratee) product of
-- finite sets.
combineProduct
    :: forall n m a.
        (SaneIntegral a, KnownIntegral a n, Limited a (n GHC.TypeLits.* m))
    => (Finite a n, Finite a m) -> Finite a (n GHC.TypeLits.* m)
combineProduct (Finite x, Finite y) = Finite $ x + y * n
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE combineProduct #-}

-- | Witness that 'combineProduct' preserves units: @1@ is the unit of
-- 'GHC.TypeLits.*', and '()' is the unit of '(,)'.
combineOne :: forall a. (SaneIntegral a, Limited a 1) => () -> Finite a 1
combineOne _ = Finite 0
{-# INLINABLE combineOne #-}

-- | Product of @n@ copies of a finite set of size @m@, biased towards the lower
-- values of the argument (colex order).
combineExponential
    :: forall n m a.
        (SaneIntegral a, KnownIntegral a m, KnownIntegral a n, Limited a (m ^ n))
    => (Finite a n -> Finite a m) -> Finite a (m ^ n)
combineExponential f
    = Finite $ fst $ foldl' next (0, 1) (finites :: [Finite a n])
    where
        next (acc, power) x = acc' `seq` (acc', m * power)
            where acc' = acc + getFinite (f x) * power
        m = intVal (Proxy :: Proxy m)
{-# INLINABLE combineExponential #-}

-- | Take a 'Left'-biased disjoint union apart.
separateSum
    :: forall n m a. (SaneIntegral a, KnownIntegral a n)
    => Finite a (n + m) -> Either (Finite a n) (Finite a m)
separateSum (Finite x)
    | x >= n = Right $ Finite $ x - n
    | otherwise = Left $ Finite x
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE separateSum #-}

-- | Witness that 'separateSum' preserves units: @0@ is the unit of
-- 'GHC.TypeLits.+', and 'Void' is the unit of 'Either'.
--
-- Also witness that a @'Finite' a 0@ is uninhabited.
separateZero :: forall a. SaneIntegral a => Finite a 0 -> Void
separateZero (Finite n) = n `seq` error
    ("separateZero: got Finite " <> show (toInteger n))
{-# INLINABLE separateZero #-}

-- | Take a 'fst'-biased product apart.
separateProduct
    :: forall n m a. (SaneIntegral a, KnownIntegral a n)
    => Finite a (n GHC.TypeLits.* m) -> (Finite a n, Finite a m)
separateProduct (Finite x) = case divMod x n of
    (d, m) -> (Finite m, Finite d)
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE separateProduct #-}

separateOne :: forall a. Finite a 1 -> ()
separateOne _ = ()
{-# INLINABLE separateOne #-}

-- | Take a product of @n@ copies of a finite set of size @m@ apart, biased
-- towards the lower values of the argument (colex order).
separateExponential
    :: forall n m a. (SaneIntegral a, KnownIntegral a m)
    => Finite a (m ^ n) -> Finite a n -> Finite a m
separateExponential = go
    where
        go (Finite n) (Finite 0) = Finite $ n `mod` m
        go (Finite n) (Finite x) = n' `seq` go (Finite n') (Finite $ x - 1)
            where n' = n `div` m
        m = intVal (Proxy :: Proxy m)
{-# INLINABLE separateExponential #-}

-- | Verifies that a given 'Finite' is valid. Should always return 'True' unless
-- you bring the @Data.Finite.Internal.Finite@ constructor into the scope, or
-- use 'Unsafe.Coerce.unsafeCoerce' or other nasty hacks.
isValidFinite
    :: forall n a. (Ord a, Num a, KnownIntegral a n)
    => Finite a n -> Bool
isValidFinite (Finite x) = x < n && x >= 0
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE isValidFinite #-}
