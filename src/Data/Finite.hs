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
        combineSum, combineZero, combineProduct, combineOne, combineExponential,
        separateSum, separateZero, separateProduct, separateOne,
        separateExponential,
        isValidFinite
    )
    where

import GHC.TypeLits
import Data.Void

import qualified Data.Finite.Integral as I
import Data.Finite.Internal

-- | Convert an 'Integer' into a 'Finite', returning 'Nothing' if the input is
-- out of bounds.
packFinite :: forall n. KnownNat n => Integer -> Maybe (Finite n)
packFinite = I.packFinite

-- | Same as 'packFinite' but with a proxy argument to avoid type signatures.
packFiniteProxy
    :: forall n proxy. KnownNat n
    => proxy n -> Integer -> Maybe (Finite n)
packFiniteProxy = I.packFiniteProxy

-- | Same as 'finite' but with a proxy argument to avoid type signatures.
finiteProxy :: forall n proxy. KnownNat n => proxy n -> Integer -> Finite n
finiteProxy = I.finiteProxy

-- | Generate a list of length @n@ of all elements of @'Finite' n@.
finites :: forall n. KnownNat n => [Finite n]
finites = I.finites

-- | Same as 'finites' but with a proxy argument to avoid type signatures.
finitesProxy :: forall n proxy. KnownNat n => proxy n -> [Finite n]
finitesProxy = I.finitesProxy

-- | Produce the 'Finite' that is congruent to the given integer modulo @n@.
modulo :: forall n. KnownNat n => Integer -> Finite n
modulo = I.modulo

-- | Same as 'modulo' but with a proxy argument to avoid type signatures.
moduloProxy :: forall n proxy. KnownNat n => proxy n -> Integer -> Finite n
moduloProxy = I.moduloProxy

-- | Test two different types of finite numbers for equality.
equals :: forall n m. Finite n -> Finite m -> Bool
equals = I.equals
infix 4 `equals`

-- | Compare two different types of finite numbers.
cmp :: forall n m. Finite n -> Finite m -> Ordering
cmp = I.cmp

-- | Convert a type-level literal into a 'Finite'.
natToFinite
    :: forall n m proxy. (KnownNat n, KnownNat m, n + 1 <= m)
    => proxy n -> Finite m
natToFinite = I.natToFinite

-- | Add one inhabitant in the end.
weaken :: forall n. Finite n -> Finite (n + 1)
weaken = I.weaken

-- | Remove one inhabitant from the end. Returns 'Nothing' if the input was the
-- removed inhabitant.
strengthen :: forall n. KnownNat n => Finite (n + 1) -> Maybe (Finite n)
strengthen = I.strengthen

-- | Add one inhabitant in the beginning, shifting everything up by one.
shift :: forall n. Finite n -> Finite (n + 1)
shift = I.shift

-- | Remove one inhabitant from the beginning, shifting everything down by one.
-- Returns 'Nothing' if the input was the removed inhabitant.
unshift :: forall n. Finite (n + 1) -> Maybe (Finite n)
unshift = I.unshift

-- | Add multiple inhabitants in the end.
weakenN :: forall n m. (n <= m) => Finite n -> Finite m
weakenN = I.weakenN

-- | Remove multiple inhabitants from the end. Returns 'Nothing' if the input
-- was one of the removed inhabitants.
strengthenN :: forall n m. KnownNat m => Finite n -> Maybe (Finite m)
strengthenN = I.strengthenN

-- | Add multiple inhabitants in the beginning, shifting everything up by the
-- amount of inhabitants added.
shiftN :: forall n m. (KnownNat n, KnownNat m, n <= m) => Finite n -> Finite m
shiftN = I.shiftN

-- | Remove multiple inhabitants from the beginning, shifting everything down by
-- the amount of inhabitants removed. Returns 'Nothing' if the input was one of
-- the removed inhabitants.
unshiftN :: forall n m. (KnownNat n, KnownNat m) => Finite n -> Maybe (Finite m)
unshiftN = I.unshiftN

weakenProxy :: forall n k proxy. proxy k -> Finite n -> Finite (n + k)
weakenProxy = I.weakenProxy

strengthenProxy
    :: forall n k proxy. KnownNat n
    => proxy k -> Finite (n + k) -> Maybe (Finite n)
strengthenProxy = I.strengthenProxy

shiftProxy
    :: forall n k proxy. KnownNat k
    => proxy k -> Finite n -> Finite (n + k)
shiftProxy = I.shiftProxy

unshiftProxy
    :: forall n k proxy. KnownNat k
    => proxy k -> Finite (n + k) -> Maybe (Finite n)
unshiftProxy = I.unshiftProxy

-- | Add two 'Finite's.
add :: forall n m. Finite n -> Finite m -> Finite (n + m)
add = I.add

-- | Subtract two 'Finite's. Returns 'Left' for negative results, and 'Right'
-- for positive results. Note that this function never returns @'Left' 0@.
sub :: forall n m. Finite n -> Finite m -> Either (Finite m) (Finite n)
sub = I.sub

-- | Multiply two 'Finite's.
multiply :: forall n m. Finite n -> Finite m -> Finite (n GHC.TypeLits.* m)
multiply = I.multiply

-- | 'Left'-biased (left values come first) disjoint union of finite sets.
combineSum
    :: forall n m. KnownNat n
    => Either (Finite n) (Finite m) -> Finite (n + m)
combineSum = I.combineSum

-- | Witness that 'combineSum' preserves units: @0@ is the unit of
-- 'GHC.TypeLits.+', and 'Void' is the unit of 'Either'.
combineZero :: Void -> Finite 0
combineZero = I.combineZero

-- | 'fst'-biased (fst is the inner, and snd is the outer iteratee) product of
-- finite sets.
combineProduct
    :: forall n m. KnownNat n
    => (Finite n, Finite m) -> Finite (n GHC.TypeLits.* m)
combineProduct = I.combineProduct

-- | Witness that 'combineProduct' preserves units: @1@ is the unit of
-- 'GHC.TypeLits.*', and '()' is the unit of '(,)'.
combineOne :: () -> Finite 1
combineOne = I.combineOne

-- | Product of @n@ copies of a finite set of size @m@, biased towards the lower
-- values of the argument (colex order).
combineExponential
    :: forall n m. (KnownNat m, KnownNat n)
    => (Finite n -> Finite m) -> Finite (m ^ n)
combineExponential = I.combineExponential

-- | Take a 'Left'-biased disjoint union apart.
separateSum
    :: forall n m. KnownNat n
    => Finite (n + m) -> Either (Finite n) (Finite m)
separateSum = I.separateSum

-- | Witness that 'separateSum' preserves units: @0@ is the unit of
-- 'GHC.TypeLits.+', and 'Void' is the unit of 'Either'.
--
-- Also witness that a @'Finite' 0@ is uninhabited.
separateZero :: Finite 0 -> Void
separateZero = I.separateZero

-- | Take a 'fst'-biased product apart.
separateProduct
    :: forall n m. KnownNat n
    => Finite (n GHC.TypeLits.* m) -> (Finite n, Finite m)
separateProduct = I.separateProduct

separateOne :: Finite 1 -> ()
separateOne = I.separateOne

-- | Take a product of @n@ copies of a finite set of size @m@ apart, biased
-- towards the lower values of the argument (colex order).
separateExponential
    :: forall n m. KnownNat m
    => Finite (m ^ n) -> Finite n -> Finite m
separateExponential = I.separateExponential

-- | Verifies that a given 'Finite' is valid. Should always return 'True' unless
-- you bring the @Data.Finite.Internal.Finite@ constructor into the scope, or
-- use 'Unsafe.Coerce.unsafeCoerce' or other nasty hacks.
isValidFinite :: forall n. KnownNat n => Finite n -> Bool
isValidFinite = I.isValidFinite
