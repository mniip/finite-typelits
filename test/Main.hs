{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Control.Exception
import Control.DeepSeq
import Control.Monad
import Data.Bifunctor
import Data.Int
import Data.List
import Data.Maybe
import Data.Proxy
import Data.Type.Equality
import Data.Typeable
import Data.Void
import Data.Word
import GHC.TypeLits
import System.Exit
import Test.QuickCheck hiding (Small)
import Unsafe.Coerce
import Numeric.Natural

import Debug.Trace

import Data.Finite.Integral
import Data.Finite.Internal.Integral

newtype SmallNonNeg a = SmallNonNeg { getSmallNonNeg :: a }
    deriving (Show)

instance (Integral a, Arbitrary a) => Arbitrary (SmallNonNeg a) where
    arbitrary = SmallNonNeg <$> arbitrarySizedNatural
    shrink (SmallNonNeg x) = SmallNonNeg <$> shrink x

instance Arbitrary Natural where
    arbitrary = fromInteger . getNonNegative <$> arbitrary

instance CoArbitrary Natural where
    coarbitrary n = coarbitrary (toInteger n)

newtype Small a n = Small (Finite a n)
    deriving (Show)

newtype Big a n = Big (Finite a n)
    deriving (Show)

newtype Edgy a n = Edgy (Finite a n)
    deriving (Show)

instance
    (Arbitrary a, SaneIntegral a, KnownIntegral a n)
    => Arbitrary (Small a n) where
    arbitrary
        | intVal @n @a Proxy == 0 = discard
        | otherwise = Small . Finite . (`mod` n)
            . getSmallNonNeg <$> arbitrary
        where n = intVal @n Proxy
    shrink (Small (Finite x)) = Small <$> mapMaybe packFinite (shrink x)

instance
    (Arbitrary a, SaneIntegral a, KnownIntegral a n)
    => Arbitrary (Big a n) where
    arbitrary
        | intVal @n @a Proxy == 0 = discard
        | otherwise = Big . Finite . ((n - 1) -) . (`mod` n)
            . getSmallNonNeg <$> arbitrary
        where n = intVal @n Proxy
    shrink (Big (Finite x)) = Big <$> mapMaybe packFinite (shrink x)

instance CoArbitrary a => CoArbitrary (Big a n) where
    coarbitrary (Big (Finite x)) = coarbitrary x

instance
    (Arbitrary a, SaneIntegral a, KnownIntegral a n)
    => Arbitrary (Edgy a n) where
    arbitrary
        | intVal @n @a Proxy == 0 = discard
        | otherwise = Edgy . Finite <$> oneof
            [ (`mod` n) . getSmallNonNeg <$> arbitrary
            , ((n - 1) -) . (`mod` n) . getSmallNonNeg <$> arbitrary
            ]
        where n = intVal @n Proxy
    shrink (Edgy (Finite x)) = Edgy <$> mapMaybe packFinite (shrink x)

data SLimited a where
    SLimited :: (Limited a n, KnownNat n) => Proxy n -> SLimited a

mkLimited
    :: forall a lim. (Limit a ~ 'Just lim, KnownNat lim)
    => Integer -> Maybe (SLimited a)
mkLimited n = case someNatVal n of
    Just (SomeNat (p :: Proxy b))
        | n <= natVal @lim Proxy
        , Refl :: (b <=? lim) :~: 'True <- unsafeCoerce Refl
        -> Just $ SLimited p
    _ -> Nothing

mkUnlimited
    :: forall a. Limit a ~ 'Nothing
    => Integer -> Maybe (SLimited a)
mkUnlimited n = case someNatVal n of
    Just (SomeNat p) -> Just $ SLimited p
    _ -> Nothing

genSmall, genOver7, genOver8, genOver15, genOver16, genOver31, genOver32,
    genOver63, genOver64, genOverI, genOverW, genUnder7, genUnder8, genUnder15,
    genUnder16, genUnder32, genUnder63, genUnder64, genUnderI, genUnderW
    :: Gen Integer
genSmall = getNonNegative <$> arbitrary
genOver7 = (toInteger (maxBound @Int8) +) <$> genSmall
genOver8 = (toInteger (maxBound @Word8) +) <$> genSmall
genOver15 = (toInteger (maxBound @Int16) +) <$> genSmall
genOver16 = (toInteger (maxBound @Word16) +) <$> genSmall
genOver31 = (toInteger (maxBound @Int32) +) <$> genSmall
genOver32 = (toInteger (maxBound @Word32) +) <$> genSmall
genOver63 = (toInteger (maxBound @Int64) +) <$> genSmall
genOver64 = (toInteger (maxBound @Word64) +) <$> genSmall
genOverI = (toInteger (maxBound @Int) +) <$> genSmall
genOverW = (toInteger (maxBound @Word) +) <$> genSmall
genUnder7 = ((toInteger (maxBound @Int8) -) <$> genSmall) `suchThat` (>= 0)
genUnder8 = ((toInteger (maxBound @Word8) -) <$> genSmall) `suchThat` (>= 0)
genUnder15 = ((toInteger (maxBound @Int16) -) <$> genSmall) `suchThat` (>= 0)
genUnder16 = ((toInteger (maxBound @Word16) -) <$> genSmall) `suchThat` (>= 0)
genUnder31 = ((toInteger (maxBound @Int32) -) <$> genSmall) `suchThat` (>= 0)
genUnder32 = ((toInteger (maxBound @Word32) -) <$> genSmall) `suchThat` (>= 0)
genUnder63 = ((toInteger (maxBound @Int64) -) <$> genSmall) `suchThat` (>= 0)
genUnder64 = ((toInteger (maxBound @Word64) -) <$> genSmall) `suchThat` (>= 0)
genUnderI = ((toInteger (maxBound @Int) -) <$> genSmall) `suchThat` (>= 0)
genUnderW = ((toInteger (maxBound @Word) -) <$> genSmall) `suchThat` (>= 0)

instance Arbitrary (SLimited Integer) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32
        , genOver32, genUnder63, genOver63, genUnder64, genOver64, genUnderI
        , genOverI, genUnderW, genOverW ]
        `suchThatMap` mkUnlimited
    shrink (SLimited p) = mapMaybe mkUnlimited $ shrink $ natVal p

instance Arbitrary (SLimited Natural) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32
        , genOver32, genUnder63, genOver63, genUnder64, genOver64, genUnderI
        , genOverI, genUnderW, genOverW ]
        `suchThatMap` mkUnlimited
    shrink (SLimited p) = mapMaybe mkUnlimited $ shrink $ natVal p

instance Arbitrary (SLimited Word) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32
        , genOver32, genUnder63, genOver63, genUnder64, genOver64, genUnderI
        , genOverI, genUnderW ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Int) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32
        , genOver32, genUnder63, genOver63, genUnder64, genOver64, genUnderI ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Word8) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8 ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Int8) where
    arbitrary = oneof
        [ genSmall, genUnder7 ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Word16) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16 ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Int16) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15 ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Word32) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32 ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Int32) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31 ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Word64) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32
        , genOver32, genUnder63, genOver63, genUnder64, genOverI, genUnderW
        , genOverW ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

instance Arbitrary (SLimited Int64) where
    arbitrary = oneof
        [ genSmall, genUnder7, genOver7, genUnder8, genOver8, genUnder15
        , genOver15, genUnder16, genOver16, genUnder31, genOver31, genUnder32
        , genOver32, genUnder63, genUnderI, genOverI, genUnderW, genOverW ]
        `suchThatMap` mkLimited
    shrink (SLimited p) = mapMaybe mkLimited $ shrink $ natVal p

newtype SmallLimited a = SmallLimited { getSmallLimited :: SLimited a }

instance Arbitrary (SmallLimited Integer) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkUnlimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Natural) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkUnlimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Word) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Int) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Word8) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Int8) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Word16) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Int16) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Word32) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Int32) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Word64) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

instance Arbitrary (SmallLimited Int64) where
    arbitrary = SmallLimited <$> genSmall `suchThatMap` mkLimited
    shrink = map SmallLimited . shrink . getSmallLimited

type Good a =
    ( Show a
    , Read a
    , NFData a
    , Typeable a
    , SaneIntegral a
    , Arbitrary a
    , Arbitrary (SLimited a)
    , Arbitrary (SmallLimited a)
    , CoArbitrary a
    )

data SType where
    SType :: Good a => Proxy a -> SType

forType :: forall prop. Testable prop
    => (forall a. Good a => Proxy a -> prop)
    -> Property
forType prop = forAllBlind gen $ \case
    (name, SType p) -> counterexample @prop ("@" ++ name) $ prop p
    where
        gen = elements
            [ ("Integer", SType @Integer Proxy)
            , ("Natural", SType @Natural Proxy)
            , ("Word", SType @Word Proxy)
            , ("Int", SType @Int Proxy)
            , ("Word8", SType @Word8 Proxy)
            , ("Int8", SType @Int8 Proxy)
            , ("Word16", SType @Word16 Proxy)
            , ("Int16", SType @Int16 Proxy)
            , ("Word32", SType @Word32 Proxy)
            , ("Int32", SType @Int32 Proxy)
            , ("Word64", SType @Word64 Proxy)
            , ("Int64", SType @Int64 Proxy)
            ]

forLimit'
    :: forall a. SaneIntegral a
    => Gen (SLimited a)
    -> (SLimited a -> [SLimited a])
    -> (forall n. (KnownIntegral a n, Limited a n)
        => (forall i. Num i => i) -> Proxy n -> Property)
    -> Property
forLimit' gen shr prop = forAllShrinkBlind @Property gen shr $ \case
    SLimited p -> counterexample ("@" ++ show (natVal p)) $
        prop (fromInteger $ natVal p) p

forLimit
    :: forall a. (SaneIntegral a, Arbitrary (SLimited a))
    => (forall n. (KnownIntegral a n, Limited a n)
        => (forall i. Num i => i) -> Proxy n -> Property)
    -> Property
forLimit = forLimit' @a arbitrary shrink


forPositiveLimit
    :: forall a. (SaneIntegral a, Arbitrary (SLimited a))
    => (forall n. (KnownIntegral a n, Limited a n)
        => (forall i. Num i => i) -> Proxy n -> Property)
    -> Property
forPositiveLimit = forLimit' @a
    (arbitrary `suchThat` isPositive)
    (filter isPositive . shrink)
    where
        isPositive :: SLimited a -> Bool
        isPositive (SLimited p) = natVal p > 0

forSmallLimit
    :: forall a. (SaneIntegral a, Arbitrary (SmallLimited a))
    => (forall n. (KnownIntegral a n, Limited a n)
        => (forall i. Num i => i) -> Proxy n -> Property)
    -> Property
forSmallLimit = forLimit' @a
    (getSmallLimited <$> arbitrary)
    (map getSmallLimited . shrink . SmallLimited)

unsafeWithKnownIntegral
    :: forall n a. (SaneIntegral a, Typeable a)
    => Integer -> ((KnownNat n, Limited a n) => Property) -> Property
unsafeWithKnownIntegral n prop
    | Just (Refl :: a :~: Integer) <- cast (Refl @a)
    , Just (SLimited (_ :: Proxy n')) <- mkUnlimited @a n
    , Refl <- unsafeCoerce Refl :: n :~: n'
    = prop
    | Just (Refl :: a :~: Natural) <- cast (Refl @a)
    , Just (SLimited (_ :: Proxy n')) <- mkUnlimited @a n
    , Refl <- unsafeCoerce Refl :: n :~: n'
    = prop
    | Just (Refl :: a :~: Word) <- cast (Refl @a)
    , Just (SLimited (_ :: Proxy n')) <- mkLimited @a n
    , Refl <- unsafeCoerce Refl :: n :~: n'
    = prop
    | Just (Refl :: a :~: Int) <- cast (Refl @a)
    , Just (SLimited (_ :: Proxy n')) <- mkLimited @a n
    , Refl <- unsafeCoerce Refl :: n :~: n'
    = prop
    | otherwise = discard

newtype IneqCond (n :: Nat) (m :: Nat) = IneqCond ((n <= m) => Property)
unsafeWithInequality
    :: forall (n :: Nat) (m :: Nat). ((n <= m) => Property) -> Property
unsafeWithInequality prop =
    case unsafeCoerce (IneqCond @n @m $ property prop) :: IneqCond 0 1 of
        IneqCond prop' -> prop'

prop_isvalid_under = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x ->
    x < 0 ==> not $ isValidFinite @n @a (Finite x)
prop_isvalid_over = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    property $ \x ->
    not (x >= n) .||. not (isValidFinite @n @a (Finite x))

prop_valid_finite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    evaluate (isValidFinite $ finite @n @a x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_getFinite_finite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    evaluate (getFinite (finite @n @a x) == x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_finite_getFinite = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    finite (getFinite x) === x

prop_valid_maxBound = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    n > 0 ==> isValidFinite (maxBound @(Finite a n))
prop_maxBound_max = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    n > 0 ==> maxBound >= x

prop_valid_minBound = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    n > 0 ==> isValidFinite (minBound @(Finite a n))
prop_minBound_min = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    n > 0 ==> minBound <= x

prop_valid_toEnum = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    evaluate (isValidFinite $ toEnum @(Finite a n) x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_fromEnum_toEnum = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    evaluate (fromEnum (toEnum @(Finite a n) x) == x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_toEnum_fromEnum = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    n <= toInteger (maxBound @Int) ==> toEnum (fromEnum x) == x

prop_valid_enumFrom = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) ->
    all isValidFinite [x..]
prop_getFinite_enumFrom = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) ->
    map getFinite [x..]
        === takeWhile (isJust . packFinite @n @a) [getFinite x..]

prop_valid_enumFromTo = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) (Big y) ->
    all isValidFinite [x..y]
prop_valid_enumFromTo' = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Small x :: Small a n) (Small y) ->
    all isValidFinite [x..y]
prop_getFinite_enumFromTo = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) (Big y) ->
    map getFinite [x..y] === [getFinite x..getFinite y]
prop_getFinite_enumFromTo' = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Small x :: Small a n) (Small y) ->
    map getFinite [x..y] === [getFinite x..getFinite y]

prop_valid_enumFromThen = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) (Big y) ->
    x < y ==> all isValidFinite [x,y..]
prop_valid_enumFromThen' = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Small x :: Small a n) (Small y) ->
    x > y ==> all isValidFinite [x,y..]
prop_getFinite_enumFromThen = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) (Big y) ->
    x < y ==> map getFinite [x,y..]
        === takeWhile (isJust . packFinite @n @a) [getFinite x,getFinite y..]
prop_getFinite_enumFromThen' = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Small x :: Small a n) (Small y) ->
    x > y ==> map getFinite [x,y..]
        === takeWhile (isJust . packFinite @n @a) [getFinite x,getFinite y..]

prop_valid_enumFromThenTo = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Small x :: Small a n) (Small y) (Small z) ->
    x /= y ==> all isValidFinite [x,y..z]
prop_getFinite_enumFromThenTo = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Small x :: Small a n) (Small y) (Small z) ->
    x /= y ==> map getFinite [x,y..z] === [getFinite x,getFinite y..getFinite z]

prop_nonint_succ = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Big x :: Big a n) ->
    case packFinite @n @a $ succ $ getFinite x of
        Nothing -> discard
        Just y -> y === succ x

prop_valid_read = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forPositiveLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) -> ioProperty $
    evaluate (isValidFinite $ read @(Finite a m) (show x))
        `catch` \(_ :: ErrorCall) -> pure True
prop_read_show = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    read (show x) === x

prop_valid_plus = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    isValidFinite $ x + y
prop_getFinite_plus = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    (getFinite x + getFinite y - getFinite (x + y)) `mod` n === 0

prop_valid_minus = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
        isValidFinite $ x - y
prop_getFinite_minus = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    (getFinite x + n - getFinite y - getFinite (x - y)) `mod` n === 0

prop_valid_times = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
        isValidFinite $ x * y
prop_getFinite_times = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    (toInteger (getFinite x) * toInteger (getFinite y)
        - toInteger (getFinite $ x * y)) `mod` n === 0

prop_valid_negate = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
        isValidFinite $ -x
prop_getFinite_negate = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    (n - getFinite x - getFinite (-x)) `mod` n === 0

prop_valid_abs = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ abs x
prop_getFinite_abs = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    getFinite (abs x) === abs (getFinite x)

prop_valid_signum = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ signum x
prop_getFinite_signum = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    getFinite (signum x) === signum (getFinite x)

prop_valid_fromInteger = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    evaluate (isValidFinite $ fromInteger @(Finite a n) x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_toInteger_fromInteger = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    evaluate (toInteger (fromInteger @(Finite a n) x) == x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_fromInteger_toInteger = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    fromInteger (toInteger x) === x

prop_valid_quot = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> isValidFinite $ x `quot` y
prop_getFinite_quot = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> getFinite (x `quot` y) === getFinite x `quot` getFinite y

prop_valid_rem = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> isValidFinite $ x `rem` y
prop_getFinite_rem = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> getFinite (x `rem` y) === getFinite x `rem` getFinite y

prop_valid_div = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> isValidFinite $ x `div` y
prop_getFinite_div = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> getFinite (x `div` y) === getFinite x `div` getFinite y

prop_valid_mod = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> isValidFinite $ x `mod` y
prop_getFinite_mod = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y) ->
    y /= 0 ==> getFinite (x `mod` y) === getFinite x `mod` getFinite y

prop_force = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    ioProperty $
    evaluate (rnf @(Finite a n) (error "Expected exception") `seq` False)
        `catch` (\(_ :: ErrorCall) -> pure True)

prop_valid_packFinite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x ->
    maybe True isValidFinite $ packFinite @n @a x
prop_getFinite_packFinite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x ->
    maybe (property True) ((x ===) . getFinite) $ packFinite @n @a x
prop_finite_packFinite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
    case packFinite @n @a x of
        Nothing -> (evaluate (finite @n @a x) >> pure False)
            `catch` \(_ :: ErrorCall) -> pure True
        Just y -> evaluate (y == finite x)

prop_valid_finites = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \_ (_ :: Proxy n) ->
    property $
    all isValidFinite $ finites @n @a
prop_finites_minMax = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    n > 0 ==> minBound `elem` finites @n @a .&&. maxBound `elem` finites @n @a
prop_finites_ordered = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \_ (_ :: Proxy n) ->
    finites @n @a === sort finites
prop_finites_all = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \_ (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    x -- could be discard
        `seq` x `elem` finites @n @a

prop_valid_modulo = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    property $ \x ->
    isValidFinite $ modulo @n @a x
prop_getFinite_modulo = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \x ->
    (toInteger x - toInteger (getFinite $ modulo @n @a x)) `mod` n === 0

prop_getFinite_equals = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forPositiveLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    (x `equals` y) === (getFinite x == getFinite y)

prop_getFinite_cmp = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forPositiveLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    (x `cmp` y) === (getFinite x `compare` getFinite y)

prop_valid_natToFinite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    n + 1 <= m ==> unsafeWithInequality @(n + 1) @m $
    property $
    isValidFinite $ natToFinite @n @m @a Proxy
prop_getFinite_natToFinite = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    n + 1 <= m ==> unsafeWithInequality @(n + 1) @m $
    getFinite (natToFinite @n @m @a Proxy) === n

prop_valid_weaken = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ weaken x
prop_finites_weaken = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    map (weaken @n @a) finites === init finites

prop_valid_strengthen = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    property $ \(Edgy x :: Edgy a (n + 1)) ->
    maybe True isValidFinite $ strengthen x
prop_finites_strengthen = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    map (strengthen @n @a) finites === map Just finites ++ [Nothing]

prop_valid_shift = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ shift x
prop_finites_shift = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    map (shift @n @a) finites === drop 1 finites

prop_valid_unshift = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    property $ \(Edgy x :: Edgy a (n + 1)) ->
    maybe True isValidFinite $ unshift x
prop_finites_unshift = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    map (unshift @n @a) finites === [Nothing] ++ map Just finites

prop_valid_weakenN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    n <= m ==> unsafeWithInequality @n @m $
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ weakenN @n @m @a x
prop_finites_weakenN = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    n <= m ==> unsafeWithInequality @n @m $
    map (weakenN @n @m @a) finites === take n finites

prop_valid_strengthenN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) ->
    maybe True isValidFinite $ strengthenN @n @m x
prop_finites_strengthenN = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    map (strengthenN @n @m @a) finites
        === take n (map Just finites) ++ replicate (n - m) Nothing

prop_valid_shiftN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    n <= m ==> unsafeWithInequality @n @m $
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ shiftN @n @m @a x
prop_finites_shiftN = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    n <= m ==> unsafeWithInequality @n @m $
    map (shiftN @n @m @a) finites === drop (m - n) finites

prop_valid_unshiftN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) ->
    maybe True isValidFinite $ unshiftN @n @m x
prop_finites_unshiftN = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    map (unshiftN @n @m @a) finites
        === replicate (n - m) Nothing ++ drop (m - n) (map Just finites)

prop_valid_weakenProxy = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ weakenProxy @n @k Proxy x
prop_finites_weakenProxy = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    map (weakenProxy @n @k @a Proxy) finites === take n finites

prop_valid_strengthenProxy = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    property $ \(Edgy x :: Edgy a (n + k)) ->
    maybe True isValidFinite $ strengthenProxy @n @k Proxy x
prop_finites_strengthenProxy = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    map (strengthenProxy @n @k @a Proxy) finites
        === take n (map Just finites) ++ replicate k Nothing

prop_valid_shiftProxy = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    property $ \(Edgy x :: Edgy a n) ->
    isValidFinite $ shiftProxy @n @k Proxy x
prop_finites_shiftProxy = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    map (shiftProxy @n @k @a Proxy) finites === drop k finites

prop_valid_unshiftProxy = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    property $ \(Edgy x :: Edgy a (n + k)) ->
    maybe True isValidFinite $ unshiftProxy @n @k Proxy x
prop_finites_unshiftProxy = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    map (unshiftProxy @n @k @a Proxy) finites
        === replicate k Nothing ++ map Just finites

prop_strengthen_weaken = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    strengthen (weaken x) === Just x
prop_weaken_strengthen = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    property $ \(Edgy x :: Edgy a (n + 1)) ->
    maybe True (== x) (weaken <$> strengthen x)

prop_unshift_shift = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    property $ \(Edgy x :: Edgy a n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    unshift (shift x) === Just x
prop_shift_unshift = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    unsafeWithKnownIntegral @(n + 1) @a (n + 1) $
    property $ \(Edgy x :: Edgy a (n + 1)) ->
    maybe True (== x) (shift <$> unshift x)

prop_strengthenN_weakenN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    n <= m ==> unsafeWithInequality @n @m $
    property $ \(Edgy x :: Edgy a n) ->
    strengthenN (weakenN @n @m x) === Just x
prop_weakenN_strengthenN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    m <= n ==> unsafeWithInequality @m @n $
    property $ \(Edgy x :: Edgy a n) ->
    maybe True (== x) (weakenN <$> strengthenN @n @m x)

prop_unshiftN_shiftN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    n <= m ==> unsafeWithInequality @n @m $
    property $ \(Edgy x :: Edgy a n) ->
    unshiftN (shiftN @n @m x) === Just x
prop_shiftN_unshiftN = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    m <= n ==> unsafeWithInequality @m @n $
    property $ \(Edgy x :: Edgy a n) ->
    maybe True (== x) (shiftN <$> unshiftN @n @m x)

prop_strengthenProxy_weakenProxy = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    property $ \(Edgy x :: Edgy a n) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    strengthenProxy Proxy (weakenProxy @n @k Proxy x) === Just x
prop_weakenProxy_strengthenProxy = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    property $ \(Edgy x :: Edgy a (n + k)) ->
    maybe True (== x) (weakenProxy Proxy <$> strengthenProxy @n @k Proxy x)

prop_unshiftProxy_shiftProxy = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    property $ \(Edgy x :: Edgy a n) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    unshiftProxy Proxy (shiftProxy @n @k Proxy x) === Just x
prop_shiftProxy_unshiftProxy = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \k (_ :: Proxy k) ->
    unsafeWithKnownIntegral @(n + k) @a (n + k) $
    property $ \(Edgy x :: Edgy a (n + k)) ->
    maybe True (== x) (shiftProxy Proxy <$> unshiftProxy @n @k Proxy x)

prop_valid_add = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    isValidFinite $ add x y
prop_getFinite_add = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    getFinite (add x y) === getFinite x + getFinite y

prop_valid_sub = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forPositiveLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    either isValidFinite isValidFinite $ sub x y
prop_getFinite_sub = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forPositiveLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    either (negate . toInteger . getFinite) (toInteger . getFinite) (sub x y)
        === toInteger (getFinite x) - toInteger (getFinite y)
prop_sub_Left_0 = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \_ (_ :: Proxy n) ->
    forPositiveLimit @a $ \_ (_ :: Proxy m) ->
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    sub x y =/= Left 0

prop_valid_multiply = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    isValidFinite $ multiply x y
prop_getFinite_multiply = forType $ \(_ :: Proxy a) ->
    forPositiveLimit @a $ \n (_ :: Proxy n) ->
    forPositiveLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    property $ \(Edgy x :: Edgy a n) (Edgy y :: Edgy a m) ->
    getFinite (multiply x y) === getFinite x * getFinite y

prop_valid_combineSum = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    property $ \e ->
    isValidFinite $ combineSum
        $ bimap (\(Edgy x :: Edgy a n) -> x) (\(Edgy y :: Edgy a m) -> y) e
prop_finites_combineSum = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    map (combineSum @n @m @a) (map Left finites ++ map Right finites)
        === finites

prop_valid_combineProduct = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    property $ \p ->
    isValidFinite $ combineProduct
        $ bimap (\(Edgy x :: Edgy a n) -> x) (\(Edgy y :: Edgy a m) -> y) p
prop_finites_combineProduct = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    map (combineProduct @n @m @a) [(x, y) | y <- finites, x <- finites]
        === finites

prop_valid_separateSum = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    property $ \(Edgy x :: Edgy a (n + m)) ->
    either isValidFinite isValidFinite $ separateSum @n @m x
prop_finites_separateSum = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    map (separateSum @n @m @a) finites === map Left finites ++ map Right finites

prop_valid_separateProduct = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    property $ \(Edgy x :: Edgy a (n GHC.TypeLits.* m)) ->
    x -- could be discard
        `seq` isValidFinite (fst $ separateProduct @n @m x)
        .&&. isValidFinite (snd $ separateProduct @n @m x)
prop_finites_separateProduct = forType $ \(_ :: Proxy a) ->
    forSmallLimit @a $ \n (_ :: Proxy n) ->
    forSmallLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    map (separateProduct @n @m @a) finites
        === [(x, y) | y <- finites, x <- finites]

prop_combineSum_separateSum = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    property $ \(Edgy x :: Edgy a (n + m)) ->
    combineSum (separateSum @n @m x) === x
prop_separateSum_combineSum = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n + m) @a (n + m) $
    property $ \e ->
    let x = bimap (\(Edgy x :: Edgy a n) -> x) (\(Edgy y :: Edgy a m) -> y) e in
    separateSum (combineSum x) === x

prop_combineProduct_separateProduct = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    property $ \(Edgy x :: Edgy a (n GHC.TypeLits.* m)) ->
    x -- could be discard
        `seq` combineProduct (separateProduct @n @m x) === x
prop_separateProduct_combineProduct = forType $ \(_ :: Proxy a) ->
    forLimit @a $ \n (_ :: Proxy n) ->
    forLimit @a $ \m (_ :: Proxy m) ->
    unsafeWithKnownIntegral @(n GHC.TypeLits.* m) @a (n * m) $
    property $ \p ->
    let x = bimap (\(Edgy x :: Edgy a n) -> x) (\(Edgy y :: Edgy a m) -> y) p in
    force x -- could be discard
        `seq` separateProduct (combineProduct x) === x

return []
main = $quickCheckAll >>= \case
    True -> pure ()
    False -> exitFailure
