{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
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
import Data.List
import Data.Maybe
import Data.Proxy
import Data.Type.Equality
import GHC.TypeLits
import System.Exit
import Test.QuickCheck
import Unsafe.Coerce

import Data.Finite
import Data.Finite.Internal

instance KnownNat n => Arbitrary (Finite n) where
    arbitrary
        | natVal @n Proxy == 0 = discard
        | otherwise = oneof
            [ pure (Finite 0)
            , pure (Finite $ natVal @n Proxy - 1)
            , Finite . (`mod` natVal @n Proxy) <$> arbitrary
            ]
    shrink (Finite x) = mapMaybe packFinite $ shrink x

withNat' :: forall prop. Testable prop => Gen Integer -> (Integer -> [Integer]) -> (forall n. KnownNat n => (forall i. Num i => i) -> Proxy n -> prop) -> Property
withNat' gen shr prop = forAllShrinkBlind gen shr $ \n -> case someNatVal n of
    Nothing -> counterexample "withNat" False
    Just (SomeNat p) -> counterexample ("@" ++ show n) $ prop (fromInteger (natVal p)) p

withNat :: forall prop. Testable prop => (forall n. KnownNat n => (forall i. Num i => i) -> Proxy n -> prop) -> Property
withNat = withNat' (getNonNegative <$> arbitrary) (map getNonNegative . shrink . NonNegative)

withNatPos :: forall prop. Testable prop => (forall n. KnownNat n => (forall i. Num i => i) -> Proxy n -> prop) -> Property
withNatPos = withNat' (getPositive <$> arbitrary) (map getPositive . shrink . Positive)

unsafeWithKnownNat :: forall n prop. Testable prop => Integer -> (KnownNat n => prop) -> Property
unsafeWithKnownNat n prop = case someNatVal n of
    Nothing -> counterexample "unsafeWithKnownNat: someNatVal" False
    Just (SomeNat (_ :: Proxy n')) -> case unsafeCoerce Refl :: n :~: n' of
        Refl -> property prop

newtype IneqCond (n :: Nat) (m :: Nat) = IneqCond ((n <= m) => Property)
unsafeWithInequality :: forall (n :: Nat) (m :: Nat) prop. Testable prop => ((n <= m) => prop) -> Property
unsafeWithInequality prop =
    case unsafeCoerce (IneqCond @n @m $ property prop) :: IneqCond 0 1 of
        IneqCond prop' -> prop'

prop_isvalid_under = withNat $ \_ (_ :: Proxy n) x ->
    x < 0 ==> expectFailure $ isValidFinite @n (Finite x)
prop_isvalid_over = withNat $ \n (_ :: Proxy n) x ->
    x >= n ==> expectFailure $ isValidFinite @n (Finite x)

prop_valid_finite = withNat $ \_ (_ :: Proxy n) x -> ioProperty $
    evaluate (isValidFinite $ finite @n x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_getFinite_finite = withNat $ \_ (_ :: Proxy n) x -> ioProperty $
    evaluate (getFinite (finite @n x) == x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_finite_getFinite = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        finite (getFinite @n x) === x

prop_valid_maxBound = withNat $ \n (_ :: Proxy n) ->
    n > 0 ==> isValidFinite (maxBound @(Finite n))
prop_maxBound_max = withNat $ \n (_ :: Proxy n) ->
    property $ \x ->
        n > 0 ==> maxBound @(Finite n) >= x

prop_valid_minBound = withNat $ \n (_ :: Proxy n) ->
    n > 0 ==> isValidFinite (minBound @(Finite n))
prop_minBound_min = withNat $ \n (_ :: Proxy n) ->
    property $ \x ->
        n > 0 ==> minBound @(Finite n) <= x

prop_valid_toEnum = withNat $ \_ (_ :: Proxy n) x -> ioProperty $
    evaluate (isValidFinite $ toEnum @(Finite n) x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_fromEnum_toEnum = withNat $ \_ (_ :: Proxy n) x -> ioProperty $
    evaluate (fromEnum (toEnum @(Finite n) x) == x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_toEnum_fromEnum = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        toEnum @(Finite n) (fromEnum x) == x

prop_valid_enumFrom = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        all isValidFinite $ enumFrom @(Finite n) x
prop_getFinite_enumFrom = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        map getFinite (enumFrom @(Finite n) x)
            === takeWhile (isJust . packFinite @n) (enumFrom (getFinite x))

prop_valid_enumFromTo = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        all isValidFinite $ enumFromTo @(Finite n) x y
prop_getFinite_enumFromTo = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        map getFinite (enumFromTo @(Finite n) x y)
            === enumFromTo (getFinite x) (getFinite y)

prop_valid_enumFromThen = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        x /= y ==> all isValidFinite $ enumFromThen @(Finite n) x y
prop_getFinite_enumFromThen = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        x /= y ==> map getFinite (enumFromThen @(Finite n) x y)
            === takeWhile (isJust . packFinite @n) (enumFromThen (getFinite x) (getFinite y))

prop_valid_enumFromThenTo = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y z ->
        x /= y ==> all isValidFinite $ enumFromThenTo @(Finite n) x y z
prop_getFinite_enumFromThenTo = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y z ->
        x /= y ==> map getFinite (enumFromThenTo @(Finite n) x y z)
            === enumFromThenTo (getFinite x) (getFinite y) (getFinite z)

prop_nonint_succ = withNat' genBig shrinkBig $ \_ (_ :: Proxy n) ->
    forAllShrink genBig shrinkBig $ \x ->
        case packFinite @n $ succ x of
            Nothing -> discard
            Just y -> y === succ (finite x)
    where
        big = toInteger (maxBound :: Int)
        genBig = (big +) . getNonNegative <$> arbitrary
        shrinkBig = map ((big +) . getNonNegative) . shrink . NonNegative . subtract big

prop_valid_read = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x -> ioProperty $
            evaluate (isValidFinite $ read @(Finite n) (show @(Finite m) x))
                `catch` \(_ :: ErrorCall) -> pure True
prop_read_show = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        read (show @(Finite n) x) === x

prop_valid_plus = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        isValidFinite @n $ x + y
prop_getFinite_plus = withNatPos $ \n (_ :: Proxy n) ->
    property $ \x y ->
        (getFinite @n (x + y) - (getFinite x + getFinite y)) `mod` n === 0

prop_valid_minus = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        isValidFinite @n $ x - y
prop_getFinite_minus = withNatPos $ \n (_ :: Proxy n) ->
    property $ \x y ->
        (getFinite @n (x - y) - (getFinite x - getFinite y)) `mod` n === 0

prop_valid_times = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        isValidFinite @n $ x * y
prop_getFinite_times = withNatPos $ \n (_ :: Proxy n) ->
    property $ \x y ->
        (getFinite @n (x * y) - (getFinite x * getFinite y)) `mod` n === 0

prop_valid_negate = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        isValidFinite @n $ -x
prop_getFinite_negate = withNatPos $ \n (_ :: Proxy n) ->
    property $ \x ->
        (getFinite @n (-x) - (- getFinite x)) `mod` n === 0

prop_valid_abs = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        isValidFinite @n $ abs x
prop_getFinite_abs = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        getFinite @n (abs x) === abs (getFinite x)

prop_valid_signum = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
        evaluate (isValidFinite @n $ signum x)
            `catch` \(_ :: ErrorCall) -> pure True

prop_getFinite_signum = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x -> ioProperty $
        evaluate (getFinite @n (signum x) == signum (getFinite x))
            `catch` \(_ :: ErrorCall) -> pure True

prop_valid_fromInteger = withNatPos $ \_ (_ :: Proxy n) x -> ioProperty $
    evaluate (isValidFinite $ fromInteger @(Finite n) x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_toInteger_fromInteger = withNat $ \_ (_ :: Proxy n) x -> ioProperty $
    evaluate (toInteger (fromInteger @(Finite n) x) == x)
        `catch` \(_ :: ErrorCall) -> pure True
prop_fromInteger_toInteger = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        fromInteger (toInteger @(Finite n) x) === x

prop_valid_quot = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> isValidFinite @n $ x `quot` y
prop_getFinite_quot = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> getFinite @n (x `quot` y) === getFinite x `quot` getFinite y

prop_valid_rem = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> isValidFinite @n $ x `rem` y
prop_getFinite_rem = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> getFinite @n (x `rem` y) === getFinite x `rem` getFinite y

prop_valid_div = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> isValidFinite @n $ x `div` y
prop_getFinite_div = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> getFinite @n (x `div` y) === getFinite x `div` getFinite y

prop_valid_mod = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> isValidFinite @n $ x `mod` y
prop_getFinite_mod = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x y ->
        y /= 0 ==> getFinite @n (x `mod` y) === getFinite x `mod` getFinite y

prop_force = withNat $ \_ (_ :: Proxy n) ->
    expectFailure $ rnf @(Finite n) (error "Expected exception") `seq` True

prop_valid_packFinite = withNat $ \_ (_ :: Proxy n) x ->
    maybe True isValidFinite $ packFinite @n x
prop_getFinite_packFinite = withNat $ \_ (_ :: Proxy n) x ->
    maybe (property True) ((x ===) . getFinite) $ packFinite @n x
prop_finite_packFinite = withNat $ \_ (_ :: Proxy n) x -> ioProperty $
    case packFinite @n x of
        Nothing -> (evaluate (finite @n x) >> pure False)
            `catch` \(_ :: ErrorCall) -> pure True
        Just y -> evaluate (y == finite x)

prop_valid_finites = withNat $ \_ (_ :: Proxy n) ->
    all isValidFinite $ finites @n
prop_finites_minMax = withNatPos $ \_ (_ :: Proxy n) ->
    minBound `elem` finites @n .&&. maxBound `elem` finites @n
prop_finites_ordered = withNat $ \_ (_ :: Proxy n) ->
    finites @n === sort finites
prop_finites_all = withNat $ \_ (_ :: Proxy n) ->
    property $ \x ->
        x {- could be discard -} `seq` x `elem` finites @n

prop_valid_modulo = withNatPos $ \_ (_ :: Proxy n) x ->
    isValidFinite $ modulo @n x
prop_getFinite_modulo = withNatPos $ \n (_ :: Proxy n) x ->
    (getFinite (modulo @n x) - x) `mod` n === 0


prop_getFinite_equals = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            (x `equals` y) === (getFinite @n x == getFinite @m y)

prop_getFinite_cmp = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            (x `cmp` y) === (getFinite @n x `compare` getFinite @m y)

prop_valid_natToFinite = withNat $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        n + 1 <= m ==> unsafeWithInequality @(n + 1) @m @Bool $
            isValidFinite $ natToFinite @n @m Proxy
prop_getFinite_natToFinite = withNat $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        n + 1 <= m ==> unsafeWithInequality @(n + 1) @m @Property $
            getFinite (natToFinite @n @m Proxy) === natVal @n Proxy

prop_valid_weaken = withNatPos $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        property $ \x ->
            isValidFinite $ weaken @n x
prop_finites_weaken = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        map (weaken @n) finites === init finites

prop_valid_strengthen = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        property $ \x ->
            maybe True isValidFinite $ strengthen @n x
prop_finites_strengthen = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        map (strengthen @n) finites === map Just finites ++ [Nothing]

prop_valid_shift = withNatPos $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        property $ \x ->
            isValidFinite $ shift @n x
prop_finites_shift = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        map (shift @n) finites === drop 1 finites

prop_valid_unshift = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        property $ \x ->
            maybe True isValidFinite $ unshift @n x
prop_finites_unshift = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        map (unshift @n) finites === [Nothing] ++ map Just finites

prop_valid_weakenN = withNatPos $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        n <= m ==> unsafeWithInequality @n @m @Property $
            property $ \x ->
                isValidFinite $ weakenN @n @m x
prop_finites_weakenN = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        n <= m ==> unsafeWithInequality @n @m @Property $
            map (weakenN @n @m) finites === take n finites

prop_valid_strengthenN = withNat $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x ->
            maybe True isValidFinite $ strengthenN @m @n x
prop_finites_strengthenN = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        map (strengthenN @n @m) finites === take n (map Just finites) ++ replicate (n - m) Nothing

prop_valid_shiftN = withNatPos $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        n <= m ==> unsafeWithInequality @n @m @Property $
            property $ \x ->
                isValidFinite $ shiftN @n @m x
prop_finites_shiftN = withNat $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        n <= m ==> unsafeWithInequality @n @m @Property $
            map (shiftN @n @m) finites === drop (m - n) finites

prop_valid_unshiftN = withNatPos $ \_ (_ :: Proxy n) ->
    withNat $ \_ (_ :: Proxy m) ->
        property $ \x ->
            maybe True isValidFinite $ unshiftN @n @m x
prop_finites_unshiftN = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        map (unshiftN @n @m) finites === replicate (n - m) Nothing ++ drop (m - n) (map Just finites)

prop_valid_weakenProxy = withNatPos $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            property $ \x ->
                isValidFinite $ weakenProxy @n @k Proxy x
prop_finites_weakenProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            map (weakenProxy @n @k Proxy) finites === take n finites

prop_valid_strengthenProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            property $ \x ->
                maybe True isValidFinite $ strengthenProxy @n @k Proxy x
prop_finites_strengthenProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            map (strengthenProxy @n @k Proxy) finites === take n (map Just finites) ++ replicate k Nothing

prop_valid_shiftProxy = withNatPos $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            property $ \x ->
                isValidFinite $ shiftProxy @n @k Proxy x
prop_finites_shiftProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            map (shiftProxy @n @k Proxy) finites === drop k finites

prop_valid_unshiftProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            property $ \x ->
                maybe True isValidFinite $ unshiftProxy @n @k Proxy  x
prop_finites_unshiftProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            map (unshiftProxy @n @k Proxy) finites === replicate k Nothing ++ map Just finites

prop_strengthen_weaken = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        strengthen @n (weaken x) === Just x
prop_weaken_strengthen = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        property $ \x ->
            maybe True (== x) (weaken @n <$> strengthen x)

prop_unshift_shift = withNatPos $ \_ (_ :: Proxy n) ->
    property $ \x ->
        unshift @n (shift x) === Just x
prop_shift_unshift = withNat $ \n (_ :: Proxy n) ->
    unsafeWithKnownNat @(n + 1) (n + 1) $
        property $ \x ->
            maybe True (== x) (shift @n <$> unshift x)

prop_strengthenN_weakenN = withNatPos $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        m <= n ==> unsafeWithInequality @m @n @Property $
            property $ \x ->
                strengthenN @n @m (weakenN x) === Just x
prop_weakenN_strengthenN = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        n <= m ==> unsafeWithInequality @n @m @Property $
            property $ \x ->
                maybe True (== x) (weakenN @n @m <$> strengthenN x)

prop_unshiftN_shiftN = withNatPos $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        m <= n ==> unsafeWithInequality @m @n @Property $
            property $ \x ->
                unshiftN @n @m (shiftN x) === Just x
prop_shiftN_unshiftN = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        n <= m ==> unsafeWithInequality @n @m @Property $
            property $ \x ->
                maybe True (== x) (shiftN @n @m <$> unshiftN x)

prop_strengthenProxy_weakenProxy = withNatPos $ \_ (_ :: Proxy n) ->
    withNat $ \_ (_ :: Proxy k) ->
        property $ \x ->
            strengthenProxy @n @k Proxy (weakenProxy Proxy x) === Just x
prop_weakenProxy_strengthenProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            property $ \x ->
                maybe True (== x) (weakenProxy @n @k Proxy <$> strengthenProxy Proxy x)

prop_unshiftProxy_shiftProxy = withNatPos $ \_ (_ :: Proxy n) ->
    withNat $ \_ (_ :: Proxy k) ->
        property $ \x ->
            unshiftProxy @n @k Proxy (shiftProxy Proxy x) === Just x
prop_shiftProxy_unshiftProxy = withNat $ \n (_ :: Proxy n) ->
    withNat $ \k (_ :: Proxy k) ->
        unsafeWithKnownNat @(n + k) (n + k) $
            property $ \x ->
                maybe True (== x) (shiftProxy @n @k Proxy <$> unshiftProxy Proxy x)

prop_valid_add = withNatPos $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n + m) (n + m) $
            property $ \x y ->
                isValidFinite $ add @n @m x y
prop_getFinite_add = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            getFinite (add @n @m x y) === getFinite x + getFinite y

prop_valid_sub = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            either isValidFinite isValidFinite $ sub @n @m x y
prop_getFinite_sub = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            either (negate . getFinite) getFinite (sub @n @m x y) === getFinite x - getFinite y
prop_sub_Left_0 = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            sub @n @m x y =/= Left 0

prop_valid_multiply = withNatPos $ \n (_ :: Proxy n) ->
    withNatPos $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n GHC.TypeLits.* m) (n * m) $
            property $ \x y ->
                isValidFinite $ multiply @n @m x y
prop_getFinite_multiply = withNatPos $ \_ (_ :: Proxy n) ->
    withNatPos $ \_ (_ :: Proxy m) ->
        property $ \x y ->
            getFinite (multiply @n @m x y) === getFinite x * getFinite y

prop_valid_combineSum = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n + m) (n + m) $
            property $ \x ->
                isValidFinite $ combineSum @n @m x
prop_finites_combineSum = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n + m) (n + m) $
            map (combineSum @n @m) (map Left finites ++ map Right finites) === finites

prop_valid_combineProduct = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n GHC.TypeLits.* m) (n * m) $
            property $ \x ->
                isValidFinite (combineProduct @n @m x)
prop_finites_combineProduct = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n GHC.TypeLits.* m) (n * m) $
            map (combineProduct @n @m) [(x, y) | y <- finites, x <- finites] === finites

prop_valid_separateSum = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n + m) (n + m) $
            property $ \x ->
                either isValidFinite isValidFinite $ separateSum @n @m x
prop_finites_separateSum = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n + m) (n + m) $
            map (separateSum @n @m) finites === map Left finites ++ map Right finites

prop_valid_separateProduct = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n GHC.TypeLits.* m) (n * m) $
            property $ \x ->
                x {- could be discard -} `seq` isValidFinite (fst $ separateProduct @n @m x)
                    .&&. isValidFinite (snd $ separateProduct @n @m x)
prop_finites_separateProduct = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n GHC.TypeLits.* m) (n * m) $
            map (separateProduct @n @m) finites === [(x, y) | y <- finites, x <- finites]

prop_combineSum_separateSum = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n + m) (n + m) $
            property $ \x ->
                combineSum @n @m (separateSum x) === x
prop_separateSum_combineSum = withNat $ \_ (_ :: Proxy n) ->
    withNat $ \_ (_ :: Proxy m) ->
        property $ \x ->
            separateSum @n @m (combineSum x) === x

prop_combineProduct_separateProduct = withNat $ \n (_ :: Proxy n) ->
    withNat $ \m (_ :: Proxy m) ->
        unsafeWithKnownNat @(n GHC.TypeLits.* m) (n * m) $
            property $ \x ->
                x {- could be discard -} `seq` combineProduct @n @m (separateProduct x) === x
prop_separateProduct_combineProduct = withNat $ \_ (_ :: Proxy n) ->
    withNat $ \_ (_ :: Proxy m) ->
        property $ \x ->
            force x {- could be discard -} `seq` separateProduct @n @m (combineProduct x) === x

return []
main = $quickCheckAll >>= \case
    True -> pure ()
    False -> exitFailure
