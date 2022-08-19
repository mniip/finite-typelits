--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite.Internal
-- Copyright   :  (C) 2015-2022 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}
module Data.Finite.Internal
    (
        Finite(Finite),
        finite,
        getFinite
    )
    where

import Control.DeepSeq
import Control.Monad
import Data.Ratio
import GHC.Read
import GHC.TypeLits
import Text.ParserCombinators.ReadPrec
import Text.Read.Lex

-- | Finite number type. @'Finite' n@ is inhabited by exactly @n@ values
-- the range @[0, n)@ including @0@ but excluding @n@. Invariants:
--
-- prop> getFinite x < natVal x
-- prop> getFinite x >= 0
newtype Finite (n :: Nat) = Finite Integer
                          deriving (Eq, Ord)

-- | Convert an 'Integer' into a 'Finite', throwing an error if the input is out
-- of bounds.
finite :: forall n. KnownNat n => Integer -> Finite n
finite x = result
    where
        result = if x < natVal result && x >= 0
            then Finite x
            else error $ "finite: Integer " ++ show x ++ " is not representable in Finite " ++ show (natVal result)

-- | Convert a 'Finite' into the corresponding 'Integer'.
getFinite :: forall n. Finite n -> Integer
getFinite (Finite x) = x

-- | Throws an error for @'Finite' 0@
instance KnownNat n => Bounded (Finite n) where
    maxBound = result
        where
            result = if natVal result > 0
                then Finite $ natVal result - 1
                else error "maxBound: Finite 0 is uninhabited"
    minBound = result
        where
            result = if natVal result > 0
                then Finite 0
                else error "minBound: Finite 0 is uninhabited"

instance KnownNat n => Enum (Finite n) where
    succ fx@(Finite x) = if x == natVal fx - 1
        then error "succ: bad argument"
        else Finite $ succ x
    pred (Finite x) = if x == 0
        then error "pred: bad argument"
        else Finite $ pred x
    fromEnum = fromEnum . getFinite
    toEnum = finite . toEnum
    enumFrom x = enumFromTo x maxBound
    enumFromTo (Finite x) (Finite y) = Finite `fmap` enumFromTo x y
    enumFromThen x y = enumFromThenTo x y (if x >= y then minBound else maxBound)
    enumFromThenTo (Finite x) (Finite y) (Finite z) = Finite `fmap` enumFromThenTo x y z

instance Show (Finite n) where
    showsPrec d (Finite x) = showParen (d > 9) $ showString "finite " . showsPrec 10 x

instance KnownNat n => Read (Finite n) where
    readPrec = parens $ Text.ParserCombinators.ReadPrec.prec 10 $ do
                 expectP (Ident "finite")
                 x <- readPrec
                 let result = finite x
                 guard (x >= 0 && x < natVal result)
                 return result

-- | 'Prelude.+', 'Prelude.-', and 'Prelude.*' implement arithmetic modulo @n@.
-- The 'fromInteger' function raises an error for inputs outside of bounds.
instance KnownNat n => Num (Finite n) where
    fx@(Finite x) + Finite y = Finite $ (x + y) `mod` natVal fx
    fx@(Finite x) - Finite y = Finite $ (x - y) `mod` natVal fx
    fx@(Finite x) * Finite y = Finite $ (x * y) `mod` natVal fx
    abs fx = fx
    signum (Finite x) = fromInteger $ if x == 0 then 0 else 1
    fromInteger x = result
        where
            result = if x < natVal result && x >= 0
                then Finite x
                else error $ "fromInteger: Integer " ++ show x ++ " is not representable in Finite " ++ show (natVal result)

instance KnownNat n => Real (Finite n) where
    toRational (Finite x) = x % 1

-- | 'quot' and 'rem' are the same as 'div' and 'mod' and they implement regular
-- division of numbers in the range @[0, n)@, __not__ modular arithmetic.
instance KnownNat n => Integral (Finite n) where
    quotRem (Finite x) (Finite y) = (Finite $ x `quot` y, Finite $ x `rem` y)
    toInteger (Finite x) = x

instance NFData (Finite n) where
    rnf (Finite x) = rnf x
