--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite.Internal
-- Copyright   :  (C) 2015 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE KindSignatures, DataKinds, DeriveGeneric #-}
module Data.Finite.Internal
    (
        Finite(Finite),
        finite,
        getFinite
    )
    where

import GHC.Read
import GHC.TypeLits
import GHC.Generics
import Control.DeepSeq
import Data.Ratio
import Text.Read.Lex
import Text.ParserCombinators.ReadPrec

-- | Finite number type. @'Finite' n@ is inhabited by exactly @n@ values. Invariants:
--
-- prop> getFinite x < natVal x
-- prop> getFinite x >= 0
newtype Finite (n :: Nat) = Finite Integer
                          deriving (Eq, Ord, Generic)

-- | Convert an 'Integer' into a 'Finite', throwing an error if the input is out of bounds.
finite :: KnownNat n => Integer -> Finite n
finite x = result
    where
        result = if x < natVal result && x >= 0
            then Finite x
            else error $ "finite: Integer " ++ show x ++ " is not representable in Finite " ++ show (natVal result)

-- | Convert a 'Finite' into the corresponding 'Integer'.
getFinite :: Finite n -> Integer
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
    fromEnum = fromEnum . getFinite
    toEnum = finite . toEnum
    enumFrom x = enumFromTo x maxBound
    enumFromThen x y = enumFromThenTo x y (if x >= y then minBound else maxBound)

instance Show (Finite n) where
    showsPrec d (Finite x) = showParen (d > 9) $ showString "finite " . showsPrec 10 x

instance KnownNat n => Read (Finite n) where
    readPrec = parens $ Text.ParserCombinators.ReadPrec.prec 10 $ expectP (Ident "finite") >> finite <$> step readPrec

-- | Modulo arithmetic. Only the 'fromInteger' function is supposed to be useful.
instance KnownNat n => Num (Finite n) where
    fx@(Finite x) + Finite y = Finite $ (x + y) `mod` natVal fx
    fx@(Finite x) - Finite y = Finite $ (x - y) `mod` natVal fx
    fx@(Finite x) * Finite y = Finite $ (x * y) `mod` natVal fx
    abs fx = fx
    signum _ = fromInteger 1
    fromInteger x = result
        where
            result = if x < natVal result && x >= 0
                then Finite x
                else error $ "fromInteger: Integer " ++ show x ++ " is not representable in Finite " ++ show (natVal result)

instance KnownNat n => Real (Finite n) where
    toRational (Finite x) = x % 1

instance KnownNat n => Integral (Finite n) where
    quotRem (Finite x) (Finite y) = (Finite $ x `quot` y, Finite $ x `rem` y)
    toInteger (Finite x) = x

instance NFData (Finite n)
