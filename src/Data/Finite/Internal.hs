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
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Finite.Internal
    (
        Finite(Finite),
        finite,
        getFinite
    )
    where

import Control.DeepSeq
import Control.Monad
import Data.Ix
import Data.Proxy
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
    deriving (Eq, Ord, Ix)

type role Finite nominal

pack :: forall n. KnownNat n => String -> Integer -> Finite n
pack name x
    | x < n && x >= 0 = Finite x
    | otherwise = error $ name ++ ": Integer " ++ show x
        ++ " is not representable in Finite " ++ show n
    where n = natVal (Proxy :: Proxy n)


-- | Convert an 'Integer' into a 'Finite', throwing an error if the input is out
-- of bounds.
finite :: forall n. KnownNat n => Integer -> Finite n
finite = pack "finite"

-- | Convert a 'Finite' into the corresponding 'Integer'.
getFinite :: forall n. Finite n -> Integer
getFinite (Finite x) = x

-- | Throws an error for @'Finite' 0@
instance KnownNat n => Bounded (Finite n) where
    maxBound
        | n > 0 = Finite $ n - 1
        | otherwise = error "maxBound: Finite 0 is uninhabited"
        where n = natVal (Proxy :: Proxy n)
    minBound
        | n > 0 = Finite 0
        | otherwise = error "minBound: Finite 0 is uninhabited"
        where n = natVal (Proxy :: Proxy n)

instance KnownNat n => Enum (Finite n) where
    succ (Finite x)
        | x == n - 1 = error "succ: bad argument"
        | otherwise = Finite $ succ x
        where n = natVal (Proxy :: Proxy n)
    pred (Finite x)
        | x == 0 = error "pred: bad argument"
        | otherwise = Finite $ pred x
    fromEnum = fromEnum . getFinite
    toEnum = pack "toEnum" . toEnum
    enumFrom x = enumFromTo x maxBound
    enumFromTo (Finite x) (Finite y) = Finite `fmap` enumFromTo x y
    enumFromThen x y
        = enumFromThenTo x y (if x >= y then minBound else maxBound)
    enumFromThenTo (Finite x) (Finite y) (Finite z)
        = Finite `fmap` enumFromThenTo x y z

instance Show (Finite n) where
    showsPrec d (Finite x)
        = showParen (d > 9) $ showString "finite " . showsPrec 10 x

instance KnownNat n => Read (Finite n) where
    readPrec = parens $ Text.ParserCombinators.ReadPrec.prec 10 $ do
                 expectP (Ident "finite")
                 x <- readPrec
                 guard (x >= 0 && x < n)
                 return $ Finite x
        where n = natVal (Proxy :: Proxy n)

-- | 'Prelude.+', 'Prelude.-', and 'Prelude.*' implement arithmetic modulo @n@.
-- The 'fromInteger' function raises an error for inputs outside of bounds.
instance KnownNat n => Num (Finite n) where
    Finite x + Finite y = Finite $ (x + y) `mod` n
        where n = natVal (Proxy :: Proxy n)
    Finite x - Finite y = Finite $ (x - y) `mod` n
        where n = natVal (Proxy :: Proxy n)
    Finite x * Finite y = Finite $ (x * y) `mod` n
        where n = natVal (Proxy :: Proxy n)
    abs fx = fx
    signum (Finite x) = Finite $ if x == 0 then 0 else 1
    fromInteger = pack "fromInteger"

instance KnownNat n => Real (Finite n) where
    toRational (Finite x) = x % 1

-- | 'quot' and 'rem' are the same as 'div' and 'mod' and they implement regular
-- division of numbers in the range @[0, n)@, __not__ modular arithmetic.
instance KnownNat n => Integral (Finite n) where
    quot (Finite x) (Finite y) = Finite $ quot x y
    rem (Finite x) (Finite y) = Finite $ rem x y
    quotRem (Finite x) (Finite y) = case quotRem x y of
        (q, r) -> (Finite q, Finite r)
    div (Finite x) (Finite y) = Finite $ div x y
    mod (Finite x) (Finite y) = Finite $ mod x y
    divMod (Finite x) (Finite y) = case divMod x y of
        (q, r) -> (Finite q, Finite r)
    toInteger (Finite x) = x

instance NFData (Finite n) where
    rnf (Finite x) = rnf x
