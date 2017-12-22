--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite.Internal
-- Copyright   :  (C) 2015 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE KindSignatures, DataKinds, DeriveGeneric, ScopedTypeVariables, TypeApplications #-}
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
import Control.Monad
import Data.Ratio
import Data.Proxy
import Text.Read.Lex
import Text.ParserCombinators.ReadPrec

-- | Finite number type. @'Finite' n@ is inhabited by exactly @n@ values. Invariants:
--
-- prop> getFinite x < natVal x
-- prop> getFinite x >= 0
newtype Finite (n :: Nat) = Finite Integer
                          deriving (Eq, Ord, Generic)

-- | Convert an 'Integer' into a 'Finite', throwing an error if the input is out of bounds.
finite :: forall n. KnownNat n => Integer -> Finite n
finite x = if x < natVal (Proxy @n) && x >= 0
              then Finite x
              else error $ "finite: Integer " ++ show x ++ " is not representable in Finite " ++ show (natVal (Proxy @n))

-- | Convert a 'Finite' into the corresponding 'Integer'.
getFinite :: forall n. Finite n -> Integer
getFinite (Finite x) = x

-- | Throws an error for @'Finite' 0@
instance KnownNat n => Bounded (Finite n) where
    maxBound = if natVal (Proxy @n) > 0
                  then Finite $ natVal (Proxy @n) - 1
                  else error "maxBound: Finite 0 is uninhabited"
    minBound = if natVal (Proxy @n) > 0
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
    readPrec = parens $ Text.ParserCombinators.ReadPrec.prec 10 $ do 
                 expectP (Ident "finite")
                 x <- readPrec
                 guard (x >= 0 && x < natVal (Proxy @n)) 
                 return $ Finite x

-- | Modulo arithmetic. Only the 'fromInteger' function is supposed to be useful.
instance KnownNat n => Num (Finite n) where
    Finite x + Finite y = Finite $ (x + y) `rem` natVal (Proxy @n)
    Finite x - Finite y = Finite $ (x - y) `mod` natVal (Proxy @n)
    Finite x * Finite y = Finite $ (x * y) `rem` natVal (Proxy @n)
    abs = id
    signum (Finite x) = Finite $ signum x
    fromInteger x = if x < natVal (Proxy @n) && x >= 0
                       then Finite x
                       else error $ "fromInteger: Integer " ++ show x ++ " is not representable in Finite " ++ show (natVal (Proxy @n))

instance KnownNat n => Real (Finite n) where
    toRational (Finite x) = x % 1

instance KnownNat n => Integral (Finite n) where
    quotRem (Finite x) (Finite y) = (Finite quot, Finite rem)
      where (quot, rem) = x `quotRem` y
    divMod = quotRem -- divMod = quotRem when ignoring negative values, like here
    toInteger = getFinite

instance NFData (Finite n)
