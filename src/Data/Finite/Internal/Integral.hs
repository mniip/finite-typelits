--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite.Internal.Integral
-- Copyright   :  (C) 2015-2024 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UndecidableInstances #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE UndecidableSuperClasses #-}
#endif
module Data.Finite.Internal.Integral
    (
        SaneIntegral(..), Limited, KnownIntegral, intVal,
        withIntegral, withLimited,
        Finite(Finite), finite, getFinite
    )
    where

#if MIN_VERSION_base(4,8,0)
import Numeric.Natural
#endif
import Control.DeepSeq
import Control.Monad
import Data.Ix
import Data.Int
import Data.Proxy
import Data.Tagged
import Data.Type.Equality
import Data.Word
import GHC.Exts
import GHC.Read
import GHC.TypeLits
import Language.Haskell.TH.Lib
import Text.ParserCombinators.ReadPrec
import Text.Read.Lex
import Unsafe.Coerce

#include "MachDeps.h"

-- | A class of datatypes that faithfully represent a sub-range of 'Integer'
-- that includes @0@. A valid instance must obey the following laws:
--
-- 'fromInteger' must be a retract of 'toInteger':
--
-- prop> fromInteger (toInteger a) == a
--
-- Restricted to the range @[0, 'Limit']@ (with 'Nothing' understood as positive
-- infinity), 'fromInteger' must be an inverse of 'toInteger':
--
-- prop> limited i ==> toInteger (fromInteger i) == i
-- where:
--
-- > limited i = case limit of
-- >     Just l -> 0 <= i && i <= l
-- >     Nothing -> 0 <= i
--
-- __WARNING__: violating the above constraint in particular breaks type safety.
--
-- The implementations of 'Ord', 'Enum', 'Num', 'Integral' must be compatible
-- with that of 'Integer', whenever all arguments and results fall within
-- @[0, 'Limit']@, for example:
--
-- prop> limited i && limited j && limited k && (i * j == k) ==> (fromInteger i * fromInteger j == fromInteger k)
--
-- Methods 'modAdd', 'modSub', and 'modMul' implement modular addition,
-- multiplication, and subtraction. The default implementation is via 'Integer',
-- but a faster implementation can be provided instead. If provided, the
-- implementation must be correct for moduli in range @[1, 'Limit']@.
--
-- __WARNING:__ a naive implementaton is prone to arithmetic overflow and may
-- produce invalid results for moduli close to 'Limit'.
class Integral a => SaneIntegral a where
    type Limit a :: Maybe Nat
    -- | Given @n > 0@, @0 <= a < n@, and @0 <= b < n@, @'modAdd' n a b@
    -- computes @(a 'Prelude.+' b) \` 'mod' \` n@.
    modAdd :: a -> a -> a -> a
    modAdd n a b = fromInteger
        (modAdd (toInteger n) (toInteger a) (toInteger b) :: Integer)
    -- | Given @n > 0@, @0 <= a < n@, and @0 <= b < n@, @'modSub' n a b@
    -- computes @(a 'Prelude.-' b) \` 'mod' \` n@.
    modSub :: a -> a -> a -> a
    modSub n a b = fromInteger
        (modSub (toInteger n) (toInteger a) (toInteger b) :: Integer)
    -- | Given @n > 0@, @0 <= a < n@, and @0 <= b < n@, @'modMul' n a b@
    -- computes @(a 'Prelude.*' b) \` 'mod' \` n@.
    modMul :: a -> a -> a -> a
    modMul n a b = fromInteger
        (modMul (toInteger n) (toInteger a) (toInteger b) :: Integer)

instance SaneIntegral Integer where
    type Limit Integer = 'Nothing
    modAdd n a b = case a + b of
        r | r >= n -> r - n
        r -> r
    modSub n a b = if a >= b then a - b else n - b + a
    modMul n a b = (a * b) `mod` n

#if MIN_VERSION_base(4,8,0)
instance SaneIntegral Natural where
    type Limit Natural = 'Nothing
    modAdd n a b = case a + b of
        r | r >= n -> r - n
        r -> r
    modSub n a b = if a >= b then a - b else n - b + a
    modMul n a b = (a * b) `mod` n
#endif

instance SaneIntegral Word where
    type Limit Word = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Word))

    modAdd (W# n) (W# a) (W# b) = W# (case plusWord2# a b of
        (# 0##, r #) | isTrue# (ltWord# r n) -> r
        (# _, r #) -> minusWord# r n)

    modSub (W# n) (W# a) (W# b) = W# (if isTrue# (leWord# b a)
        then minusWord# a b
        else plusWord# (minusWord# n b) a)

    modMul (W# n) (W# a) (W# b) = W# (case n of
        0## -> error "modMul: division by zero"
        _ -> case timesWord2# a b of
            (# h, l #) -> case quotRemWord2# h l n of
                (# _, r #) -> r)

modAddViaWord :: (Num a, Integral a) => a -> a -> a -> a
modAddViaWord n a b = fromIntegral
    (modAdd (fromIntegral n) (fromIntegral a) (fromIntegral b) :: Word)

modSubViaWord :: (Num a, Integral a) => a -> a -> a -> a
modSubViaWord n a b = fromIntegral
    (modSub (fromIntegral n) (fromIntegral a) (fromIntegral b) :: Word)

modMulViaWord :: (Num a, Integral a) => a -> a -> a -> a
modMulViaWord n a b = fromIntegral
    (modMul (fromIntegral n) (fromIntegral a) (fromIntegral b) :: Word)

instance SaneIntegral Int where
    type Limit Int = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Int))
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord

instance SaneIntegral Word8 where
    type Limit Word8
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Word8))
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord

instance SaneIntegral Int8 where
    type Limit Int8
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Int8))
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord

instance SaneIntegral Word16 where
    type Limit Word16
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Word16))
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord

instance SaneIntegral Int16 where
    type Limit Int16
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Int16))
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord

instance SaneIntegral Word32 where
    type Limit Word32
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Word32))
#if WORD_SIZE_IN_BITS >= 32
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord
#endif

instance SaneIntegral Int32 where
    type Limit Int32
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Int32))
#if WORD_SIZE_IN_BITS >= 32
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord
#endif

instance SaneIntegral Word64 where
    type Limit Word64
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Word64))
#if WORD_SIZE_IN_BITS >= 64
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord
#endif

instance SaneIntegral Int64 where
    type Limit Int64
        = 'Just $(litT $ numTyLit $ toInteger (maxBound :: Int64))
#if WORD_SIZE_IN_BITS >= 64
    modAdd = modAddViaWord
    modSub = modSubViaWord
    modMul = modMulViaWord
#endif

class LeqMaybe (n :: Nat) (c :: Maybe Nat)
instance LeqMaybe n 'Nothing
instance n <= m => LeqMaybe n ('Just m)

-- | Ensures that the value of @n@ is representable in type @a@ (which should be
-- a 'SaneIntegral').
type Limited a (n :: Nat) = LeqMaybe n (Limit a)

-- | This class asserts that the value of @n@ is known at runtime, and that it
-- is representable in type @a@ (which should be a 'SaneIntegral').
--
-- At runtime it acts like an implicit parameter of type @a@, much like
-- 'KnownNat' is an implicit parameter of type 'Integer'.
class KnownIntegral a (n :: Nat) where
    intVal_ :: Tagged n a

instance (SaneIntegral a, Limited a n, KnownNat n) => KnownIntegral a n where
    intVal_ = Tagged $ fromInteger $ natVal (Proxy :: Proxy n)

-- | Reflect a type-level number into a term.
intVal :: forall n a proxy. KnownIntegral a n => proxy n -> a
intVal _ = unTagged (intVal_ :: Tagged n a)
{-# INLINABLE intVal #-}

-- | Recover a 'KnownNat' constraint from a 'KnownIntegral' constraint.
withIntegral
    :: forall a n r proxy1 proxy2. (SaneIntegral a, KnownIntegral a n)
    => proxy1 a -> proxy2 n -> (KnownNat n => r) -> r
withIntegral _ _ k = case someNatVal n of
    Nothing -> error $ "withIntegral: got KnowIntegral instance dictionary "
        ++ " for which toInteger returns " ++ show n
    Just (SomeNat (_ :: Proxy m)) -> case unsafeCoerce Refl :: n :~: m of
        Refl -> k
    where n = toInteger $ (intVal_  :: Tagged n a)
{-# INLINABLE withIntegral #-}

-- | Recover a 'Limited' constraint from a 'KnownIntegral' constraint.
withLimited
    :: forall a n r lim proxy1 proxy2. (Limit a ~ 'Just lim, KnownIntegral a n)
    => proxy1 a -> proxy2 n -> (Limited a n => r) -> r
withLimited _ _ k = case unsafeCoerce Refl :: (n <=? lim) :~: 'True of
    Refl -> k
{-# INLINABLE withLimited #-}

-- | Finite number type. The type @'Finite' a n@ is inhabited by exactly @n@
-- values from type @a@, in the range @[0, n)@ including @0@ but excluding @n@.
-- @a@ must be an instance of 'SaneIntegral' to use this type. Invariants:
--
-- prop> getFinite x < intVal x
-- prop> getFinite x >= 0
newtype Finite a (n :: Nat) = Finite a
    deriving (Eq, Ord, Ix)

type role Finite nominal nominal

-- | Convert an @a@ into a @'Finite' a@, throwing an error if the input is out
-- of bounds.
finite :: forall n a. (SaneIntegral a, KnownIntegral a n) => a -> Finite a n
finite x
    | x < n && x >= 0 = Finite x
    | otherwise = error $ "finite: Integral " ++ show (toInteger x)
        ++ " is not representable in Finite _ " ++ show (toInteger n)
    where n = intVal (Proxy :: Proxy n)
{-# INLINABLE finite #-}

-- | Convert a @'Finite' a@ into the corresponding @a@.
getFinite :: forall n a. Finite a n -> a
getFinite (Finite x) = x
{-# INLINABLE getFinite #-}

-- | Throws an error for @'Finite' _ 0@
instance (SaneIntegral a, KnownIntegral a n) => Bounded (Finite a n) where
    {-# SPECIALIZE instance KnownNat n => Bounded (Finite Integer n) #-}
#if MIN_VERSION_base(4,8,0)
    {-# SPECIALIZE instance KnownNat n => Bounded (Finite Natural n) #-}
#endif
    {-# SPECIALIZE instance KnownIntegral Word n => Bounded (Finite Word n) #-}
    {-# SPECIALIZE instance KnownIntegral Int n => Bounded (Finite Int n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word8 n => Bounded (Finite Word8 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int8 n => Bounded (Finite Int8 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word16 n => Bounded (Finite Word16 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int16 n => Bounded (Finite Int16 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word32 n => Bounded (Finite Word32 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int32 n => Bounded (Finite Int32 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word64 n => Bounded (Finite Word64 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int64 n => Bounded (Finite Int64 n) #-}
    maxBound
        | n > 0 = Finite $ n - 1
        | otherwise = error "maxBound: Finite _ 0 is uninhabited"
        where n = intVal (Proxy :: Proxy n) :: a
    minBound
        | n > 0 = Finite 0
        | otherwise = error "minBound: Finite _ 0 is uninhabited"
        where n = intVal (Proxy :: Proxy n) :: a

instance (SaneIntegral a, KnownIntegral a n) => Enum (Finite a n) where
    {-# SPECIALIZE instance KnownNat n => Enum (Finite Integer n) #-}
#if MIN_VERSION_base(4,8,0)
    {-# SPECIALIZE instance KnownNat n => Enum (Finite Natural n) #-}
#endif
    {-# SPECIALIZE instance KnownIntegral Word n => Enum (Finite Word n) #-}
    {-# SPECIALIZE instance KnownIntegral Int n => Enum (Finite Int n) #-}
    {-# SPECIALIZE instance KnownIntegral Word8 n => Enum (Finite Word8 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int8 n => Enum (Finite Int8 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word16 n => Enum (Finite Word16 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int16 n => Enum (Finite Int16 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word32 n => Enum (Finite Word32 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int32 n => Enum (Finite Int32 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word64 n => Enum (Finite Word64 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int64 n => Enum (Finite Int64 n) #-}
    succ (Finite x)
        | x == n - 1 = error "succ: bad argument"
        | otherwise = Finite $ succ x
        where n = intVal (Proxy :: Proxy n)
    pred (Finite x)
        | x == 0 = error "pred: bad argument"
        | otherwise = Finite $ pred x
    fromEnum = fromEnum . getFinite
    toEnum x
        | toInteger x < toInteger n && x >= 0 = Finite $ fromIntegral x
        | otherwise = error $ "toEnum: Int " ++ show x
            ++ " is not representable in Finite _ " ++ show (toInteger n)
        where n = intVal (Proxy :: Proxy n) :: a
    enumFrom x = enumFromTo x maxBound
    enumFromTo (Finite x) (Finite y) = Finite `fmap` enumFromTo x y
    enumFromThen x y
        = enumFromThenTo x y (if x >= y then minBound else maxBound)
    enumFromThenTo (Finite x) (Finite y) (Finite z)
        = Finite `fmap` enumFromThenTo x y z

instance Show a => Show (Finite a n) where
    showsPrec d (Finite x)
        = showParen (d > 9) $ showString "finite " . showsPrec 10 x

instance (Read a, SaneIntegral a, KnownIntegral a n) => Read (Finite a n) where
    readPrec = parens $ Text.ParserCombinators.ReadPrec.prec 10 $ do
        expectP (Ident "finite")
        x <- readPrec
        guard (x >= 0 && x < n)
        return $ Finite x
        where n = intVal (Proxy :: Proxy n)

-- | 'Prelude.+', 'Prelude.-', and 'Prelude.*' implement arithmetic modulo @n@.
-- The 'fromInteger' function raises an error for inputs outside of bounds.
instance (SaneIntegral a, KnownIntegral a n) => Num (Finite a n) where
    {-# SPECIALIZE instance KnownNat n => Num (Finite Integer n) #-}
#if MIN_VERSION_base(4,8,0)
    {-# SPECIALIZE instance KnownNat n => Num (Finite Natural n) #-}
#endif
    {-# SPECIALIZE instance KnownIntegral Word n => Num (Finite Word n) #-}
    {-# SPECIALIZE instance KnownIntegral Int n => Num (Finite Int n) #-}
    {-# SPECIALIZE instance KnownIntegral Word8 n => Num (Finite Word8 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int8 n => Num (Finite Int8 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word16 n => Num (Finite Word16 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int16 n => Num (Finite Int16 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word32 n => Num (Finite Word32 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int32 n => Num (Finite Int32 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word64 n => Num (Finite Word64 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int64 n => Num (Finite Int64 n) #-}
    Finite x + Finite y = Finite $ modAdd n x y
        where n = intVal (Proxy :: Proxy n)
    Finite x - Finite y = Finite $ modSub n x y
        where n = intVal (Proxy :: Proxy n)
    Finite x * Finite y = Finite $ modMul n x y
        where n = intVal (Proxy :: Proxy n)
    abs fx = fx
    signum (Finite x) = Finite $ if x == 0 then 0 else 1
    fromInteger x
        | x < toInteger n && x >= 0 = Finite $ fromInteger x
        | otherwise = error $ "fromInteger: Integer " ++ show x
            ++ " is not representable in Finite _ " ++ show (toInteger n)
        where n = intVal (Proxy :: Proxy n) :: a

instance (SaneIntegral a, KnownIntegral a n) => Real (Finite a n) where
    {-# SPECIALIZE instance KnownNat n => Real (Finite Integer n) #-}
#if MIN_VERSION_base(4,8,0)
    {-# SPECIALIZE instance KnownNat n => Real (Finite Natural n) #-}
#endif
    {-# SPECIALIZE instance KnownIntegral Word n => Real (Finite Word n) #-}
    {-# SPECIALIZE instance KnownIntegral Int n => Real (Finite Int n) #-}
    {-# SPECIALIZE instance KnownIntegral Word8 n => Real (Finite Word8 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int8 n => Real (Finite Int8 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word16 n => Real (Finite Word16 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int16 n => Real (Finite Int16 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word32 n => Real (Finite Word32 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int32 n => Real (Finite Int32 n) #-}
    {-# SPECIALIZE instance KnownIntegral Word64 n => Real (Finite Word64 n) #-}
    {-# SPECIALIZE instance KnownIntegral Int64 n => Real (Finite Int64 n) #-}
    toRational (Finite x) = toRational x

-- | 'quot' and 'rem' are the same as 'div' and 'mod' and they implement regular
-- division of numbers in the range @[0, n)@, __not__ modular inverses.
instance (SaneIntegral a, KnownIntegral a n) => Integral (Finite a n) where
    {-# SPECIALIZE instance KnownNat n => Integral (Finite Integer n) #-}
#if MIN_VERSION_base(4,8,0)
    {-# SPECIALIZE instance KnownNat n => Integral (Finite Natural n) #-}
#endif
    {-# SPECIALIZE instance KnownIntegral Word n => Integral (Finite Word n) #-}
    {-# SPECIALIZE instance KnownIntegral Int n => Integral (Finite Int n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word8 n => Integral (Finite Word8 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int8 n => Integral (Finite Int8 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word16 n => Integral (Finite Word16 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int16 n => Integral (Finite Int16 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word32 n => Integral (Finite Word32 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int32 n => Integral (Finite Int32 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Word64 n => Integral (Finite Word64 n) #-}
    {-# SPECIALIZE instance
        KnownIntegral Int64 n => Integral (Finite Int64 n) #-}
    quot (Finite x) (Finite y) = Finite $ quot x y
    rem (Finite x) (Finite y) = Finite $ rem x y
    quotRem (Finite x) (Finite y) = case quotRem x y of
        (q, r) -> (Finite q, Finite r)
    div (Finite x) (Finite y) = Finite $ div x y
    mod (Finite x) (Finite y) = Finite $ mod x y
    divMod (Finite x) (Finite y) = case divMod x y of
        (q, r) -> (Finite q, Finite r)
    toInteger (Finite x) = toInteger x

instance NFData a => NFData (Finite a n) where
    rnf (Finite x) = rnf x
