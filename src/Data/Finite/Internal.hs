--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Finite
-- Copyright   :  (C) 2022-2023 mniip
-- License     :  BSD3
-- Maintainer  :  mniip <mniip@mniip.com>
-- Stability   :  experimental
-- Portability :  portable
--------------------------------------------------------------------------------
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
module Data.Finite.Internal
    (
        Finite, pattern Finite,
        finite, getFinite
    )
    where

import GHC.TypeLits

import qualified Data.Finite.Internal.Integral as I

-- | Finite number type. The type @'Finite' n@ is inhabited by exactly @n@
-- values in the range @[0, n)@ including @0@ but excluding @n@. Invariants:
--
-- prop> getFinite x < natVal x
-- prop> getFinite x >= 0
type Finite = I.Finite Integer

#if __GLASGOW_HASKELL__ >= 710
pattern Finite :: forall n. Integer -> Finite n
#endif
pattern Finite x = I.Finite (x :: Integer)

-- | Convert an 'Integer' into a 'Finite', throwing an error if the input is out
-- of bounds.
finite :: forall n. KnownNat n => Integer -> Finite n
finite = I.finite

-- | Convert a 'Finite' into the corresponding 'Integer'.
getFinite :: forall n. Finite n -> Integer
getFinite = I.getFinite
