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
        Finite(Finite)
    )
    where

import GHC.TypeLits
import GHC.Generics

-- | Finite number type. @'Finite' n@ is inhabited by exactly @n@ values. Invariants:
--
-- prop> getFinite x < natVal x
-- prop> getFinite x >= 0
newtype Finite (n :: Nat) = Finite Integer
                          deriving (Generic)
