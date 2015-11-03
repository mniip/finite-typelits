{-# LANGUAGE KindSignatures, DataKinds #-}
module Data.Finite.Internal
    (
        Finite(Finite)
    )
    where

import GHC.TypeLits

-- | Finite number type. @'Finite' n@ is inhabited by exactly @n@ values. Invariants:
--
-- prop> getFinite x < natVal x
-- prop> getFinite x >= 0
data Finite (n :: Nat) = Finite Integer
