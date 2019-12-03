
{-# LANGUAGE TypeOperators, DataKinds, TypeFamilies, FlexibleContexts,
  AllowAmbiguousTypes, RankNTypes, ScopedTypeVariables, TypeApplications #-}

module Data.Finite.Internal.With
    (
        withFinite
    )
    where

import Data.Kind
import Data.Proxy
import Data.Type.Equality
import GHC.TypeNats
import Unsafe.Coerce

import Data.Finite.Internal

-- | Pass a 'Finite' to a function expecting a type-level natural (passed via a 'Proxy').
withFinite
  :: forall (n :: Nat) (r :: Type)
  .  ( forall i. ( KnownNat i, CmpNat i n ~ 'LT ) => Proxy i -> r )
  -> Finite n
  -> r
withFinite f j = case someNatVal ( fromIntegral $ getFinite j ) of
  ( SomeNat ( px :: Proxy j ) ) ->
    case unsafeCoerce Refl :: CmpNat j n :~: 'LT of
      Refl -> f px
