{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances,
             FunctionalDependencies, KindSignatures, MultiParamTypeClasses,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{- |
   Module      : Data.List.Dependent.Numeric
   Description : Extra number mangling
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.List.Dependent.Numeric where

import Data.Singletons.Prelude
import GHC.TypeLits

--------------------------------------------------------------------------------

class (KnownNat n, KnownNat d, KnownNat q, KnownNat r
      , 1 <= d, n ~ (q :* d + r), (r :< d) ~ 'True) => DivMod n d q r | n d -> q, n d -> r, q r d -> n

instance (KnownNat n, KnownNat d, KnownNat q, KnownNat r
         , 1 <= d, DivMod' n d q r (Compare n d), (r :< d) ~ 'True) => DivMod n d q r

class (1 <= d, n ~ (d :* q + r), Compare n d ~ cmp) => DivMod' (n :: Nat) (d :: Nat)
                                                               (q :: Nat) (r :: Nat)
                                                               (cmp :: Ordering)
                                                               | n d cmp -> q, n d cmp -> r, q r d -> n

instance (1 <= d, Compare n d ~ 'LT) => DivMod' n d 0 n 'LT
instance (1 <= n) => DivMod' n n 1 0 'EQ
instance (1 <= d, DivMod' (n :- d) d (q :- 1) r (Compare (n :- d) d), Compare n d ~ 'GT) => DivMod' n d q r 'GT
