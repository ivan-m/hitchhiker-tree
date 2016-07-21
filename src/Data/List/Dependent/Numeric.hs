{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
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

import           Data.Constraint        hiding ((:-))
import qualified Data.Constraint        as C
import           Data.Constraint.Unsafe (unsafeCoerceConstraint)

--------------------------------------------------------------------------------

type (::<=) (x :: Nat) (y :: Nat) = (x :<= y) ~ 'True

infixl 4 ::<=

class (KnownNat n, KnownNat d, KnownNat q, KnownNat r
      , 1 ::<= d, n ~ (q :* d + r), (r :< d) ~ 'True) => DivMod n d q r | n d -> q, n d -> r, q r d -> n

instance (KnownNat n, KnownNat d, KnownNat q, KnownNat r
         , 1 ::<= d, DivMod' n d q r (Compare n d), (r :< d) ~ 'True) => DivMod n d q r

class (1 ::<= d, n ~ (d :* q + r), Compare n d ~ cmp) => DivMod' (n :: Nat) (d :: Nat)
                                                               (q :: Nat) (r :: Nat)
                                                               (cmp :: Ordering)
                                                               | n d cmp -> q, n d cmp -> r, q r d -> n

instance (1 ::<= d, Compare n d ~ 'LT) => DivMod' n d 0 n 'LT
instance (1 ::<= n) => DivMod' n n 1 0 'EQ
instance (1 ::<= d, DivMod' (n :- d) d (q :- 1) r (Compare (n :- d) d), Compare n d ~ 'GT) => DivMod' n d q r 'GT

type family QuotRem (n :: Nat) (d :: Nat) :: (Nat, Nat) where
  QuotRem n 0 = '(0, n)
  QuotRem n d = QuotRem' n d 0 (Compare n d)

type family QuotRem' (n :: Nat) (d :: Nat) (q' :: Nat) (cmp :: Ordering) :: (Nat, Nat) where
  QuotRem' n d q 'LT = '(0, n)
  QuotRem' d d q 'EQ = '(q, 0)
  QuotRem' n d q 'GT = QuotRem' (n :- d) d (q + 1) (Compare (n :- d) d)

type Quot n d = Fst (QuotRem n d)
type Rem  n d = Snd (QuotRem n d)

-- | True by construction, but can't be proven\/derived by GHC.
validQuotRem :: proxy n -> proxy d -> (HasQuotRem n d) C.:- (n ~ (d :* Quot n d + Rem n d), KnownNat (Quot n d), KnownNat (Rem n d), (Rem n d :< d) ~ 'True)
validQuotRem _ _ = unsafeCoerceConstraint

nonZeroQuot :: proxy n -> proxy d -> (d ::<= n) C.:- (1 ::<= Quot n d)
nonZeroQuot _ _ = unsafeCoerceConstraint

class    (KnownNat n, KnownNat d) => HasQuotRem n d
instance (KnownNat n, KnownNat d) => HasQuotRem n d
