{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs,
             KindSignatures, MultiParamTypeClasses, ScopedTypeVariables,
             StandaloneDeriving, TypeOperators #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{- |
   Module      : Data.Hitchhiker
   Description : The \"Data.Hitchhiker\" module
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Hitchhiker where

import Prelude hiding (head, (++))

import Data.List.Dependent

-- Until the list module re-exports this
import Data.List.Dependent.Numeric

import Data.Singletons.Prelude
import Data.Singletons.Prelude
import Data.Singletons.TypeLits
import GHC.TypeLits

import Control.Applicative (liftA2)
import Data.Bifunctor      (second)
import Data.Constraint     hiding ((:-))

--------------------------------------------------------------------------------

-- | A Hitchhiker Tree where each internal node stores at most @l@
--   messages and each non-root node has between @b@ and @2b@
--   children.
data HTree l b k a where
  Empty   :: HTree l b k a

  -- | Partial root node, acting like a leaf.
  Partial :: forall c     l b k a. (1 <= c, c <= 2:*b)
             => Leaves c k a -> HTree l b k a

  -- | Full root node, acting like an internal node.
  Full    :: forall c e d l b k a. (2 <= c, c <= (2:*b), e <= l)
             => NodeLog e k a -> Children c d l b k a -> HTree l b k a

-- c == number of children.
type Children c d l b k a = List c (k, HNode d l b k a)
type Leaves   c       k a = List c (k, Log k a)

deriving instance (Show k, Show a) => Show (HTree l b k a)

-- | A node of depth @d@ containing at most @l@ internal logs per node,
--   branch factor @b@, keys @k@ and values @a@.
data HNode (d :: Nat) (l :: Nat) (b :: Nat) k a where
  HLeaf :: forall c      l b k a. (b <= c, c <= (2:*b), KnownNat c)
           => Leaves c k a -> HNode 0 l b k a

  HInt  :: forall c e d l b k a. (b <= c, c <= (2:*b), e <= l, KnownNat c, KnownNat e)
           => NodeLog e k a             -- ^ Internal log
           -> Children c (d:-1) l b k a -- ^ Sub-nodes with minimum key
           -> HNode d l b k a

deriving instance (Show k, Show a) => Show (HNode d l b k a)

--------------------------------------------------------------------------------

-- | Specify a change in value @a@ for a particular key @k@.
data Statement k a = Assert k a
                   | Retract k
  deriving (Eq, Ord, Show, Read)

keyFor :: Statement k a -> k
keyFor (Assert  k _) = k
keyFor (Retract k)   = k

type Log k a = [Statement k a]
type NodeLog l k a = List l (Statement k a)

--------------------------------------------------------------------------------

-- addLog :: forall e d l b k a. (Ord k, KnownNat b, 1 <= b) => NodeLog e k a -> (k, HNode d l b k a)
--           -> SomeList (k, HNode d l b k a)
-- addLog lg (k0,hn) = case hn of
--                       HLeaf lvs -> case insertOrdAll mappend (fromLog lg) lvs of
--                                      SomeList lc' lvs' -> case fromSing (sCompare lc' ub) of
--                                         GT -> case splitNode lc' lb lvs' of
--                                                 (rb,q) -> mkLeaf rb `scons` someList (fmap mkLeaf q)
--   where
--     lb :: SNat b
--     lb = SNat

--     ub :: SNat (2 :* b)
--     ub = (SNat :: SNat 2) %:* lb

--     fromLog :: NodeLog c' k' a' -> List c' (k', [Statement k' a'])
--     fromLog = fmap (liftA2 (,) keyFor (:[]))

--     -- Because r < b, r+b < 2b, thus upper bound is not violated.  We
--     -- just need to tell GHC that.
--     splitNode :: (CalcQuotRem c b, 1 <= Quot c b)
--                  => SNat c -> SNat b -> List c v -> (List (Rem c b +b) v, List (Quot c b :- 1) (List b v))
--     splitNode SNat SNat ls = case splitInto ls of
--                                (r,(l :| q)) -> (r ++ l, q)

--     mkLeaf :: (KnownNat c, b <= c, 1 <= c, c <= (2:*b)) => Leaves c k a -> (k, HNode 0 l b k a)
--     mkLeaf lvs = (fst (head' lvs), HLeaf lvs)

--     -- The type-checker isn't too smart

-- blah :: (KnownNat b, b <= (2 :* b)) => SNat b -> Integer
-- blah = natVal
