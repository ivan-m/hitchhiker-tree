{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs,
             KindSignatures, MultiParamTypeClasses, ScopedTypeVariables,
             TypeOperators #-}

{- |
   Module      : Data.Hitchhiker
   Description : The \"Data.Hitchhiker\" module
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Hitchhiker where

import Data.Hitchhiker.List

import Data.Proxy
import Data.Singletons.Prelude.Num
import Data.Singletons.TypeLits
import GHC.TypeLits

--------------------------------------------------------------------------------

data HTree l b k a where
  Partial :: forall c     l b k a. (1 <= c, c <= (b:-1))
             => Leaves c k a -> HTree l b k a

  Full    :: forall c e t l b k a. (2 <= c, c <= b, e <= l)
             => NodeLog e k a -> Children c t l b k a -> HTree l b k a

data Statement k a = Assert k a
                   | Retract k
  deriving (Eq, Ord, Show, Read)

type Log k a = [Statement k a]

type Leaves c k a = List c (k, Log k a)
type Children c t l b k a = List c (k, HNode t l b k a)

type NodeLog l k a = List l (Statement k a)

data NType = Internal | Leaf

-- | A node of type @t@ containing at most @l@ internal logs per node,
--   branch factor @b@, keys @k@ and values @a@.
data HNode (t :: NType) (l :: Nat) (b :: Nat) k a where
  HLeaf :: forall c      l b k a. (LeafC b c)
           => Leaves c k a -> HNode 'Leaf l b k a

  HInt  :: forall c e t' l b k a. (IntC b c, e <= l)
           => NodeLog e k a            -- ^ Internal log
           -> Children c t' l b k a    -- ^ Sub-nodes with minimum key
           -> HNode 'Internal l b k a

type LeafC b c = (b <= (2:*c + 2), c <= (b :- 1))
type IntC  b c = (b <= (2:*c), c <= b)
