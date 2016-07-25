{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, GADTs,
             KindSignatures, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, StandaloneDeriving, TypeOperators #-}

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
import Data.Singletons.Prelude.Enum
import Data.Singletons.TypeLits
import Data.Type.Equality
import GHC.TypeLits

import           Control.Applicative    (liftA2)
import           Data.Bifunctor         (second)
import           Data.Constraint        hiding ((:-))
import qualified Data.Constraint        as C
import           Data.Constraint.Unsafe (unsafeCoerceConstraint)
import           Unsafe.Coerce          (unsafeCoerce)

--------------------------------------------------------------------------------

-- | A Hitchhiker Tree where each internal node stores at most @l@
--   messages and each non-root node has between @b@ and @2b@
--   children.
data HTree l b k a where
  Empty   :: HTree l b k a

  -- | Partial root node, acting like a leaf.
  Partial :: forall c     l b k a. (1 ::<= c, c ::<= 2:*b)
             => Leaves c k a -> HTree l b k a

  -- | Full root node, acting like an internal node.
  Full    :: forall c e d l b k a. (2 ::<= c, c ::<= (2:*b), e ::<= l)
             => NodeLog e k a -> Children c d l b k a -> HTree l b k a

-- c == number of children.
type Children c d l b k a = List c (k, HNode d l b k a)
type Leaves   c       k a = List c (k, Log k a)

deriving instance (Show k, Show a) => Show (HTree l b k a)

-- | A node of depth @d@ containing at most @l@ internal logs per node,
--   branch factor @b@, keys @k@ and values @a@.
data HNode (d :: Nat) (l :: Nat) (b :: Nat) k a where
  HLeaf :: forall c      l b k a. (b ::<= c, c ::<= (2:*b), KnownNat c)
           => Leaves c k a -> HNode 0 l b k a

  HInt  :: forall c e d l b k a. (b ::<= c, c ::<= (2:*b), e ::<= l, KnownNat c, KnownNat e)
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

addLog :: forall e d l b k a. (Ord k, KnownNat b, 1 ::<= b) => NodeLog e k a -> (k, HNode d l b k a)
          -> SomeList (k, HNode d l b k a)
addLog lg (k0,hn) = case hn of
  HLeaf lvs -> addLeaves b HLeaf lg lvs

  where
    b :: SNat b
    b = SNat

addLeaves :: forall e (l :: Nat) b k a c lb res.
             (Ord k, KnownNat b, KnownNat c, 1 ::<= b, KnownNat lb, lb ::<= c, 1 ::<= lb, lb ::<= b)
             => SNat lb -> (forall c'. (KnownNat c', lb ::<= c', c' ::<= 2 :* b) => Leaves c' k a -> res l b k a)
             -> NodeLog e k a -> Leaves c k a -> SomeList (k, res l b k a)
addLeaves lb mkRes lg lvs =
  case insertOrdAll mappend (fromLog lg) lvs of
     SomeList lc' lvs' -> case trueOrFalse (ub %:<  lc') of
       Left Refl -> (case splitNode lc' lvs'  of
         (rb,ql,q,r) -> (mkLeaf rb `scons` someList (fmap mkLeaf ql))
                        \\ stillNatPlus r lb
                        \\ stillNatPred q
                        \\ nonZeroQuot lc' lb
                        \\ monotInc r
                        \\ validQuotRem lc' lb
                        \\ lbLTub)
                      \\ doubleLT b lc'
                      \\ stillLT lc'
       -- This is going to be true by construction, but have to prove it.
       Right Refl -> scons (mkLeaf lvs') nilList \\ transitiveLT lb lc'
                                                 \\ stillLT lc'
                                                 \\ invGT ub lc'

  where
    b :: SNat b
    b = SNat

    ub :: SNat (2:*b)
    ub = (SNat :: SNat 2) %:* b

    fromLog :: NodeLog c' k' a' -> List c' (k', [Statement k' a'])
    fromLog = fmap (liftA2 (,) keyFor (:[]))

    -- Because r < b, r+b < 2b, thus upper bound is not violated.  We
    -- just need to tell GHC that.
    splitNode :: (HasQuotRem c' lb, lb ::<= c')
                 => SNat c' -> List c' v
                 -> (List (Rem c' lb + lb) v, List (Quot c' lb :- 1) (List lb v), SNat (Quot c' lb), SNat (Rem c' lb))
    splitNode c' ls = (case splitInto ls of
                         (r, lq) -> case uncons' lq of
                                      (l, q) -> (r ++ l, q, SNat, SNat)
                      ) \\ nonZeroQuot c' lb -- Avoid complaining about missing case
                        \\ validQuotRem c' lb
                        \\ transitiveLT lb b

    mkLeaf :: (KnownNat c', lb ::<= c', 1 ::<= c', c' ::<= (2:*b)) => Leaves c' k a -> (k, res l b k a)
    mkLeaf lvs' = (fst (head' lvs'), mkRes lvs')

    -- The type-checker needs some help

    lbLTub :: (1 ::<= lb, lb ::<= b) C.:- (lb ::<= 2 :* b)
    lbLTub = unsafeCoerceConstraint

    -- 1 <= lb, 0 <= r, lb <= b
    monotInc :: proxy r -> ((r :< lb) ~ 'True) C.:- (lb ::<= (r + lb), 1 ::<= (r+lb), (r+lb) ::<= 2:*b)
    monotInc _ = unsafeCoerceConstraint

    -- insertOrdAll can't decrease the number of values
    stillLT :: proxy c' -> (lb ::<= c) C.:- (lb ::<= c')
    stillLT _ = unsafeCoerceConstraint

doubleLT :: SNat a -> SNat b -> ((2:*a :< b) ~ 'True) C.:- (a ::<= b)
doubleLT _ _ = unsafeCoerceConstraint

stillNatPlus :: proxy a -> proxy b -> (KnownNat a, KnownNat b) C.:- (KnownNat (a+b))
stillNatPlus _ _ = unsafeCoerceConstraint

stillNatPred :: proxy n -> (KnownNat n, 1 ::<= n) C.:- (KnownNat (Pred n))
stillNatPred _ = unsafeCoerceConstraint

transitiveLT :: proxy a -> proxy b -> (1 ::<= a, a ::<= b) C.:- (1 ::<= b)
transitiveLT _ _ = unsafeCoerceConstraint

invGT :: SNat a -> SNat b -> ((a :< b) ~ 'False) C.:- (b ::<= a)
invGT _ _ = unsafeCoerceConstraint

trueOrFalse :: SBool b -> Either (b :~: 'True) (b :~: 'False)
trueOrFalse b = case testEquality b STrue of
                  Just Refl -> Left Refl
                  Nothing   -> Right (unsafeCoerce Refl)
