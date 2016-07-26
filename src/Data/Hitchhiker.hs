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

import Prelude hiding (head, zipWith, (++))

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
import           GHC.Exts               (IsList (..))
import           Unsafe.Coerce          (unsafeCoerce)

--------------------------------------------------------------------------------

-- | A Hitchhiker Tree where each internal node stores at most @l@
--   messages and each non-root node has between @b@ and @2b@
--   children.
data HTree l b k a where
  Empty   :: HTree l b k a

  -- | Partial root node, acting like a leaf.
  Partial :: forall c     l b k a. (LeafC 1 b c)
             => Leaves c k a -> HTree l b k a

  -- | Full root node, acting like an internal node.
  Full    :: forall c e d l b k a. (IntC l 2 b e c)
             => NodeLog e k a -> Children c d l b k a -> HTree l b k a

-- c == number of children.
type Children c d l b k a = List c (k, HNode d l b k a)
type Leaves   c       k a = List c (k, Log k a)

deriving instance (Show k, Show a) => Show (HTree l b k a)

type LeafC   lb b   c = (1 ::<= lb, lb ::<= c, c ::<= (2:*b),                       KnownNat c)
type IntC  l lb b e c = (1 ::<= lb, lb ::<= c, c ::<= (2:*b), e ::<= l, KnownNat e, KnownNat c)

one :: SNat 1
one = SNat

two :: SNat 2
two = SNat

-- | A node of depth @d@ containing at most @l@ internal logs per node,
--   branch factor @b@, keys @k@ and values @a@.
data HNode (d :: Nat) (l :: Nat) (b :: Nat) k a where
  HLeaf :: forall c      l b k a. (LeafC b b c)
           => Leaves c k a -> HNode 0 l b k a

  HInt  :: forall c e d l b k a. (IntC l b b e c)
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

addStatements :: forall l b k a. (Ord k, KnownNat l, KnownNat b, 1 ::<= b)
                 => [Statement k a] -> HTree l b k a -> HTree l b k a
addStatements stmts ht
  = case fromList stmts of
      SomeList _ Nil -> ht
      SomeList _ lg  -> either snd handleOverflow
                          (case ht of
                             Empty -> addLeaves one Partial lg Nil -- TODO: how to define this?
                          )


  where
    handleOverflow :: SomeList (k, HNode d l b k a) -> HTree l b k a
    handleOverflow (SomeList c chld) = undefined
      where


addLog :: forall e d l b k a. (Ord k, KnownNat b, KnownNat e, KnownNat l, 1 ::<= b)
          => NodeLog e k a -> HNode d l b k a
          -> SomeList (k, HNode d l b k a)
addLog lgAdd hn = case hn of
  HLeaf lvs     -> eitherSList (addLeaves b HLeaf lgAdd lvs)
  HInt  lg chld -> eitherSList (addInternal b HInt lgAdd lg chld)
                   \\ intHasNonZeroD
  where
    b :: SNat b
    b = SNat

    eitherSList :: Either v (SomeList v) -> SomeList v
    eitherSList = either (`scons` nilList) id

    intHasNonZeroD :: () C.:- (1 ::<= d)
    intHasNonZeroD = unsafeCoerceConstraint

addLeaves :: forall e (l :: Nat) b k a c lb res.
             (Ord k, KnownNat b, KnownNat c, 1 ::<= b, KnownNat lb, lb ::<= c, 1 ::<= lb, lb ::<= b)
             => SNat lb -> (forall c'. (LeafC lb b c') => Leaves c' k a -> res l b k a)
             -> NodeLog e k a -> Leaves c k a -> Either (k, res l b k a) (SomeList (k, HNode 0 l b k a))
addLeaves lb mkRes lg lvs =
  case insertOrdAll mappend (fromLog lg) lvs of
     SomeList lc' lvs' -> case trueOrFalse (ub %:<  lc') of
       Left Refl -> (case splitNode lc' lvs'  of
         (rb,ql,q,r) -> Right (mkLeaf rb `scons` someList (fmap mkLeaf ql))
                              \\ halfLT b
                              \\ stillNatPlus r b
                              \\ stillNatPred q
                              \\ nonZeroQuot lc' b
                              \\ monotInc r
                              \\ validQuotRem lc' b
                              \\ lbLTub)
                      \\ doubleLT b lc'
                      \\ stillLT lc'
       -- This is going to be true by construction, but have to prove it.
       Right Refl -> Left (sameLevel lvs') \\ transitiveLT lb lc'
                                           \\ stillLT lc'
                                           \\ invGT ub lc'

  where
    b :: SNat b
    b = SNat

    ub :: SNat (2:*b)
    ub = two %:* b

    fromLog :: NodeLog c' k' a' -> List c' (k', [Statement k' a'])
    fromLog = fmap (liftA2 (,) keyFor (:[]))

    -- Because r < b, r+b < 2b, thus upper bound is not violated.  We
    -- just need to tell GHC that.
    splitNode :: (HasQuotRem c' b, b ::<= c')
                 => SNat c' -> List c' v
                 -> (List (Rem c' b + b) v, List (Quot c' b :- 1) (List b v), SNat (Quot c' b), SNat (Rem c' b))
    splitNode c' ls = (case splitInto ls of
                         (r, lq) -> case uncons' lq of
                                      (l, q) -> (r ++ l, q, SNat, SNat)
                      ) \\ nonZeroQuot c' b -- Avoid complaining about missing case
                        \\ validQuotRem c' b
                        \\ transitiveLT b b

    mkLeaf :: (KnownNat c', b ::<= c', 1 ::<= c', c' ::<= (2:*b)) => Leaves c' k a -> (k, HNode 0 l b k a)
    mkLeaf lvs' = (fst (head' lvs'), HLeaf lvs')

    sameLevel :: (KnownNat c', lb ::<= c', 1 ::<= c', c' ::<= (2:*b)) => Leaves c' k a -> (k, res l b k a)
    sameLevel lvs' = (fst (head' lvs'), mkRes lvs')

    -- The type-checker needs some help

    lbLTub :: (1 ::<= lb, lb ::<= b) C.:- (lb ::<= 2 :* b)
    lbLTub = unsafeCoerceConstraint

    -- 1 <= lb, 0 <= r, lb <= b
    monotInc :: proxy r -> ((r :< b) ~ 'True) C.:- (b ::<= (r + b), 1 ::<= (r+b), (r+b) ::<= 2:*b)
    monotInc _ = unsafeCoerceConstraint

    -- insertOrdAll can't decrease the number of values
    stillLT :: proxy c' -> (lb ::<= c) C.:- (lb ::<= c')
    stillLT _ = unsafeCoerceConstraint

addInternal :: forall d l b k a lb lc e c res.
               (Ord k, IntC l lb b e c, KnownNat b, KnownNat l, KnownNat lc, 1 ::<= b, KnownNat lb, lb ::<= c, 1 ::<= lb, lb ::<= b, e ::<= l, 1 ::<= d)
               => SNat lb -> (forall e' c'. (IntC l lb b e' c') => NodeLog e' k a -> Children c' (d:-1) l b k a -> res l b k a)
               -> NodeLog lc k a -> NodeLog e k a -> Children c (d:-1) l b k a
               -> Either (k, res l b k a) (SomeList (k, HNode d l b k a))
addInternal lb mkRes lgAdd lg chld
  = case trueOrFalse (l %:< e') of
      Left Refl -> case mkChildren chld of
        SomeList c' chld' -> case trueOrFalse (ub %:< c') of
          Left Refl ->
            (case splitChildren c' chld' of
              (rb,ql,q,r) -> Right (mkNode rb `scons` someList (fmap mkNode ql))
                                   \\ halfLT b
                                   \\ monotInc r
                                   \\ stillNatPred q
                                   \\ nonZeroQuot c' b
                                   \\ stillNatPlus r b
                                   \\ validQuotRem c' b
            ) \\ doubleLT b c'
          Right Refl -> Left (sameLevel Nil chld') \\ stillLT c'
                                                   \\ invGT ub c'
                                                   \\ zeroAlwaysLT l

      Right Refl -> Left (sameLevel lg' chld) \\ invGT l e'
                                              \\ hasLCE

  where
    b :: SNat b
    b = SNat

    ub :: SNat (2:*b)
    ub = two %:* b

    l :: SNat l
    l = SNat

    hasLCE = stillNatPlus (SNat :: SNat lc) (SNat :: SNat e)

    lg' = lgAdd ++ lg

    e' = lengthNat lg' \\ hasLCE

    lgBkts :: List c (SomeList (Statement k a))
    lgBkts = go (ordBuckets chld) (someList lg' \\ hasLCE)
      where
        go :: forall c'. List c' (k -> Bool) -> SomeList (Statement k a) -> List c' (SomeList (Statement k a))
        go ps (SomeList _ stmts) = case ps of
                                     Nil      -> Nil
                                     p :| ps' -> case partition (p . keyFor) stmts of
                                                   (pStmts, stmts') -> pStmts :| go ps' stmts'

    addLogsTo :: SomeList (Statement k a) -> (k,HNode (d:-1) l b k a) -> SomeList (k, HNode (d:-1) l b k a)
    addLogsTo (SomeList _ Nil) kn    = kn `scons` nilList
    addLogsTo (SomeList _ clg) (_,n) = addLog clg n

    mkChildren = concatS . zipWith addLogsTo lgBkts

    splitChildren :: (HasQuotRem c' b, b ::<= c')
                     => SNat c' -> List c' v
                     -> (List (Rem c' b + b) v
                        , List (Quot c' b :- 1) (List b v)
                        , SNat (Quot c' b)
                        , SNat (Rem c' b))
    splitChildren c' chld' = (case splitInto chld' of
                                (r,lq) -> case uncons' lq of
                                            (q,qs) -> (r++q, qs, SNat, SNat)
                             ) \\ validQuotRem c' b
                               \\ nonZeroQuot c' b

    mkNode :: forall c'. (KnownNat c', b ::<= c', c' ::<= (2:*b))
              => Children c' (d:-1) l b k a -> (k, HNode d l b k a)
    mkNode chld' = (fst (head' chld'), HInt Nil chld') \\ zeroAlwaysLT l
                                                       \\ transitiveLT b (SNat :: SNat c')

    sameLevel :: forall e' c'. (IntC l lb b e' c') => NodeLog e' k a -> Children c' (d:-1) l b k a
                 -> (k, res l b k a)
    sameLevel newLg chld' = (fst (head' chld'), mkRes newLg chld') \\ transitiveLT lb (SNat :: SNat c')

    monotInc :: proxy r -> ((r :< b) ~ 'True) C.:- (b ::<= (r + b), (r+b) ::<= 2:*b)
    monotInc _ = unsafeCoerceConstraint

    -- insertOrdAll can't decrease the number of values
    stillLT :: proxy c' -> (lb ::<= c) C.:- (lb ::<= c')
    stillLT _ = unsafeCoerceConstraint

halfLT :: proxy b -> () C.:- (b ::<= 2 :* b)
halfLT _ = unsafeCoerceConstraint

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

zeroAlwaysLT :: proxy a -> () C.:- (0 ::<= a)
zeroAlwaysLT _ = unsafeCoerceConstraint
