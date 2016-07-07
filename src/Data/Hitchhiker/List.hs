{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleContexts, FlexibleInstances,
             GADTs, ScopedTypeVariables, StandaloneDeriving, TypeFamilies,
             TypeOperators, UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

{- |
   Module      : Data.Hitchhiker.List
   Description : Dependently-typed lists
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Hitchhiker.List where

import Prelude hiding (concat, drop, length, splitAt, take, (++))

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TypeLits
import Data.Type.Equality
import GHC.TypeLits

import Control.Arrow                   (first)
import Data.Function                   (on)
import Data.List                       (unfoldr)
import GHC.Exts                        (IsList (..))
import Text.ParserCombinators.ReadPrec (prec, (<++))
import Text.Read                       (Lexeme (Ident, Symbol), Read (..), lexP,
                                        parens, readListPrecDefault, readPrec)

--------------------------------------------------------------------------------

data List :: Nat -> * -> * where
  Nil :: List 0 a
  (:|) :: a -> List (n - 1) a -> List n a

infixr 5 :|

deriving instance (Eq a) => Eq (List n a)
deriving instance (Ord a) => Ord (List n a)
deriving instance (Show a) => Show (List n a)
deriving instance Functor (List n)

instance {-# OVERLAPPING #-} Read (List 0 a) where
  readPrec = do Ident "Nil" <- lexP
                return Nil

  readListPrec = readListPrecDefault

instance (Read a, Read (List (n-1) a)) => Read (List n a) where
  readPrec = parens . prec 10
             $ do a <- readPrec
                  Symbol ":|" <- lexP
                  as <- readPrec
                  return (a :| as)

  readListPrec = readListPrecDefault

take :: forall n r a. (KnownNat n) => List (n + r) a -> List n a
take = go sing
  where
    go :: SNat n' -> List (n' + r) a -> List n' a
    go n' as = case (testEquality n' zero, as) of
                 (Just Refl, _)           -> Nil
                 (_,         ~(a :| as')) -> a :| go (sPred n') as'

drop :: forall n r a. (KnownNat r) => List (r + n) a -> List n a
drop = go sing
  where
    go :: SNat r' -> List (r' + n) a -> List n a
    go r' as = case (testEquality r' zero, as) of
                 (Just Refl, _)           -> as
                 (_,         ~(_ :| as')) -> go (sPred r') as'

splitAt :: forall n l r a. (KnownNat l, (l + r) ~ n) => List n a -> (List l a, List r a)
splitAt = go sing
  where
    go :: forall l' n'. ((l' + r) ~ n') => SNat l' -> List n' a -> (List l' a, List r a)
    go l' as = case (testEquality l' zero, as) of
                 (Just Refl, _)           -> (Nil, as)
                 -- We know that this must be a :| since n, l, r >= 0
                 (_,         ~(a :| as')) -> first (a:|) (go (sPred l') as')

zero :: SNat 0
zero = SNat

uncons :: List (n + 1) a -> (a, List n a)
uncons (a :| as) = (a, as)

uncons' :: List n a -> Maybe (a, List (n-1) a)
uncons' as = case as of
                Nil      -> Nothing
                a :| as' -> Just (a, as')

(++) :: forall n m a. List n a -> List m a -> List (n + m) a
ll ++ lr = go ll
  where
    go :: List n' a -> List (n' + m) a
    go ll' = case ll' of
               Nil     -> lr
               a :| as -> a :| go as

infixr 5 ++

length :: forall n a. (KnownNat n) => List n a -> Integer
length _ = natVal (Proxy :: Proxy n)

-- | Merging function is @f new old@.  Comparison function assumed to
-- be O(1).  Result will have length of either @n@ or @n+1@.
insertOrdOn :: forall n a b. (KnownNat n, Ord b) => (a -> a -> a) -> (a -> b)
               -> a -> List n a -> SomeList a
insertOrdOn mrg cmp v = go sing
  where
    go :: (KnownNat n') => SNat n' -> List n' a -> SomeList a
    go n as = case as of
                Nil -> SomeList SNat (v :| Nil)
                a :| as' -> case (compare `on` cmp) v a of
                              LT -> v `scons` someList as
                              EQ -> someList ((mrg v a) :| as')
                              GT -> let n' = sPred n
                                    in withKnownNat n' (a `scons` go n' as')

--------------------------------------------------------------------------------

data SomeList :: * -> * where
  SomeList :: forall n a. (KnownNat n) => SNat n -> List n a -> SomeList a

someList :: (KnownNat n) => List n a -> SomeList a
someList = SomeList SNat

nilList :: SomeList a
nilList = SomeList zero Nil

instance (Eq a) => Eq (SomeList a) where
  (SomeList nl ll) == (SomeList nr lr)
    = case testEquality nl nr of
        Just Refl -> withKnownNat nl (withKnownNat nr (ll == lr))
        Nothing   -> False

-- | Compares on lengths before comparing on values.
instance (Ord a) => Ord (SomeList a) where
  compare (SomeList nl ll) (SomeList nr lr) =
    case (fromSing (sCompare nl nr), testEquality nl nr) of
      -- Malformed instances may end up having this return (EQ, Nothing)...
      (EQ, Just Refl) -> compare ll lr
      (ne,_)          -> ne

instance (Show a) => Show (SomeList a) where
  showsPrec d (SomeList _ l) = showsPrec d l

instance (Read a) => Read (SomeList a) where
  readPrec = (do Ident "Nil" <- lexP
                 return nilList)
             <++
             (parens . prec 10 $ do a <- readPrec
                                    Symbol ":|" <- lexP
                                    as <- readPrec
                                    return (scons a as))

instance Monoid (SomeList a) where
  mempty = nilList

  mappend = append

  mconcat = concat

scons :: a -> SomeList a -> SomeList a
scons a sl = case sl of
               SomeList n as -> let m = sSucc n
                                in withKnownNat n (withKnownNat m (SomeList m (a :| as)))

unscons :: SomeList a -> Maybe (a, SomeList a)
unscons (SomeList n as) = case as of
                            Nil      -> Nothing
                            a :| as' -> let m = sPred n
                                        in withKnownNat m (Just (a, SomeList m as'))

instance IsList (SomeList a) where
  type Item (SomeList a) = a

  fromList = foldr scons nilList

  toList = unfoldr unscons

append :: SomeList a -> SomeList a -> SomeList a
append (SomeList nl ll) (SomeList nr lr)
  = let n = nl %:+ nr
    in withKnownNat n (SomeList n (ll ++ lr))

concat :: [SomeList a] -> SomeList a
concat = foldr append nilList

slength :: SomeList a -> Integer
slength (SomeList n _) = natVal n
