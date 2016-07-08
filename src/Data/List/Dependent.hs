{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds, DeriveFunctor, GADTs, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}


{- |
   Module      : Data.List.Dependent
   Description : Dependently-typed lists
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

  A copy of the standard list data structure + associated functions
  where the length is statically known.

 -}
module Data.List.Dependent where

import Prelude hiding (concat, drop, length, splitAt, take, zip, zipWith, (++), replicate)

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.Prelude.Num
import Data.Singletons.TypeLits
import Data.Type.Equality
import GHC.TypeLits

import Control.Applicative             (liftA2)
import Data.Bifunctor                  (bimap, first)
import Data.Function                   (on)
import Data.List                       (unfoldr)
import GHC.Exts                        (IsList (..))
import Text.ParserCombinators.ReadPrec (ReadPrec, prec, (<++))
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

instance (Read a, KnownNat n) => Read (List n a) where
  readPrec = go sing
    where
      go :: forall n'. SNat n' -> ReadPrec (List n' a)
      go n = case testEquality n zero of
               Just Refl -> do Ident "Nil" <- lexP
                               return Nil
               _         -> parens . prec 10
                            $ do a <- readPrec
                                 Symbol ":|" <- lexP
                                 as <- go (sPred n)
                                 return (a :| as)

  readListPrec = readListPrecDefault

fromDependent :: forall n a. List n a -> [a]
fromDependent = go
  where
    go :: List n' a -> [a]
    go Nil = []
    go (a :| as) = a : go as

--------------------------------------------------------------------------------
-- Defining functions in the order of Data.List

---------------------
-- Basic functions --
---------------------

(++) :: forall n m a. List n a -> List m a -> List (n + m) a
ll ++ lr = go ll
  where
    go :: List n' a -> List (n' + m) a
    go ll' = case ll' of
               Nil     -> lr
               a :| as -> a :| go as

infixr 5 ++

head :: List (n+1) a -> a
head (a :| _) = a

last :: forall n a. (KnownNat n) => List (n+1) a -> a
last = go sing
  where
    go :: SNat n' -> List (n'+1) a -> a
    go n1 as = case as of
                 (a :| Nil) -> a
                 (_ :| as') -> go (sPred n1) as'

tail :: List (n+1) a -> List n a
tail (_ :| as) = as

init :: forall n a. (KnownNat n) => List (n+1) a -> List n a
init = go sing
  where
    go :: SNat n' -> List (n'+1) a -> List n' a
    go n1 as = case as of
                 (_ :| Nil) -> Nil
                 (a :| as') -> a :| go (sPred n1) as'

uncons :: List n a -> Maybe (a, List (n-1) a)
uncons as = case as of
               Nil      -> Nothing
               a :| as' -> Just (a, as')

-- Not sure why anyone would want to use this...
null :: List n a -> Bool
null Nil = True
null _   = False

-- O(1) !!!
length :: forall n a. (KnownNat n) => List n a -> Integer
length _ = natVal (Proxy :: Proxy n)

--------------------------
-- List transformations --
--------------------------

map :: (a -> b) -> List n a -> List n b
map = fmap

reverse :: forall n a. List n a -> List n a
reverse = go zero Nil
  where
    -- Without the SNat, we get "*** Exception: Prelude.foldr1: empty list" from ghc.
    go :: ((c + r) ~ n) => SNat c -> List c a -> List r a -> List n a
    go c lc lr = case lr of
                   Nil        -> lc
                   (a :| lr') -> go (sSucc c) (a :| lc) lr'

-- Note: doesn't handle the empty case
intersperse :: forall n a. a -> List (1+n) a -> List (1 + 2*n) a
intersperse e (a0 :| as0) = a0 :| go as0
  where
    go :: List n' a -> List (2*n') a
    go as = case as of
              Nil        -> Nil
              (a :| as') -> e :| a :| go as'

-- TODO: intercalate

transpose :: forall r c a. (KnownNat c) => List r (List c a) -> List c (List r a)
transpose = go sing
  where
    go :: SNat c' -> List r (List c' a) -> List c' (List r a)
    go c' rs = case testEquality c' zero of
                 Just Refl -> Nil
                 _         -> let (c, rs') = nextC rs
                              in c :| go (sPred c') rs'

    uncons' :: List (1+n) b -> (b, List n b)
    uncons' (b:|bs) = (b, bs)

    nextC = unzipWith uncons'

subsequences :: forall n a. List n a -> List (2^n) (SomeList a)
subsequences = go
  where
    go :: List n' a -> List (2^n') (SomeList a)
    go as = case as of
              Nil -> nilList :| Nil
              a :| as' -> let ss = go as'
                          in doubleLength ss (fmap (scons a) ss)

    -- Needed to convince the type-checker that (2^(n'-1) + 2^(n'-1)) ~ 2^n'
    doubleLength :: List (2^k) b -> List (2^k) b -> List (2^(k+1)) b
    doubleLength l1 l2 = l1 ++ l2

replicate :: forall n a. (KnownNat n) => a -> List n a
replicate a = go sing
  where
    go :: SNat n' -> List n' a
    go n = case testEquality n zero of
             Just Refl -> Nil
             _         -> a :| go (sPred n)

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

zipWith :: forall n a b c. (a -> b -> c) -> List n a -> List n b -> List n c
zipWith f = go
  where
    go :: List n' a -> List n' b -> List n' c
    go as bs = case (as, bs) of
                 (Nil,       Nil)      -> Nil
                 ~(a :| as', b :| bs') -> f a b :| go as' bs'

zip :: List n a -> List n b -> List n (a,b)
zip = zipWith (,)

unzipWith :: forall n a b c. (c -> (a,b)) -> List n c -> (List n a, List n b)
unzipWith f = go
  where
    go :: List n' c -> (List n' a, List n' b)
    go lab = case lab of
               Nil         -> (Nil, Nil)
               (c :| lab') -> let (a,b) = f c
                              in bimap (a:|) (b:|) (go lab')

unzip :: List n (a,b) -> (List n a, List n b)
unzip = unzipWith id

ordBuckets :: forall n k a. (Ord k) => List n (k,a) -> List n (k -> Bool)
ordBuckets lst = case lst of
                   Nil        -> Nil
                   (_ :| kas) -> go Nothing kas
  where
    go :: Maybe k -> List n' (k,a) -> List (n' + 1) (k -> Bool)
    go mk kas = case kas of
                  Nil             -> lowB mk :| Nil
                                     -- ^ This is either the only
                                     -- child - in which case case
                                     -- always insert here - or the
                                     -- last one, so no upper bound to
                                     -- worry about.
                  ((k,_) :| kas') -> liftA2 (&&) (lowB mk) (<k) :| go (Just k) kas'

    lowB = maybe (const True) (>=)

-- | Merging function is @f new old@.  Key-getting function assumed to
--   be O(1).
insertOrdOn :: forall n a k. (Ord k) => (a -> a -> a) -> (a -> k)
               -> a -> List n a -> Either (List n a) (List (n+1) a)
insertOrdOn mrg cmp v = go
  where
    go :: List n' a -> Either (List n' a) (List (n'+1) a)
    go as = case as of
              Nil      -> Right (v :| Nil)
              a :| as' -> case (compare `on` cmp) v a of
                            LT -> Right (v :| as)
                            EQ -> Left (mrg v a :| as')
                            GT -> a `eCons` go as'

    eCons :: forall n'. a -> Either (List (n'-1) a) (List n' a) -> Either (List n' a) (List (n'+1) a)
    eCons a = bimap (a:|) (a:|)

-- | TODO: is it worth trying to do a binary search?
lookupOrd :: forall n a k. (Ord k) => k -> List n (k,a) -> Maybe a
lookupOrd v = go
  where
    go :: List n' (k,a) -> Maybe a
    go kas = case kas of
               Nil           -> Nothing
               (k,a) :| kas' -> case compare v k of
                                  LT -> go kas'
                                  EQ -> Just a
                                  GT -> Nothing

-- | For a given key @k@ and indexed list, finds the first @a_i@ where
--   @k_i <= k < k_{i+1}@ (or @k_0@ if @k < k_0@).
-- ordRegion :: k ->

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
