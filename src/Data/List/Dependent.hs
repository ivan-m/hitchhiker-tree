{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleContexts, GADTs,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             StandaloneDeriving, TypeFamilies, TypeOperators #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

{- |
   Module      : Data.List.Dependent
   Description : Dependently-typed lists
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

  A copy of the standard list data structure + associated functions
  where the length is statically known.

  TODO:

  * Flesh out functions

  * Document

  * Determine how to specify constraints on SomeList (e.g. non-empty, <=)

 -}
module Data.List.Dependent where

import Data.List.Dependent.Numeric

import           Prelude hiding (Foldable (..), break, concat, drop, iterate,
                          length, map, replicate, span, splitAt, take, zip,
                          zipWith, (++))
import qualified Prelude as P

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.TypeLits
import Data.Type.Equality
import GHC.TypeLits

import Control.DeepSeq (NFData (..))
import           Control.Applicative             (liftA2)
import           Data.Bifunctor                  (bimap, first, second)
import           Data.Bool
import           Data.Constraint                 hiding ((:-), ins)
import qualified Data.Constraint                 as C
import           Data.Constraint.Unsafe          (unsafeCoerceConstraint)
import           Data.List                       (unfoldr)
import           GHC.Exts                        (IsList (..))
import           Text.ParserCombinators.ReadPrec (ReadPrec, prec, (<++))
import           Text.Read                       (Lexeme (Ident, Symbol),
                                                  Read (..), lexP, parens,
                                                  readListPrecDefault, readPrec)

--------------------------------------------------------------------------------

data List :: Nat -> * -> * where
  Nil :: List 0 a
  (:|) :: a -> List (n - 1) a -> List n a

infixr 5 :|

deriving instance (Eq a) => Eq (List n a)
deriving instance (Ord a) => Ord (List n a)
deriving instance (Show a) => Show (List n a)
deriving instance Functor (List n)

instance (NFData a) => NFData (List n a) where
  rnf Nil       = ()
  rnf (a :| as) = rnf a `seq` rnf as

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

-- | Probably not very efficient as it requires recursing down all the
--   instances.
instance P.Foldable (List n) where

  foldMap f as = case as of
                   Nil        -> mempty
                   (a :| as') -> f a `mappend` P.foldMap f as'

fromDependent :: forall n a. List n a -> [a]
fromDependent = go
  where
    go :: List n' a -> [a]
    go Nil = []
    go (a :| as) = a : go as

data SomeList :: * -> * where
  SomeList :: forall n a. (KnownNat n) => SNat n -> List n a -> SomeList a

someList :: (KnownNat n) => List n a -> SomeList a
someList = SomeList SNat

withSomeList :: (forall n. (KnownNat n) => List n a -> r) -> SomeList a -> r
withSomeList f (SomeList n as) = withKnownNat n (f as)

withSomeListN :: (forall n. (KnownNat n) => SNat n -> List n a -> r) -> SomeList a -> r
withSomeListN f (SomeList n as) = withKnownNat n (f n as)

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

  mconcat = sconcat'

instance IsList (SomeList a) where
  type Item (SomeList a) = a

  fromList = P.foldr scons nilList

  toList = unfoldr unscons

instance (NFData a) => NFData (SomeList a) where
  rnf = withSomeList rnf

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

append :: SomeList a -> SomeList a -> SomeList a
append (SomeList nl ll) (SomeList nr lr)
  = let n = nl %:+ nr
    in withKnownNat n (SomeList n (ll ++ lr))

head :: List (1+n) a -> a
head (a :| _) = a

head' :: (1 ::<= n) => List n a -> a
head' (a :| _) = a

last :: forall n a. (KnownNat n) => List (n+1) a -> a
last = go sing
  where
    go :: SNat n' -> List (n'+1) a -> a
    go n1 as = case as of
                 (a :| Nil) -> a
                 (_ :| as') -> go (sPred n1) as'

tail :: List (1+n) a -> List n a
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

uncons' :: (1 ::<= n) => List n a -> (a, List (n:-1) a)
uncons' (a :| as) = (a, as)

unsnoc :: forall n a. (1 ::<= n) => List n a -> (List (n:-1) a, a)
unsnoc = go
  where
    go :: forall n'. List (n'+1) a -> (List n' a, a)
    go as = case as of
              a :| Nil -> (Nil, a)
              a :| as' -> first (a:|) (go as')

scons :: a -> SomeList a -> SomeList a
scons a sl = case sl of
               SomeList n as -> let m = sSucc n
                                in withKnownNat n (withKnownNat m (SomeList m (a :| as)))

unscons :: SomeList a -> Maybe (a, SomeList a)
unscons (SomeList n as) = case as of
                            Nil      -> Nothing
                            a :| as' -> let m = sPred n
                                        in withKnownNat m (Just (a, SomeList m as'))

-- Not sure why anyone would want to use this...
null :: List n a -> Bool
null Nil = True
null _   = False

snull :: SomeList a -> Bool
snull (SomeList _ as) = null as

-- O(1) !!!
length :: forall n a. (KnownNat n) => List n a -> Integer
length _ = natVal (Proxy :: Proxy n)

lengthNat :: (KnownNat n) => List n a -> SNat n
lengthNat _ = SNat

slength :: SomeList a -> Integer
slength (SomeList n _) = natVal n

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
intersperse :: forall n a. a -> List (1+n) a -> List (1 + 2:*n) a
intersperse e (a0 :| as0) = a0 :| go as0
  where
    go :: List n' a -> List (2:*n') a
    go as = case as of
              Nil        -> Nil
              (a :| as') -> e :| a :| go as'

-- TODO: intercalate

transpose :: forall r c a. (KnownNat c) => List r (List c a) -> List c (List r a)
transpose = go sing
  where
    go :: SNat c' -> List r (List c' a) -> List c' (List r a)
    go c rs = case testEquality c zero of
                Just Refl -> Nil
                _         -> let (col, rs') = nextC c rs
                             in col :| go (sPred c) rs'

    nextC :: SNat (c'+1) -> List r (List (c'+1) a) -> (List r a, List r (List c' a))
    nextC c1 = unzipWith uncons' \\ isGTEOne c1

isGTEOne :: proxy (n+1) -> () C.:- (1 ::<= (n+1))
isGTEOne _ = unsafeCoerceConstraint

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

-- TODO: permutations

----------------------------
-- Reducing lists (folds) --
----------------------------

foldl :: forall n a b. (b -> a -> b) -> b -> List n a -> b
foldl f = go
  where
    go :: forall n'. b -> List n' a -> b
    go z as = case as of
                Nil        -> z
                (a :| as') -> let z' = f z a
                              in z' `seq` go z' as'

foldl1 :: (a -> a -> a) -> List (n+1) a -> a
foldl1 f (a :| as) = foldl f a as

foldr :: forall n a b. (a -> b -> b) -> b -> List n a -> b
foldr f z = go
  where
    go :: List n' a -> b
    go as = case as of
              Nil        -> z
              (a :| as') -> f a (go as')

foldr1 :: (a -> a -> a) -> List (n+1) a -> a
foldr1 f (a :| as) = foldr f a as

-------------------
-- Special folds --
-------------------

concat :: forall n m a. List n (List m a) -> List (n:*m) a
concat = go
  where
    go :: List n' (List m a) -> List (n':*m) a
    go mas = case mas of
               Nil          -> Nil
               (ma :| mas') -> ma ++ go mas'

sconcat :: SomeList (SomeList a) -> SomeList a
sconcat = withSomeList concatS

concatS :: List n (SomeList a) -> SomeList a
concatS = go
  where
   go :: List n' (SomeList a) -> SomeList a
   go as = case as of
             Nil      -> nilList
             a :| as' -> append a (go as')

sconcat' :: [SomeList a] -> SomeList a
sconcat' = P.foldr append nilList

-- TODO: optimise
concatMap :: forall n m a b. (a -> List m b) -> List n a -> List (n:*m) b
concatMap f = concat . fmap f

and :: List n Bool -> Bool
and = foldr (&&) True

or :: List n Bool -> Bool
or = foldr (||) False

-- TODO: any

-- TODO: all

-- TODO: sum

-- TODO: product

maximum :: (Ord a) => List (n+1) a -> a
maximum = foldl1 max

-- TODO: minimum

--------------------
-- Building lists --
--------------------

-- TODO: Scans

-- TODO: Accumulating maps

--------------------
-- Infinite lists --
--------------------

iterate :: forall n a. (KnownNat n) => (a -> a) -> a -> List n a
iterate f = go sing
  where
    go :: SNat n' -> a -> List n' a
    go n a = case testEquality n zero of
               Just Refl -> Nil
               _         -> a :| go (sPred n) (f a)

-- Cannot implement repeat

replicate :: forall n a. (KnownNat n) => a -> List n a
replicate a = go sing
  where
    go :: SNat n' -> List n' a
    go n = case testEquality n zero of
             Just Refl -> Nil
             _         -> a :| go (sPred n)

-- Cannot implement cycle

-- TODO: unfoldr; how to implement? SomeList -> as with lists; specified length -> max length, but what if shorter? Either?

--------------
-- Sublists --
--------------

-------------------------
-- Extracting sublists --
-------------------------

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

-- TODO: how to specify that returned length is <= ?

takeWhile :: forall n a. (a -> Bool) -> List n a -> SomeList a
takeWhile p = go
  where
    go :: List n' a -> SomeList a
    go as = case as of
              Nil           -> nilList
              (a :| as')
                | p a       -> go as'
                | otherwise -> nilList

dropWhile :: forall n a. (KnownNat n) => (a -> Bool) -> List n a -> SomeList a
dropWhile p = go sing
  where
    go :: (KnownNat n') => SNat n' -> List n' a -> SomeList a
    go n as = case as of
                Nil           -> nilList
                (a :| as')
                  | p a       -> let n' = sPred n
                                 in withKnownNat n' (go n' as')
                  | otherwise -> someList as

-- TODO: dropWhileEnd

span :: forall n a. (KnownNat n) => (a -> Bool) -> List n a -> (SomeList a, SomeList a)
span p = go sing
  where
    go :: (KnownNat n') => SNat n' -> List n' a -> (SomeList a, SomeList a)
    go n as = case as of
                Nil           -> (nilList, nilList)
                a :| as'
                  | p a       -> let n' = sPred n
                                 in withKnownNat n' (first (scons a) (go n' as'))
                  | otherwise -> (nilList, someList as)

break :: (KnownNat n) => (a -> Bool) -> List n a -> (SomeList a, SomeList a)
break f = span (not . f)

-- TODO: stripPrefix

-- TODO: return type not that great
group :: (KnownNat n, Eq a) => List n a -> SomeList (a, SomeList a)
group = groupBy (==)

groupBy :: forall n a. (KnownNat n) => (a -> a -> Bool) -> List n a -> SomeList (a, SomeList a)
groupBy f = go . someList
  where
    go :: SomeList a -> SomeList (a, SomeList a)
    go (SomeList n as) = case as of
                           Nil      -> nilList
                           a :| as' -> withKnownNat (sPred n)
                                                    (uncurry scons
                                                     . bimap ((,) a) go
                                                     $ span (f a) as')

inits :: forall n a. List n a -> List (n+1) (SomeList a)
inits = go
  where
    go :: List n' a -> List (n'+1) (SomeList a)
    go as = nilList :| case as of
                         Nil      -> Nil
                         a :| as' -> fmap (scons a) (go as')

tails :: forall n a. (KnownNat n) => List n a -> List (n + 1) (SomeList a)
tails = go sing
  where
    go :: (KnownNat n') => SNat n' -> List n' a -> List (n' + 1) (SomeList a)
    go n as = SomeList n as :| case as of
                                 Nil      -> Nil
                                 _ :| as' -> let n' = sPred n
                                             in withKnownNat n' (go n' as')
-- TODO: Predicates

---------------------
-- Searching lists --
---------------------

---------------------------
-- Searching by equality --
---------------------------

-- TODO: elem, notElem

lookup :: forall n k a. (Eq k) => k -> List n (k,a) -> Maybe a
lookup k0 = go
  where
    go :: List n' (k,a) -> Maybe a
    go kas = case kas of
               Nil -> Nothing
               (k,a) :| kas'
                 | k0 == k   -> Just a
                 | otherwise -> go kas'

--------------------------------
-- Searching with a predicate --
--------------------------------

-- TODO: find

filter :: forall n a. (a -> Bool) -> List n a -> SomeList a
filter p = go
  where
    go :: List n' a -> SomeList a
    go as = case as of
              Nil -> nilList
              a :| as'
                | p a       -> a `scons` go as'
                | otherwise -> go as'

partition :: (a -> Bool) -> List n a -> (SomeList a, SomeList a)
partition p = foldr select (nilList, nilList)
  where
    select = liftA2 (bool first second) p scons

--------------------
-- Indexing lists --
--------------------

-- TODO: determine how to do these safely using the dependent length

---------------------------------
-- Zipping and unzipping lists --
---------------------------------

zip :: List n a -> List n b -> List n (a,b)
zip = zipWith (,)

zipWith :: forall n a b c. (a -> b -> c) -> List n a -> List n b -> List n c
zipWith f = go
  where
    go :: List n' a -> List n' b -> List n' c
    go as bs = case (as, bs) of
                 (Nil,       Nil)      -> Nil
                 ~(a :| as', b :| bs') -> f a b :| go as' bs'

unzip :: List n (a,b) -> (List n a, List n b)
unzip = unzipWith id

unzipWith :: forall n a b c. (c -> (a,b)) -> List n c -> (List n a, List n b)
unzipWith f = go
  where
    go :: List n' c -> (List n' a, List n' b)
    go lab = case lab of
               Nil         -> (Nil, Nil)
               (c :| lab') -> let (a,b) = f c
                              in bimap (a:|) (b:|) (go lab')

-- TODO: the rest of them

-------------------
-- Special lists --
-------------------

-- TODO: Functions on strings

sortBy :: forall n a. (KnownNat n) => (a -> a -> Ordering) -> List n a -> List n a
sortBy cmp = mergeAll . sequences n
  where
    sequences :: (KnownNat n') => SNat n' -> List n' a -> [SomeList a]
    sequences n' xs = case xs of
                        a :| b :| xs'
                          | a `cmp` b == GT -> withKnownNat n'' (descending n'' b (scons a nilList) xs')
                          | otherwise       -> withKnownNat n'' (ascending  n'' b (scons a)         xs')
                        _                   -> [someList xs]
      where
        n'' = sPred (sPred n')

    descending :: (KnownNat n') => SNat n' -> a -> SomeList a -> List n' a -> [SomeList a]
    descending n' a rs xs = case xs of
                              b :| ys
                                | a `cmp` b == GT -> let n'' = sPred n'
                                                     in withKnownNat n'' (descending n'' b (scons a rs) ys)
                              _                   -> scons a rs : sequences n' xs

    ascending :: (KnownNat n') => SNat n' -> a -> (SomeList a -> SomeList a) -> List n' a -> [SomeList a]
    ascending n' a toRs xs = case xs of
                               b :| ys
                                 | a `cmp` b /= GT -> let n'' = sPred n'
                                                      in withKnownNat n'' (ascending n'' b (toRs . scons a) ys)
                               _                   -> toRs (scons a nilList) : sequences n' xs

    merge :: List nl a -> List nr a -> List (nl + nr) a
    merge ls rs = case (ls, rs) of
                    (l :| ls', r :| rs')
                      | l `cmp` r == GT -> r :| merge ls  rs'
                      | otherwise       -> l :| merge ls' rs
                    (_, Nil)            -> ls
                    (Nil, _)            -> rs

    smerge :: SomeList a -> SomeList a -> SomeList a
    smerge (SomeList ln la) (SomeList rn ra) = let sz = ln %:+ rn
                                               in withKnownNat sz (SomeList sz (merge la ra))

    mergePairs :: [SomeList a] -> [SomeList a]
    mergePairs (a:b:xs) = smerge a b : mergePairs xs
    mergePairs xs       = xs

    mergeAll :: [SomeList a] -> List n a
    mergeAll [] = error "How did an empty list appear?"
    mergeAll [SomeList n' as'] = case testEquality n n' of
                                   Just Refl -> as'
                                   _         -> error ("sort: expected length of " P.++ show (natVal n)
                                                       P.++ " doesn't match actual length of " P.++ show (natVal n'))
    mergeAll xs  = mergeAll (mergePairs xs)

    n :: SNat n
    n = SNat

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
insertOrd :: forall n a k. (Ord k) => (a -> a -> a) -> k -> a
             -> List n (k,a) -> Either (List n (k,a)) (List (n+1) (k,a))
insertOrd mrg k0 v = go
  where
    go :: List n' (k,a) -> Either (List n' (k,a)) (List (n'+1) (k,a))
    go kas = case kas of
               Nil              -> Right ((k0,v) :| Nil)
               ka@(k,a) :| kas' -> case compare k0 k of
                                     LT -> Right ((k0,v) :| kas)
                                     EQ -> Left ((k,mrg v a) :| kas')
                                     GT -> ka `eCons` go kas'

    eCons :: b -> Either (List (n':-1) b) (List n' b) -> Either (List n' b) (List (n'+1) b)
    eCons b = bimap (b:|) (b:|)

-- | Insert first list into second (assumed sorted).
insertOrdAll :: forall n m k a. (Ord k, KnownNat m) => (a -> a -> a)
                -> List n (k,a) -> List m (k,a) -> SomeList (k,a)
insertOrdAll mrg ins bs = foldr go (someList bs) ins
  where
    go :: (k,a) -> SomeList (k,a) -> SomeList (k,a)
    go (k,a) (SomeList n res) = let n1 = sSucc n
                                in withKnownNat n1 (either (SomeList n) (SomeList n1)
                                                           (insertOrd mrg k a res))

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

lookupOrdRange :: forall n a k. (Ord k, 1 ::<= n) => k -> List n (k,a) -> a
lookupOrdRange k0 lst = case lst of
                          (_,a) :| kas -> go a kas
  where
    go :: a -> List n' (k,a) -> a
    go a kas = case kas of
                 Nil            -> a
                 (k,a') :| kas' -> case compare k0 k of
                                     LT -> a
                                     EQ -> a'
                                     _  -> go a' kas'

-- | For a given key @k@ and indexed list, finds the first @a_i@ where
--   @k_i <= k < k_{i+1}@ (or @k_0@ if @k < k_0@).
-- ordRegion :: k ->

splitInto :: forall n d a. (HasQuotRem n d) => List n a -> (List (Rem n d) a, List (Quot n d) (List d a))
splitInto = second (go sing) . splitAt \\ validQuotRem (SNat :: SNat n) (SNat :: SNat d)
  where
    go :: SNat q' -> List (q' :* d) a -> List q' (List d a)
    go q as = case testEquality q zero of
                Just Refl -> Nil
                _         -> uncurry (\l1 as' -> l1 :| go (sPred q) as') (splitAt as)

--------------------------------------------------------------------------------

zero :: SNat 0
zero = SNat
