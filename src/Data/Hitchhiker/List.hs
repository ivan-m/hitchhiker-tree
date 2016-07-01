{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}


{-# LANGUAGE DataKinds, DeriveFunctor, FlexibleInstances, GADTs, KindSignatures,
             StandaloneDeriving, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

--

{-# LANGUAGE ScopedTypeVariables #-}

{- |
   Module      : Data.Hitchhiker.List
   Description : Dependently-typed lists
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Hitchhiker.List where

import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Prelude.Enum
import Data.Singletons.Prelude.Ord
import Data.Singletons.TypeLits
import Data.Type.Equality
import GHC.Exts                     (IsList (..))
import GHC.TypeLits

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

someList :: (KnownNat (n -1)) => List (n - 1) a -> SomeList a
someList l = SomeList SNat l

data SomeList :: * -> * where
  SomeList :: forall n a. (KnownNat n) => SNat n -> List n a -> SomeList a

instance (Eq a) => Eq (SomeList a) where
  (SomeList nl ll) == (SomeList nr lr)
    = case testEquality nl nr of
        Just Refl -> withKnownNat nl (withKnownNat nr (ll `checkEq` lr))
        Nothing   -> False
    where
      checkEq :: List n a -> List n a -> Bool
      checkEq = (==)

-- | Compares on lengths before comparing on values.
instance (Ord a) => Ord (SomeList a) where
  compare (SomeList nl ll) (SomeList nr lr) =
    case (fromSing (sCompare nl nr), testEquality nl nr) of
      -- Malformed instances may end up having this return (EQ, Nothing)...
      (EQ, Just Refl) -> (checkComp ll lr)
      (ne,_)          -> ne
    where
      checkComp :: List n a -> List n a -> Ordering
      checkComp = compare

instance (Show a) => Show (SomeList a) where
  showsPrec d (SomeList _ l) = showsPrec d l

instance (Read a) => Read (SomeList a) where
  readPrec = (do Ident "Nil" <- lexP
                 return (SomeList SNat Nil))
             <++
             (do a <- readPrec
                 Symbol ":|" <- lexP
                 as <- readPrec
                 case as of
                   SomeList n as' -> return (prepend n a as'))
    where
      prepend :: (KnownNat (l + 1)) => SNat (l) -> a -> List (l) a -> SomeList a
      prepend l a as = SomeList (sSucc l) (a :| as)

-- simplify :: (KnownNat l) => SNat ((l + 1) - 1) :~: SNat l
-- simplify = Refl

-- blah :: (KnownNat l) => SNat ((l - 1) + 1) :~: SNat ((l + 1) - 1)
-- blah = Refl

cons :: SNat l -> a -> List (l) a -> List (l + 1) a
cons n a as = (a :| (withKnownNat (sPred (sSucc n)) as))

scons :: forall a. a -> SomeList a -> SomeList a
scons a (SomeList (SNat :: SNat n) as) = SomeList SNat ((a :| as) :: List (n + 1) a)
