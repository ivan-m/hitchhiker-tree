{-# LANGUAGE DataKinds, GADTs, KindSignatures, TypeOperators #-}

{- |
   Module      : Data.Hitchhiker
   Description : The \"Data.Hitchhiker\" module
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Data.Hitchhiker where

import Data.Proxy
import GHC.TypeLits

import Data.Reflection

--------------------------------------------------------------------------------

data Statement k a = Assert k a
                   | Retract k
  deriving (Eq, Ord, Show, Read)

type Log k a = [Statement k a]

data BTree k a = BRoot

data HNode

data DTList :: Nat -> * -> * where
    Nil :: DTList 0 a
    Cons :: a -> DTList n a -> DTList (n+1) a

-- zip' :: DTList n a -> DTList n b -> DTList n (a,b)
-- zip' Nil Nil = Nil
-- zip' (Cons x xs) (Cons y ys) = Cons (x,y) $ zip' xs ys
