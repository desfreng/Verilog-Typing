{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeFamilies #-}

module Frontend.Reversed where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Foldable1
import Data.Monoid
import Data.Semigroup
import Data.String
import Prelude (Eq, Ord, Show (..), ($), (.))

data Reversed a = Start a | (Reversed a) :> a deriving (Eq, Ord, Functor)

{-# INLINE singleton #-}
singleton :: a -> Reversed a
singleton x = Start x

{-# INLINE map #-}
map :: (a -> b) -> Reversed a -> Reversed b
map f (Start x) = Start $ f x
map f (l :> x) = fmap f l :> f x

instance Semigroup (Reversed a) where
  {-# INLINE (<>) #-}
  (<>) :: Reversed a -> Reversed a -> Reversed a
  (l' :> x) <> l = (l' <> l) :> x
  (Start x) <> l = l :> x

instance Foldable Reversed where
  foldMap :: (Monoid m) => (a -> m) -> Reversed a -> m
  foldMap f (Start x) = f x
  foldMap f (l :> x) = foldMap f l <> f x

instance Foldable1 Reversed where
  foldMap1 :: (Semigroup m) => (a -> m) -> Reversed a -> m
  foldMap1 f (Start x) = f x
  foldMap1 f (l :> x) = foldMap1 f l <> f x

instance Applicative Reversed where
  {-# INLINE pure #-}
  pure :: a -> Reversed a
  pure = singleton

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Reversed a -> Reversed b -> Reversed c
  liftA2 f xs ys = foldMap1 (\a -> foldMap1 (singleton . f a) ys) xs

instance Monad Reversed where
  {-# INLINE (>>=) #-}
  (>>=) :: Reversed a -> (a -> Reversed b) -> Reversed b
  xs >>= f = foldMap1 f xs

instance (Show a) => Show (Reversed a) where
  show :: Reversed a -> String
  show l = "Reversed " <> show (toList l)
