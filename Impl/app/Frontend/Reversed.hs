{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeFamilies #-}

module Frontend.Reversed where

import Control.Applicative
import Control.Monad
import Data.Foldable (Foldable (foldMap))
import Data.Foldable qualified as F
import Data.Monoid
import Data.Semigroup
import Data.String
import GHC.IsList
import Prelude (Eq, Ord, Show (..), (.))

data Reversed a = Empty | (Reversed a) :> a deriving (Eq, Ord, Foldable, Functor)

instance IsList (Reversed a) where
  type Item (Reversed a) = a

  {-# INLINE fromList #-}
  fromList :: [a] -> Reversed a
  fromList [] = Empty
  fromList (hd : tl) = fromList tl :> hd

  toList :: Reversed a -> [a]
  toList = F.toList

{-# INLINE singleton #-}
singleton :: a -> Reversed a
singleton x = Empty :> x

{-# INLINE map #-}
map :: (a -> b) -> Reversed a -> Reversed b
map _ Empty = Empty
map f (l :> x) = fmap f l :> f x

instance Semigroup (Reversed a) where
  {-# INLINE (<>) #-}
  (<>) :: Reversed a -> Reversed a -> Reversed a
  (l' :> x) <> l = (l' <> l) :> x
  Empty <> l = l

instance Monoid (Reversed a) where
  {-# INLINE mempty #-}
  mempty :: Reversed a
  mempty = Empty

instance Applicative Reversed where
  {-# INLINE pure #-}
  pure :: a -> Reversed a
  pure = singleton

  {-# INLINE liftA2 #-}
  liftA2 :: (a -> b -> c) -> Reversed a -> Reversed b -> Reversed c
  liftA2 f xs ys = foldMap (\a -> foldMap (singleton . f a) ys) xs

instance Monad Reversed where
  {-# INLINE (>>=) #-}
  (>>=) :: Reversed a -> (a -> Reversed b) -> Reversed b
  xs >>= f = foldMap f xs

instance Alternative Reversed where
  {-# INLINE empty #-}
  empty :: Reversed a
  empty = Empty

  {-# INLINE (<|>) #-}
  (<|>) :: Reversed a -> Reversed a -> Reversed a
  (<|>) = (<>)

instance MonadPlus Reversed

instance (Show a) => Show (Reversed a) where
  show :: Reversed a -> String
  show l = "Reversed " <> show (toList l)
