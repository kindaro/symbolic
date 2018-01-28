{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , FunctionalDependencies
  #-}

module Algebra where

newtype Fix a = Fx { unFix :: (a (Fix a)) }

-- TODO: Is this useful?
mapFix :: (a (Fix a) -> b (Fix b)) -> Fix a -> Fix b
mapFix f = Fx . f . unFix

mapFix2 :: Functor f => (f (a (Fix a)) -> f (b (Fix b))) -> f (Fix a) -> f (Fix b)
mapFix2 f = fmap Fx . f . fmap unFix

instance Show (a (Fix a)) => Show (Fix a) where
    show (Fx e) = show e

instance Eq (a (Fix a)) => Eq (Fix a) where
    (Fx x) == (Fx y) = x == y

type Algebra a b = a b -> b

cata :: Functor a => Algebra a b -> a (Fix a) -> b
cata f = cata' f . Fx

cata' :: Functor a => Algebra a b -> Fix a -> b
cata' f = f . fmap (cata' f) . unFix
