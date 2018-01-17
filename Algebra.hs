{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , FunctionalDependencies
  #-}

module Algebra where

newtype Fix a = Fx { unFix :: (a (Fix a)) }

instance Show (a (Fix a)) => Show (Fix a) where
    show (Fx e) = show e

instance Eq (a (Fix a)) => Eq (Fix a) where
    (Fx x) == (Fx y) = x == y

type Algebra a b = a b -> b

cata :: Functor a => Algebra a b -> a (Fix a) -> b
cata f = (cata' f) . Fx

cata' :: Functor a => Algebra a b -> Fix a -> b
cata' f x = f . fmap (cata' f) . unFix $ x
