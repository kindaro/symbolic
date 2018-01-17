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

class Functor a => Algebra a b where
    cata :: (a b -> b) -> a (Fix a) -> b
    cata f = cata' . Fx
      where
        cata' = f . fmap cata' . unFix
