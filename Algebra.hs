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

class Functor a => Algebra a b | a -> b where
    alg :: a b -> b
    cata :: a (Fix a) -> b
    cata = cata' . Fx
      where
        cata' = alg . fmap cata' . unFix
