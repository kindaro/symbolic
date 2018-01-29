{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , FunctionalDependencies
  #-}

module Algebra where

import Fix

type Algebra a b = a b -> b

cata :: Functor a => Algebra a b -> a (Fix a) -> b
cata f = cata' f . Fx

cata' :: Functor a => Algebra a b -> Fix a -> b
cata' f = f . fmap (cata' f) . unFix
