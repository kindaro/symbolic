{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , FunctionalDependencies
  #-}

module Fix (converge, fixp, convergeBy, fixpBy, fixpM, Fix(..), mapFix, mapFix2) where

-- | Take elements from a list until met two equal adjacent elements. Of those,
--   take only the first one, then be done with it.
--
--   This function is intended to operate on infinite lists, but it will still
--   work on finite ones.
converge :: Eq a => [a] -> [a]
converge = convergeBy (==)

-- \ r a = \x -> (x + a / x) / 2
-- \ -- ^ A method of computing square roots due to Isaac Newton.
-- \ take 8 $ iterate (r 2) 1
-- [1.0,1.5,1.4166666666666665,1.4142156862745097,1.4142135623746899,
-- 1.414213562373095,1.414213562373095,1.414213562373095]
-- \ converge $ iterate (r 2) 1
-- [1.0,1.5,1.4166666666666665,1.4142156862745097,1.4142135623746899,1.414213562373095]

-- | Find a fixed point of a function. May present a non-terminating function
--   if applied carelessly!
fixp :: Eq a => (a -> a) -> a -> a
fixp f = last . converge . iterate f

-- \ fixp (r 2) 1
-- 1.414213562373095

-- | Non-overloaded counterpart to `converge`.
convergeBy :: (a -> a -> Bool) -> [a] -> [a]
convergeBy _ [ ] = [ ]
convergeBy _ [x] = [x]
convergeBy eq (x: xs @(y: _))
    | x `eq` y = [x]
    | otherwise = x : convergeBy eq xs

-- \ convergeBy (\x y -> abs (x - y) < 0.001) $ iterate (r 2) 1
-- [1.0,1.5,1.4166666666666665,1.4142156862745097]

-- | Non-overloaded counterpart to `fixp`.
fixpBy :: (a -> a -> Bool) -> (a -> a) -> a -> a
fixpBy eq f = last . convergeBy eq . iterate f

-- \ fixpBy (\x y -> abs (x - y) < 0.001) (r 2) 1
-- 1.4142156862745097

-- | Find a fixed point of a monadic function. May present a non-terminating
--   function if applied carelessly!
fixpM :: (Eq a, Monad m) => (a -> m a) -> a -> m a
fixpM f x = do
    y <- f x
    if x == y
        then return x
        else fixpM f y

-- \ fixpM (\x -> (".", x^2)) 0.5
-- ("............",0.0)

-- | A type constructor for fixing on the type level.
newtype Fix a = Fx { unFix :: (a (Fix a)) }

instance Show (a (Fix a)) => Show (Fix a) where
    show (Fx e) = show e

instance Eq (a (Fix a)) => Eq (Fix a) where
    (Fx x) == (Fx y) = x == y

-- | This is like an fmap, but for Fix.
mapFix :: (a (Fix a) -> b (Fix b)) -> Fix a -> Fix b
mapFix f = Fx . f . unFix

-- | This is like an fmap, but for a whole functor of Fixes.
mapFix2 :: Functor f => (f (a (Fix a)) -> f (b (Fix b))) -> f (Fix a) -> f (Fix b)
mapFix2 f = fmap Fx . f . fmap unFix
