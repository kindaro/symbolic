{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  #-}

module Symbolic where

import Control.Monad.Trans.Maybe
import Control.Monad.Writer.Strict
import Data.List
import Data.String
import Data.Text (Text)

import Algebra

-- $setup
-- λ :set -XOverloadedStrings

-- Plan:
-- 
-- [+] Write basic Expr.
-- [+] Make it Num. [Additionally made it IsString.]
-- [+] Make it Algebra.
-- [ ] Make it Traversable.
-- [ ] Make simpl.
-- [+] Make subst.
-- [ ] Make solve.
-- [ ] Make sign computable.
--
-- How do I make sign computable? For every expression, I may know the way it
-- affects its superexpression. Unknown expressions will be either isolated
-- or accounted for. Example: I can't have negative exponents, so there
-- should be a restriction put in place.

data Op = Sigma | Pi | Pow deriving (Show, Eq)

data Un = Inv | Abs deriving (Show, Eq)

data PolymorphicExpr c a = Expr Op [a]
            | Unary Un a
            | Var String
            | Const Integer
            deriving Eq

type Expr = PolymorphicExpr Integer

instance Show a => Show (Expr a) where
    show (Expr op xs) = show op ++ " " ++ show xs
    show (Unary un xs) = show un ++ " " ++ show xs
    show (Var x) = show x
    show (Const x) = show x

sigma :: [a (Fix a)] -> Expr (Fix a)
sigma = Expr Sigma . fmap Fx

pi :: [a (Fix a)] -> Expr (Fix a)
pi = Expr Pi . fmap Fx

pow :: [a (Fix a)] -> Expr (Fix a)
pow = Expr Pow . fmap Fx

inv :: a (Fix a) -> Expr (Fix a)
inv = Unary Inv . Fx

absolute :: a (Fix a) -> Expr (Fix a) 
absolute = Unary Abs . Fx

-- | Associative binary operations.
associative :: [Op]
associative = [Sigma, Pi]

-- | Commutative binary operations.
commutative :: [Op]
commutative = [Sigma, Pi]

-- | Idempotent unary operations.
idempotent :: [Un]
idempotent = [Abs]

-- | Dual unary operations, given as pairs.
dual :: [(Un, Un)]
dual = [(Inv, Inv)]

instance Functor Expr where
    fmap f (Expr op xs) = Expr op (fmap f xs)
    fmap f (Unary un x) = Unary un (f x)
    fmap _ (Var x) = Var x
    fmap _ (Const x) = Const x

eval :: Algebra Expr Integer
eval (Expr Sigma xs) = foldl1' (+) xs
eval (Expr Pi xs) = foldl1' (*) xs
eval (Expr Pow xs) = foldr1 (^) xs
eval (Unary Inv x) = -x
eval (Unary Abs x) = abs x
eval (Const x) = x
eval (Var _) = error $ "TODO: define variable lookup."

type ExprF = Expr (Fix Expr)

instance Num ExprF where
    f + g = Expr Sigma [Fx f, Fx g]
    f * g = Expr Pi    [Fx f, Fx g]
    abs f = Unary Abs (Fx f)
    signum = undefined  -- I'm not sure. Either detect outermost Inv or just ignore.
    negate = Unary Inv . Fx
    fromInteger = Const

-- |
-- λ :t fmap unFix $ [Fx (1 :: ExprF)]
-- fmap unFix $ [Fx (1 :: ExprF)]
--   :: [PolymorphicExpr Integer (Fix (PolymorphicExpr Integer))]

instance IsString ExprF where
    fromString = Var

-- |
-- λ :t fmap unFix $ [Fx ("x" :: ExprF)]
-- fmap unFix $ [Fx ("x" :: ExprF)]
--   :: [PolymorphicExpr Integer (Fix (PolymorphicExpr Integer))]

-- | An old-school Expr definition.
euler27 :: ExprF
euler27 = Expr Sigma
        [ Fx $ Expr Pow [Fx $ Var "x", Fx $ Const 2]
        , Fx $ Expr Pi [Fx $ Var "a", Fx $ Var "x"]
        , Fx $ Var "b"
        ]

-- | A definition of Expr using Num & IsString instances.
euler27' :: ExprF
euler27' = sigma [pow ["x", 2], "a" * "x", "b"]

-- |
-- λ euler27 == euler27'
-- True
-- λ euler27 == Const 1
-- False

-- |
-- λ cata eval $ pow [sigma [1,2,3],4]
-- 1296

-- | Accept something that looks like an initial algebra, but actually
--   discriminates and mutates some of the nodes. Run that algebra through
--   a given object.
--
--   algMap Fx x == x
algMap :: Algebra Expr (Fix Expr) -> ExprF -> ExprF
algMap alg = unFix . cata alg

-- | Substitute expression x with expression y, throughout expression f.
subst :: ExprF -> ExprF -> ExprF -> ExprF
subst x y = algMap (transform (replace x y))

subsTable :: [(ExprF, ExprF)] -> ExprF -> ExprF
subsTable table e = foldl' (flip . uncurry $ subst) e table

-- |
-- λ let euler1 = subsTable [("b", 41), ("a", 1)] euler27
-- λ let f i = cata eval . subst "x" (Const i) $ euler1
-- λ take 10 $ f <$> [1..]
-- [43,47,53,61,71,83,97,113,131,151]

-- | Solve f for x.
-- solve f x =

-- | Simplify an expression as best we can.
-- simpl :: Expr -> Expr

data Comment = Comment !ExprF !ExprF !Text

-- | A transformation may modify an expression and say something.
type Transformation = ExprF -> Maybe (Writer [Comment] ExprF)

tellWithDiff :: ExprF -> ExprF -> Text -> Writer [Comment] ExprF
tellWithDiff e e' x = tell [(Comment e e' x)] >> return e'

-- | Drop side effects of a transformation.
dropEffects :: Transformation -> ExprF -> ExprF
dropEffects t = fst . runWriter . dropMaybe t

dropMaybe :: Transformation -> ExprF -> Writer [Comment] ExprF
dropMaybe t e = case t e of
    Nothing -> return e
    Just w  -> w

-- | Recursively apply a transform to an expression.
transform :: Transformation -> Algebra Expr (Fix Expr)
transform t = Fx . dropEffects t

-- | If the expression is extensionally equal to x, replace it with y.
replace :: ExprF -> ExprF -> Transformation
replace x y e | e == x    = Just    $ tellWithDiff x y "replace" >> return y
              | otherwise = Nothing

-- | Fusion glues together associative operations (i.e. removing parentheses),
--   removes superfluous repetitive adjoined unary operations, and evaluates
--   constant expressions.
fusion :: Transformation
fusion = undefined

fuseAssociative :: Transformation
fuseAssociative = undefined
-- fuseAssociative e@(Expr op xs)
--     | op `elem` associative = filter (undefined) undefined
--     | otherwise = Nothing

fuseUnary :: Transformation
fuseUnary = undefined

fuseConstants :: Transformation
fuseConstants = undefined

expand :: Transformation
expand = undefined

contract :: Transformation
contract = undefined

group :: Transformation
group = undefined

-- Example: > x^2 + ax + b          x^2 + ax + b
--          > subst x (y - 1)       (y - 1)^2 + a(y - 1) + b
--          > expand                y^2 - 2y + 1 + ay - a + b
--          > group y               y^2 + (a - 2)y + (b - a + 1)
--
--          > x^2 + ax + b
--          > subst x (y - a/2)     (y - a/2)^2 + a(y - a/2) + b
--          > expand                y^2 - ay + a^2/4 + ay - a^2/2 + b
--          > group y               y^2 - a^2/4 + b
--
--  Eventually I'd like to be able to figure out the substitution necessary to remove one of the
--  terms in the polynomial automagically. It's feasible to accomplish through writing the
--  expansion of each term one after another and making sure the terms of a chosen power sum to
--  zero. I'm not sure how this should be done programmatically.

-- TODO:
--
-- How do I write a Traversable? What do I gain if I already have Algebra?
--
-- Decide the type of Transform, and how I deal with it. Specifically, I would like to have it
-- leave a note aside when something was transformed, and return something else than an Expr if
-- nothing was.
