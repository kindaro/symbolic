{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , FunctionalDependencies
  #-}

module Symbolic where

import Control.Monad ((<=<))
import Data.List
import Data.String

import Algebra

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
-- affects its superexpression. Unknown expressions will be either restricted
-- or accounted for. Example: I can't have negative exponents, so there
-- should be a restriction put in place.

data Op = Sigma | Pi | Pow deriving (Show, Eq)

data Un = Inv | Abs deriving (Show, Eq)

data PolymorphicExpr a = Expr Op [a]
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

isAssociative, isIdempotent, isDual :: Expr a -> Bool

-- | Can I remove parentheses from consecutive occurences of these expressions?
isAssociative (Expr op _) | op `elem` [Sigma, Pi] = True  -- TODO: Is this all? What about Exp?
                          | otherwise = False
isAssociative _ = False

-- | Would two successive operations have the same effect as one?
isIdempotent (Unary Abs _) = True
isIdempotent _ = False

-- | Would two successive operations cancel each other out?
isDual (Unary Inv _) = True
isDual _ = False

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
eval (Var v) = error $ "TODO: define variable lookup."

type ExprF = Expr (Fix Expr)

instance Num ExprF where
    f + g = Expr Sigma [Fx f, Fx g]
    f * g = Expr Pi    [Fx f, Fx g]
    abs f = Unary Abs (Fx f)
    signum = undefined  -- I'm not sure. Either detect outermost Inv or just ignore.
    negate = Unary Inv . Fx
    fromInteger = Const

-- \ :t fmap unFix $ [Fx (1 :: ExprF)]
-- fmap unFix $ [Fx (1 :: ExprF)] :: [Expr (Fix Expr)]

instance IsString ExprF where
    fromString = Var

-- \ :t fmap unFix $ [Fx ("x" :: ExprF)]
-- fmap unFix $ [Fx ("x" :: ExprF)] :: [Expr (Fix Expr)]

-- | An old-school Expr definition.
euler27 = Expr Sigma
        [ Fx $ Expr Pow [Fx $ Var "x", Fx $ Const 2]
        , Fx $ Expr Pi [Fx $ Var "a", Fx $ Var "x"]
        , Fx $ Var "b"
        ]

-- | A definition of Expr using Num & IsString instances.
euler27' = sigma [pow ["x", 2], "a" * "x", "b"]

-- \ euler27 == euler27'
-- True
-- \ euler27 == Const 1
-- False

-- \ cata eval $ pow [sigma [1,2,3],4]
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

-- \ let euler1 = subsTable [("b", 41), ("a", 1)] euler27
-- \ let f i = cata eval . subst "x" (Const i) $ euler1
-- \ takeWhile isPrime $ f <$> [1..]
-- [43,47,53,61,71,83,97,113,131,151,173,197,223,251,281,313,347,383,421,461,
-- 503,547,593,641,691,743,797,853,911,971,1033,1097,1163,1231,1301,1373,1447,
-- 1523,1601]

-- | Solve f for x.
-- solve f x =

-- | Simplify an expression as best we can.
-- simpl :: Expr -> Expr

-- | Transform may modify an expression and maybe also say something.
type Transform = ExprF -> ExprF

transform :: Transform -> Algebra Expr (Fix Expr)
transform t = Fx . t

replace :: ExprF -> ExprF -> Transform
replace x y e | e == x = Just y
              | otherwise = Nothing

-- | Fusion glues together associative operations (i.e. removing parentheses),
--   removes superfluous repetitive adjoined unary operations, and evaluates
--   constant expressions.
fusion :: Transform
fusion = fixp (fuseConstants <=< fuseAssociative <=< fuseUnary) . return
  where
    fuseAssociative e@(Expr op xs) | isAssociative e && or (fmap (isAssociative . unFix) xs) = undefined
                      | otherwise = Nothing

    fuseUnary = undefined

    fuseConstants = undefined

expand :: Transform
expand = undefined

contract :: Transform
contract = undefined

group :: Transform
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
