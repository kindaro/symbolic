{-# LANGUAGE
    OverloadedStrings
  , TypeSynonymInstances
  , FlexibleInstances
  , UndecidableInstances
  , FunctionalDependencies
  #-}

module Symbolic where

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
-- [ ] Make subst.
-- [ ] Make solve.
-- [ ] Make sign computable.
--
-- How do I make sign computable? For every expression, I may know the way it
-- affects its superexpression. Unknown expressions will be either restricted
-- or accounted for. Example: I can't have negative exponents, so there
-- should be a restriction put in place.

data Op = Sigma | Pi | Pow | Equal deriving (Show, Eq)

data Un = Inv | Abs deriving (Show, Eq)

data Expr a = Expr Op [a]
            | Unary Un a
            | Var String
            | Const Integer
            deriving (Show, Eq)

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

instance Functor Expr where
    fmap f (Expr op xs) = Expr op (fmap f xs)
    fmap f (Unary un x) = Unary un (f x)
    fmap _ (Var x) = Var x
    fmap _ (Const x) = Const x

instance Algebra Expr Integer where
    alg (Expr Sigma xs) = foldl1' (+) xs
    alg (Expr Pi xs) = foldl1' (*) xs
    alg (Expr Pow xs) = foldr1 (^) xs
    alg (Unary Inv x) = -x
    alg (Unary Abs x) = abs x
    alg (Const x) = x
    alg (Var v) = error $ "TODO: define variable lookup."

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

-- | Old-school Expr definition.
euler27 = Expr Sigma
        [ Fx $ Expr Pow [Fx $ Var "x", Fx $ Const 2]
        , Fx $ Expr Pi [Fx $ Var "a", Fx $ Var "x"]
        , Fx $ Var "b"
        ]

-- | A definition of Expr using Num & IsString instances.
euler27' = sigma [pow ["x", 2], "a" * "x", "b"]

-- | Simplify an expression as best we can.
-- simpl :: Expr -> Expr

-- | Substitute expression x with expression y, throughout expression f.
-- subst :: Expr -> Expr -> Expr -> Expr
-- subst f x y = 

-- | Solve f for x.
-- solve f x =
