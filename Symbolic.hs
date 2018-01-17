{-# LANGUAGE
    OverloadedStrings
  #-}

module Symbolic where

import Data.String

-- Plan:
-- 
-- [+] Write basic Expr.
-- [+] Make it Num. [Additionally made it IsString.]
-- [ ] Make it Algebra.
-- [ ] Make it Traversable.
-- [ ] Make simpl.
-- [ ] Make subst.
-- [ ] Make solve.

data Expr = Expr Op [Expr]
          | Unary Un Expr
          | Var String
          | Const Integer
          deriving (Show, Eq)

data Op = Sigma | Pi | Exp | Equal deriving (Show, Eq)

data Un = Inv | Abs deriving (Show, Eq)

instance Num Expr where
    f + g = Expr Sigma [f, g]
    f * g = Expr Pi    [f, g]
    abs f = Unary Abs f
    signum = undefined  -- I'm not sure. Either detect outermost Inv or just ignore.
    negate = Unary Inv
    fromInteger = Const

instance IsString Expr where
    fromString = Var

-- | Old-school Expr definition.
euler27 = Expr Sigma
        [ Expr Exp [Var "x", Const 2]
        , Expr Pi [Var "a", Var "x"]
        ,  Var "b"
        ]

-- | A definition of Expr using Num & IsString instances.
euler27' :: Expr
euler27' = Expr Exp ["x", 2] + ("a" * "x") + "b"

-- | Simplify an expression as best we can.
-- simpl :: Expr -> Expr

-- | Substitute expression x with expression y, throughout expression f.
-- subst :: Expr -> Expr -> Expr -> Expr
-- subst f x y = 

-- | Solve f for x.
