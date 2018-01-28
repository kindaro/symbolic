{-# LANGUAGE
    OverloadedStrings
  , NoImplicitPrelude
  , TypeSynonymInstances
  , FlexibleInstances
  #-}

module Symbolic where

import Control.Monad.Writer.Strict
import Data.List (foldl', foldl1', break)
import Data.Maybe (isJust)
import Data.String (IsString(..))
import Data.Text (Text, unwords, pack)
import Prelude hiding (unwords)

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

data Property = Associative | Commutative | Idempotent

data PairwiseProperty = Distributive | PairwiseIdempotent | Dual

-- | Associative binary operations.
associative :: [Op]
associative = [Sigma, Pi]

-- | Commutative binary operations.
commutative :: [Op]
commutative = [Sigma, Pi]

data Un = Inv | Abs deriving (Show, Eq)

-- | Idempotent unary operations.
idempotent :: [Un]
idempotent = [Abs]

-- | Pairwise idempotent unary operations.
pairwiseIdempotent :: [(Un, Un)]
pairwiseIdempotent = [(Abs, Inv)]

-- | Dual unary operations, given as pairs.
dual :: [(Un, Un)]
dual = [(Inv, Inv)]

data PolymorphicExpr l v a
    = Polyary Op [a]
    | Unary Un a
    | Var l
    | Const v
    deriving Eq

type Label = String

type Value = Integer

type Expr = PolymorphicExpr Label Value

type ExprF = Expr (Fix Expr)

maybeOperator :: Expr a -> Maybe Op
maybeOperator (Polyary op _) = Just op
maybeOperator  _          = Nothing

maybeSubexprs :: ExprF -> Maybe [ExprF]
maybeSubexprs (Polyary _ xs) = Just . map unFix $ xs
maybeSubexprs (Unary   _ x ) = Just [unFix x]
maybeSubexprs  _             = Nothing

subexprs :: ExprF -> [ExprF]
subexprs (Polyary _ xs) = map unFix xs
subexprs (Unary   _ x ) = [unFix x]
subexprs  _             = [ ]

instance Show a => Show (Expr a) where
    show (Polyary op xs) = show op ++ " " ++ show xs
    show (Unary un xs) = show un ++ " " ++ show xs
    show (Var x) = show x
    show (Const x) = show x

sigma :: [a (Fix a)] -> Expr (Fix a)
sigma = Polyary Sigma . fmap Fx

pi :: [a (Fix a)] -> Expr (Fix a)
pi = Polyary Pi . fmap Fx

pow :: [a (Fix a)] -> Expr (Fix a)
pow = Polyary Pow . fmap Fx

inv :: a (Fix a) -> Expr (Fix a)
inv = Unary Inv . Fx

absolute :: a (Fix a) -> Expr (Fix a)
absolute = Unary Abs . Fx

instance Functor Expr where
    fmap f (Polyary op xs) = Polyary op (fmap f xs)
    fmap f (Unary un x) = Unary un (f x)
    fmap _ (Var      x) = Var x
    fmap _ (Const    x) = Const x

instance Foldable Expr where
    foldMap f (Polyary _ xs) = mconcat . fmap f $ xs
    foldMap f (Unary   _ x ) = f x
    foldMap _ (Const     i ) = mempty
    foldMap _ (Var       s ) = mempty

instance Traversable Expr where
    traverse f (Polyary op xs) = fmap (Polyary op) . traverse f $ xs
    traverse f (Unary   op x ) = fmap (Unary   op) .          f $ x
    traverse _ (Var         x) = pure $ Var x
    traverse _ (Const       x) = pure $ Const x

eval :: Algebra Expr Value
eval (Polyary Sigma xs) = foldl1' (+) xs
eval (Polyary Pi xs) = foldl1' (*) xs
eval (Polyary Pow xs) = foldr1 (^) xs
eval (Unary Inv x) = -x
eval (Unary Abs x) = abs x
eval (Const x) = x
eval (Var _) = error $ "TODO: define variable lookup."

-- |
-- λ depth euler27
-- 3
depth :: ExprF -> Int
depth = cata depth'
  where
    depth' :: Expr Int -> Int  -- TODO: Int? Integer? Integral?
    depth' ( Const _    ) = 1
    depth' ( Var   _    ) = 1
    depth' ( Unary _ x  ) = 1 + x
    depth' ( Polyary  _ xs ) = 1 + maximum ( 0: xs )

-- |
-- λ size euler27
-- 5
size :: ExprF -> Int
size = cata size'
  where
    size' :: Expr Int -> Int
    size' ( Const _    ) = 1
    size' ( Var   _    ) = 1
    size' ( Unary _ x  ) = x
    size' ( Polyary  _ xs ) = sum xs

-- |
-- λ sizeOfToplevel euler27
-- 3
sizeOfToplevel :: Expr a -> Int
sizeOfToplevel (Polyary _ xs) = length xs
sizeOfToplevel _ = 1

-- |
-- λ vars euler27
-- [("b",1),("x",2),("a",1)]
vars :: ExprF -> [(Label, Int)]
vars = map (\xs -> (head xs, length xs)) . equivalenceClasses . cata vars'
  where
    vars' :: Expr [Label] -> [Label]
    vars'  ( Const _    ) = [ ]
    vars'  ( Var   v    ) = [v]
    vars'  ( Unary _ x  ) = x
    vars'  ( Polyary  _ xs ) = concat xs

equivalenceClasses :: Eq a => [a] -> [[a]]
equivalenceClasses = equivalenceClassesBy (==)

equivalenceClassesBy :: (a -> a -> Bool) -> [a] -> [[a]]
equivalenceClassesBy _  [ ] = [ ]
equivalenceClassesBy eq (x:xs) = classify eq x (equivalenceClassesBy eq xs)
  where
    classify :: (a -> a -> Bool) -> a -> [[a]] -> [[a]]
    classify ep x (xs:xss) | head xs `ep` x = (x:xs) : xss
                           | otherwise    =    xs  : classify ep x xss
    classify _  x [] = [[x]]

-- |
-- λ zebra "lalafa"
-- (["l","l"],["a","afa"])
zebra :: Eq a => [a] -> ([[a]], [[a]])
zebra [ ]    = ([ ], [ ])
zebra all@(x:_) = zebraBy (== x) all

zebraBy :: (a -> Bool) -> [a] -> ([[a]], [[a]])
zebraBy pred = unzip . separate . (divide pred)
  where
    divide :: (a -> Bool) -> [a] -> [[a]]
    divide _    [ ] = [ ]
    divide pred xs  = let
                          (good, other) = break (not . pred) xs
                          (evil, bystander) = break pred other
                      in good : evil : divide pred bystander

    separate :: [[a]] -> [([a], [a])]
    separate [  ] = [ ]
    separate [xs] = [(xs, [])]
    separate (xs:xs':xss) = (xs, xs'): separate xss

instance Num ExprF where
    f + g = Polyary Sigma [Fx f, Fx g]
    f * g = Polyary Pi    [Fx f, Fx g]
    abs f = Unary Abs (Fx f)
    signum = undefined  -- I'm not sure. Either detect outermost Inv or just ignore.
    negate = Unary Inv . Fx
    fromInteger = Const

-- |
-- λ :t fmap unFix $ [Fx (1 :: ExprF)]
-- fmap unFix $ [Fx (1 :: ExprF)]
--   :: [PolymorphicExpr
--         Label Value (Fix (PolymorphicExpr Label Value))]

instance IsString ExprF where
    fromString = Var

-- |
-- λ :t fmap unFix $ [Fx ("x" :: ExprF)]
-- fmap unFix $ [Fx ("x" :: ExprF)]
--   :: [PolymorphicExpr
--         Label Value (Fix (PolymorphicExpr Label Value))]

-- | An old-school Expr definition.
euler27 :: ExprF
euler27 = Polyary Sigma
        [ Fx $ Polyary Pow [Fx $ Var "x", Fx $ Const 2]
        , Fx $ Polyary Pi [Fx $ Var "a", Fx $ Var "x"]
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
-- λ :{
--      let euler1 = subsTable [("b", 41), ("a", 1)] euler27
--          f i = cata eval . subst "x" (Const i) $ euler1
--      in take 10 $ f <$> [1..]
-- :}
-- [43,47,53,61,71,83,97,113,131,151]

-- | Solve f for x.
-- solve f x =

-- | Simplify an expression as best we can.
-- simpl :: Expr -> Expr

data Comment = Comment !ExprF !ExprF !Text deriving (Show, Eq)

-- | A transformation may modify an expression and say something.
type Transformation = ExprF -> Maybe (Writer [Comment] ExprF)

type SubTransformation = ExprF -> Writer [Comment] ExprF

tellWithDiff :: ExprF -> ExprF -> Text -> Writer [Comment] ExprF
tellWithDiff e e' x = tell [(Comment e e' x)] >> return e'

-- | Drop side effects of a transformation.
dropEffects :: Transformation -> ExprF -> ExprF
dropEffects t = fst . runWriter . dropMaybe t

-- | Drop the Maybe layer of a transformation, but keep the Writer.
dropMaybe :: Transformation -> ExprF -> Writer [Comment] ExprF
dropMaybe t e = maybe (return e) id (t e)

-- | TODO: Write some comment.
isApplicable :: Transformation -> ExprF -> Bool
isApplicable t e = isJust (t e)

-- | TODO: Write some comment.
makesDifference :: Transformation -> ExprF -> Bool
makesDifference t e = e' == e
  where e' = dropEffects t e

-- | If a sub-transformation makes difference, make it a transformation.
wrapInMaybe :: SubTransformation -> Transformation
wrapInMaybe f e | let result = f e
                , (e', _) <- runWriter result
                , e' /= e
                    = Just result
                | otherwise = Nothing


-- | Repeat a Transformation until it fails. Keep the last resulting expression.
adNauseam = undefined

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

-- |
-- λ cata (transform fuseAssociative) $ (2 * (3 * 5) * (1 + (2 + 3)))
-- Pi [Sigma [1,2,3],2,3,5]
fuseAssociative :: Transformation
fuseAssociative = wrapInMaybe fuseAssociative'

fuseAssociative' :: SubTransformation
fuseAssociative' e@(Polyary op fxs)
    | op `elem` associative =
        let
            candidateFilter :: Expr a -> Bool
            candidateFilter (Polyary op' _) = op == op'
            candidateFilter  _              = False

            fusionCandidates, notFusionCandidates :: [[ExprF]]
            (fusionCandidates, notFusionCandidates) =
                zebraBy candidateFilter xs

            e' = Polyary op . map Fx . concat $
                    (concat notFusionCandidates: map subexprs (concat fusionCandidates))

            -- TODO: That the order of expressions changes is an unfortunate point.
            --       This transformation would better be done in place, with split & intercalate.

            message = unwords ["Fusion of", pack . show $ op, "due to associativity."]

        in tellWithDiff e e' message
  where
    xs = map unFix fxs
fuseAssociative' e = return e

fuseUnary :: Transformation
fuseUnary e@(Unary un (Fx e'@(Unary un' (Fx e''))))
    | (un, un') `elem` dual =
        let message = unwords [ "Fusion of", pack . show $ un, "due to duality with"
                              , pack . show $ un', "." ]
        in Just $ tellWithDiff e e'' message
    | un == un' && un `elem` idempotent =
        let message = unwords [ "Fusion of", pack . show $ un, "due to idempotence." ]
        in Just $ tellWithDiff e e' message
    | otherwise = Nothing
fuseUnary _ = Nothing

-- |
-- λ cata (transform fuseUnary) $ abs (abs (- (- (-2 ))))
-- Abs Inv 2

-- TODO: Should also remove Inv from directly under Abs: Abs . Inv = Abs.

fuseConstants :: Transformation
fuseConstants = undefined

expand :: Transformation
expand = undefined

contract :: Transformation
contract = undefined

-- | Group together elements that belong to equivalence classes by power of some variable.
--   Should create a proper polynomial from a soup of summands.
--
--   Should this do expansion? No. Only grouping together of elements of similar power.
collect :: Value -> Transformation
collect = undefined

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
