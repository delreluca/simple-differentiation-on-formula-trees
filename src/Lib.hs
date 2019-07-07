module Lib
    where

import Data.Map (Map, (!))

data UnaryOp = Exp | Log deriving (Eq,Show)
data BinaryOp = Add | Mult | Pow deriving (Eq,Show)
data Value = Var Char | Const Double deriving (Eq,Show)

data Expr = Expr0 Value | Expr1 UnaryOp Expr | Expr2 BinaryOp Expr Expr deriving (Eq)--,Show) 

plus :: Expr -> Expr -> Expr
plus a b = Expr2 Add a b

times :: Expr -> Expr -> Expr
times a b = Expr2 Mult a b

toThe :: Expr -> Expr -> Expr
toThe a b = Expr2 Pow a b

e :: Expr -> Expr
e a = Expr1 Exp a

ln :: Expr -> Expr
ln a = Expr1 Log a

lit :: Double -> Expr
lit x = Expr0 $ Const x

var :: Char -> Expr
var u = Expr0 $ Var u

neg :: Expr -> Expr
neg a = lit (-1.0) `times` a

inv :: Expr -> Expr
inv a = a `toThe` lit (-1.0)

over :: Expr -> Expr -> Expr
over a b = a `times` inv b

minus :: Expr -> Expr -> Expr
minus a b = a `plus` neg b

symbol2 :: BinaryOp -> String
symbol2 Add = "+"
symbol2 Mult = "*"
symbol2 Pow = "^"

--Zur Erklärung von Typklassen
instance Num Expr where
    (+) = plus
    (-) = minus
    (*) = times
    negate = neg
    abs = id --dummy
    signum = id --dummy
    fromInteger = lit . fromInteger

--Pretty printing
instance Show Expr where
    show (Expr2 o a@(Expr0 _) b@(Expr0 _)) = show a ++ "" ++ symbol2 o ++ "" ++ show b
    show (Expr2 o a@(Expr0 _) b) = show a ++ " " ++ symbol2 o ++ " (" ++ show b ++ ")"
    show (Expr2 o a b@(Expr0 _)) = "(" ++ show a ++ ") " ++ symbol2 o ++ " " ++ show b
    show (Expr2 o a b) = "(" ++ show a ++ ")" ++ symbol2 o ++ "(" ++ show b ++ ")"
    show (Expr1 o a) = symbol o ++ "(" ++ show a ++ ")"
        where symbol Exp = "exp"
              symbol Log = "ln"
    show (Expr0 (Var u)) = [u]
    show (Expr0 (Const x)) = show x

evalExpr :: Map Char Double -> Expr -> Double
evalExpr _ (Expr0 (Const x)) = x
evalExpr m (Expr0 (Var u)) = m ! u
evalExpr m (Expr1 o a) = operation o $ evalExpr m a
    where operation Exp = exp
          operation Log = log
evalExpr m (Expr2 o a b) = operation o (evalExpr m a) (evalExpr m b)
    where operation Add = (+)
          operation Mult = (*)
          operation Pow = (**)

diffExpr :: Char -> Expr -> Expr
diffExpr _ (Expr0 (Const _)) = lit 0.0
diffExpr v (Expr0 (Var u))
    | u == v = lit 1.0
    | otherwise = lit 0.0
diffExpr v (Expr1 o a) = outerDerivative o a `times` diffExpr v a
    where outerDerivative Exp = e
          outerDerivative Log = inv
diffExpr v (Expr2 Add a b) = diffExpr v a `plus` diffExpr v b
diffExpr v (Expr2 o a b) = (leftDerivative o a b `times` diffExpr v a) `plus` (rightDerivative o a b `times` diffExpr v b)
    where leftDerivative Mult a b = b
          leftDerivative Pow a b = b `times` (a `toThe` (b `minus` lit 1.0))
          rightDerivative Mult a b = a
          rightDerivative Pow a b = (a `toThe` b) `times` ln a

simplifyExpr :: Expr -> Expr
simplifyExpr e =
    case e of
        Expr1 o a -> go $ Expr1 o $ simplifyExpr a
        Expr2 o a b -> go $ Expr2 o (simplifyExpr a) (simplifyExpr b)
        _ -> e
    where go (Expr2 Mult _ (Expr0 (Const 0.0))) = lit 0.0                           -- x*0 = 0
          go (Expr2 Mult (Expr0 (Const 0.0)) _) = lit 0.0                           -- 0*x = 0
          go (Expr2 Mult (Expr0 (Const 1.0)) a) = a                                 -- x*1 = x
          go (Expr2 Mult a (Expr0 (Const 1.0))) = a                                 -- 1*x = x 
          go (Expr2 Add (Expr0 (Const 0.0)) a) = a                                  -- 0+x = 0
          go (Expr2 Add a (Expr0 (Const 0.0))) = a                                  -- x+0 = 0
          go (Expr2 Add a b) | a == neg b = lit 0.0                                 -- (-x) + x = 0
          go (Expr2 Add a b) | neg a == b = lit 0.0                                 --weil neg (neg a) != neg a
          go (Expr2 Mult a b) | a == inv b = lit 1.0                                -- (1/x)*x = 1
          go (Expr2 Mult a b) | inv a == b = lit 1.0                                -- x * (1/x) = 1
          go (Expr1 Exp (Expr1 Log a)) = a                                          -- exp(log(x)) = x
          go (Expr1 Log (Expr1 Exp a)) = a                                          -- log(exp(x)) = x
          go (Expr2 Add a b) | a == b = lit 2 `times` a                             -- x+x = 2x
          go (Expr2 Mult a b) | a == b = a `toThe` lit 2                            -- x*x = x^2
          go (Expr2 Add (Expr2 Mult a b) c) | b == c = (a `plus` lit 1.0) `times` c -- ax + x = (a+1)x
          go (Expr2 Add c (Expr2 Mult a b)) | b == c = (a `plus` lit 1.0) `times` c -- x + ax = (a+1)x
          go (Expr2 Mult (Expr2 Pow a b) c) | a == c = a `toThe` (b `plus` lit 1.0) -- x^a * x = x^(a+1)
          go (Expr2 Mult c (Expr2 Pow a b)) | a == c = a `toThe` (b `plus` lit 1.0) -- x * x^a = x^(a+1)      
          go (Expr2 Pow a (Expr0 (Const 1.0))) = a                                  -- x^1 = x
          go (Expr2 Pow a (Expr0 (Const 0.0))) = lit 1.0                            -- x^0 = 1
          go a = a

partEvalExpr :: Expr -> Expr
partEvalExpr e =
    case e of
        Expr1 o a -> go $ Expr1 o $ partEvalExpr a
        Expr2 o a b -> go $ Expr2 o (partEvalExpr a) (partEvalExpr b)
        _ -> e
    where go (Expr1 Exp (Expr0 (Const x))) = lit $ exp x
          go (Expr1 Log (Expr0 (Const x))) = lit $ log x
          go (Expr2 Add (Expr0 (Const x)) (Expr0 (Const y))) = lit $ x + y
          go (Expr2 Mult (Expr0 (Const x)) (Expr0 (Const y))) = lit $ x * y
          go (Expr2 Pow (Expr0 (Const x)) (Expr0 (Const y))) = lit $ x ** y
          go a = a

superDiff :: Char -> Expr -> Expr
superDiff v = simplifyExpr . partEvalExpr . simplifyExpr . diffExpr v . simplifyExpr

x :: Expr
x = var 'x'

y :: Expr
y = var 'y'

t :: Expr
t = var 't'
