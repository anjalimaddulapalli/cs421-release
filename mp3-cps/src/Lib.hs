--- Given Code
--- ==========

module Lib where

import System.IO (hPutStrLn, hPutStr, stdout, hFlush)

import Data.List (intercalate)

import Data.Functor.Identity (Identity)
import Text.ParserCombinators.Parsec hiding (Parser)
import Text.Parsec.Prim (ParsecT)

--- Metadata for autograder
--- -----------------------
tag1 = 36392
tag2 = 13977
tag3 = 68529

--- The Types
--- ---------

data Stmt = Decl String [String] Exp
            deriving (Eq)

instance Show Stmt where
    show (Decl f params exp) = f ++ " " ++ intercalate " " params ++ " = " ++ (show exp)

data Exp = IntExp Integer
         | VarExp String
         | LamExp String Exp
         | IfExp Exp Exp Exp
         | OpExp String Exp Exp
         | AppExp Exp Exp
         deriving (Eq)

instance Show Exp where
    show (VarExp s)       = s
    show (IntExp i)       = show i
    show (LamExp x e)     = "(\\" ++ x ++ " -> " ++ (show e) ++ ")"
    show (IfExp e1 e2 e3) = "(if " ++ show e1 ++ " then " ++ show e2
                            ++ " else " ++ show e3 ++ ")"
    show (OpExp op e1 e2) = "(" ++ show e1 ++ " " ++ op ++ " " ++ show e2 ++ ")"
    show (AppExp f e)     = show f ++ " " ++ show e

ctorShow :: Exp -> String
ctorShow (VarExp s)       = "VarExp " ++ show s
ctorShow (IntExp i)       = "IntExp " ++ show i
ctorShow (LamExp x e)     = "LamExp " ++ show x ++ " (" ++ ctorShow e ++ ")"
ctorShow (IfExp e1 e2 e3) = "IfExp (" ++ ctorShow e1 ++ ") ("
                                ++ ctorShow e2 ++ ") ("
                                ++ ctorShow e3 ++ ")"
ctorShow (OpExp op e1 e2) = "OpExp " ++ show op ++ " ("
                                ++ ctorShow e1 ++ ") ("
                                ++ ctorShow e2 ++ ")"
ctorShow (AppExp f e)     = "AppExp (" ++ ctorShow f ++ ") (" ++ ctorShow e ++ ")"

--- Problems
--- ========

--- Manual Translation
--- ------------------

--- ### `factk :: Integer -> (Integer -> t) -> t`

factk :: Integer -> (Integer -> t) -> t
factk 0 k = k 1
factk n k = factk (n - 1) (\v -> k (n * v))

--- ### `evenoddk :: [Integer] -> (Integer -> t) -> (Integer -> t) -> t`

evenoddk :: [Integer] -> (Integer -> t) -> (Integer -> t) -> t
evenoddk [x] ke ko
  | even x    = ke x
  | otherwise = ko x
evenoddk (x:xs) ke ko
  | even x    = evenoddk xs (\v -> ke (x + v)) ko
  | otherwise = evenoddk xs ke (\v -> ko (x + v))

--- Automated Translation
--- ---------------------

gensym :: Integer -> (String, Integer)
gensym i = ("v" ++ show i, i + 1)

--- ### Define `isSimple`

isSimple :: Exp -> Bool
isSimple (IntExp _)        = True
isSimple (VarExp _)        = True
isSimple (LamExp _ _)      = True
isSimple (AppExp _ _)      = False
isSimple (OpExp _ e1 e2)   = isSimple e1 && isSimple e2
isSimple (IfExp e1 e2 e3)  = isSimple e1 && isSimple e2 && isSimple e3

--- ### Define `cpsExp` - Overview

cpsExp :: Exp -> Exp -> Integer -> (Exp, Integer)

--- #### Define `cpsExp` for Integer and Variable Expressions
cpsExp e@(IntExp _) k n = (AppExp k e, n)
cpsExp e@(VarExp _) k n = (AppExp k e, n)
cpsExp e@(LamExp _ _) k n = (AppExp k e, n)
--- #### Define `cpsExp` for Application Expressions
cpsExp (AppExp f e) k n
  | isSimple e = (AppExp (AppExp f e) k, n)
  | otherwise  =
      let (v, n1) = gensym n
      in cpsExp e (LamExp v (AppExp (AppExp f (VarExp v)) k)) n1
--- #### Define `cpsExp` for Operator Expressions
cpsExp (OpExp op e1 e2) k n =
  case (isSimple e1, isSimple e2) of
    (True, True) ->
      (AppExp k (OpExp op e1 e2), n)

    (False, True) ->
      let (v, n1) = gensym n
      in cpsExp e1
           (LamExp v (AppExp k (OpExp op (VarExp v) e2)))
           n1

    (True, False) ->
      let (v, n1) = gensym n
      in cpsExp e2
           (LamExp v (AppExp k (OpExp op e1 (VarExp v))))
           n1

    (False, False) ->
      let (v1, n1) = gensym n
          (v2, n2) = gensym n1
          k2 = LamExp v2 (AppExp k (OpExp op (VarExp v1) (VarExp v2)))
          (e2', n3) = cpsExp e2 k2 n2
      in cpsExp e1 (LamExp v1 e2') n3
--- #### Define `cpsExp` for If Expressions
cpsExp (IfExp e1 e2 e3) k n
  | isSimple e1 =
      let (e2', n1) = cpsExp e2 k n
          (e3', n2) = cpsExp e3 k n1
      in (IfExp e1 e2' e3', n2)
  | otherwise   =
      let (v, n1)  = gensym n
          (e2', n2) = cpsExp e2 k n1
          (e3', n3) = cpsExp e3 k n2
      in cpsExp e1 (LamExp v (IfExp (VarExp v) e2' e3')) n3
--- ### Define `cpsDecl`
cpsDecl :: Stmt -> Stmt
cpsDecl (Decl f params body) =
  Decl f (params ++ ["k"]) (fst (cpsExp body (VarExp "k") 1))
