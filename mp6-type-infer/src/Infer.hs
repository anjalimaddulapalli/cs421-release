module Infer where

import Common

import Control.Monad.Writer (listen, censor)
import Control.Monad.Except (throwError)
import Data.Map.Strict as H (Map, insert, lookup, empty, fromList, singleton)

tag1 = 64002
tag2 = 68869
tag3 = 19545

  {- question 1: fresh instance function -}

freshInst :: PolyTy -> Infer MonoTy
freshInst (Forall qVars tau) = do
  freshVars <- mapM (\_ -> freshTau) qVars
  let subst = H.fromList (zip qVars freshVars)
  return $ apply subst tau

  {- question 2: occurs check -}

occurs :: VarId -> MonoTy -> Bool
occurs i tau = i `elem` freeVars tau

  {- question 3: unification -}

unify :: [Constraint] -> Infer Substitution
unify [] = return substEmpty

unify ((t1 :~: t2):cs)
  | t1 == t2 = unify cs

unify ((TyVar v :~: t):cs) =
  if occurs v t
    then throwError (InfiniteType v t)
    else do
      let s = substInit v t
      s' <- unify (map (apply s) cs)
      return (substCompose s' s)

unify ((t :~: TyVar v):cs) =
  unify ((TyVar v :~: t):cs)

unify ((TyConst c1 ts1 :~: TyConst c2 ts2):cs)
  | c1 == c2 && length ts1 == length ts2 =
      unify (zipWith (:~:) ts1 ts2 ++ cs)
  | otherwise =
      throwError (Can'tMatch t1 t2)
  where
    t1 = TyConst c1 ts1
    t2 = TyConst c2 ts2

  {- question 4: type inference -}

infer :: TypeEnv -> Exp -> Infer MonoTy

-- constants
infer env (ConstExp c) = freshInst (constTySig c)

-- variables
infer env (VarExp x) =
  case H.lookup x env of
    Nothing -> throwError (LookupError x)
    Just sigma -> freshInst sigma

-- unary ops
infer env (MonOpExp op e) = do
  tau <- infer env e
  opTau <- freshInst (monopTySig op)
  result <- freshTau
  constrain opTau (funTy tau result)
  return result

-- binary ops
infer env (BinOpExp op e1 e2) = do
  t1 <- infer env e1
  t2 <- infer env e2
  opTau <- freshInst (binopTySig op)
  result <- freshTau
  constrain opTau (funTy t1 (funTy t2 result))
  return result

-- if
infer env (IfExp e1 e2 e3) = do
  t1 <- infer env e1
  t2 <- infer env e2
  t3 <- infer env e3
  constrain t1 boolTy
  constrain t2 t3
  return t2

-- function
infer env (FunExp x e) = do
  arg <- freshTau
  let env' = H.insert x (Forall [] arg) env
  body <- infer env' e
  return (funTy arg body)

-- application
infer env (AppExp e1 e2) = do
  t1 <- infer env e1
  t2 <- infer env e2
  result <- freshTau
  constrain t1 (funTy t2 result)
  return result

-- let
infer env (LetExp x e1 e2) = do
  (t1, cs1) <- listen $ infer env e1
  s1 <- unify cs1
  let env' = apply s1 env
  let sigma = gen env' (apply s1 t1)
  infer (H.insert x sigma env') e2

-- let rec
infer env (LetRecExp f x e1 e2) = do
  arg <- freshTau
  res <- freshTau

  let fType = funTy arg res
  let env' = H.insert f (Forall [] fType) env
  let env'' = H.insert x (Forall [] arg) env'

  (body, cs1) <- censor (const []) $ listen $ infer env'' e1

  s1 <- unify ((body :~: res) : cs1)

  let envFinal = apply s1 env
  let fTypeFinal = apply s1 fType
  let sigma = gen envFinal fTypeFinal

  infer (H.insert f sigma envFinal) e2

inferInit :: TypeEnv -> Exp -> Infer PolyTy
inferInit env e = do
  (tau, constraints) <- listen $ infer env e
  substitution <- unify constraints
  return $ gen (apply substitution env) (apply substitution tau)

inferDec :: TypeEnv -> Dec -> Infer (TypeEnv, PolyTy)
inferDec env (AnonDec e') = do
  tau <- inferInit env e'
  return (env, tau)
inferDec env (LetDec x e') = do
  tau <- inferInit env (LetExp x e' (VarExp x))
  return (H.insert x tau env, tau)
inferDec env (LetRec f x e') = do
  tau <- inferInit env (LetRecExp f x e' (VarExp f))
  return (H.insert f tau env, tau)
