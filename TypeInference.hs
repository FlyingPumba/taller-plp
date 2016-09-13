module TypeInference (TypingJudgment, Result(..), inferType)

where

import Data.List(intersect)
import Exp
import Type
import Unification

------------
-- Errors --
------------
data Result a = OK a | Error String


--------------------
-- Type Inference --
--------------------
type TypingJudgment = (Env, AnnotExp, Type)


inferType :: PlainExp -> Result TypingJudgment
inferType e = case infer' e 0 of
    OK (_, tj) -> OK tj
    Error s -> Error s


infer' :: PlainExp -> Int -> Result (Int, TypingJudgment)
infer' (VarExp x) n = OK (n+1, (extendE emptyEnv x (TVar n), VarExp x, TVar n))
infer' ZeroExp n = OK (n, (emptyEnv, ZeroExp, TNat))
infer' TrueExp n = OK (n, (emptyEnv, TrueExp, TNat))
infer' FalseExp n = OK (n, (emptyEnv, FalseExp, TNat))
infer' (SuccExp e) n = case infer' e n of
  OK (n', (env', e', t)) -> case mgu [(t, TNat)] of
    UOK subst -> OK (n', (subst <.> env', subst <.> SuccExp e', TNat))
    UError u1 u2 -> uError u1 u2
  Error str -> Error str
infer' (PredExp e) n = case infer' e n of
  OK (n', (env', e', t)) -> case mgu [(t, TNat)] of
    UOK subst -> OK (n', (subst <.> env', subst <.> PredExp e', TNat))
    UError u1 u2 -> uError u1 u2
  Error str -> Error str
infer' (IsZeroExp e) n = case infer' e n of
  OK (n', (env', e', t)) -> case mgu [(t, TNat)] of
    UOK subst -> OK (n', (subst <.> env', subst <.> IsZeroExp e', TNat))
    UError u1 u2 -> uError u1 u2
  Error str -> Error str
infer' (IfExp e1 e2 e3) n = case infer' e1 n of
  OK (n1', (env1', e1', t1)) -> case infer' e2 n1' of
    OK (n2', (env2', e2', t2)) -> case infer' e3 n2' of
      OK (n3', (env3', e3', t3)) -> case mgu ((t2, t3):(t1, TBool):([(evalE env1' x, evalE env2' x) | x <- domainE env1', elem x (domainE env2')] ++ [(evalE env1' x, evalE env3' x) | x <- domainE env1', elem x (domainE env3')] ++ [(evalE env3' x, evalE env2' x) | x <- domainE env3', elem x (domainE env2')])) of
        UOK subst -> OK (n3', (joinE [subst <.> env1', subst <.> env2', subst <.> env3'], subst <.> IfExp e1' e2' e3', subst <.> t2))
        UError u1 u2 -> uError u1 u2
      Error str3 -> Error str3
    Error str2 -> Error str2
  Error str1 -> Error str1
infer' (LamExp x t e) n = case infer' e n of
  OK (n', (env', e', t)) -> if elem x (domainE env') then
      OK (n', (removeE env' x, LamExp x t e', TFun (evalE env' x) t))
    else
      OK (n'+1, (removeE env' x, LamExp x t e', TFun (TVar n') t))
  Error str -> Error str
infer' (AppExp e1 e2) n = case infer' e1 n of
  OK (n1', (env1', e1', t1)) -> case infer' e2 n1' of
    OK (n2', (env2', e2', t2)) -> case mgu ((t1, TFun t2 (TVar n2')):[(evalE env1' x, evalE env2' x) | x <- domainE env1', elem x (domainE env2')]) of
      UOK subst -> OK (n2'+1, (joinE [subst <.> env1', subst <.> env2'], subst <.> AppExp e1' e2', subst <.> (TVar n2')))
      UError u1 u2 -> uError u1 u2
    Error str2 -> Error str2
  Error str1 -> Error str1

--------------------------------
-- YAPA: Error de unificacion --
--------------------------------
uError :: Type -> Type -> Result (Int, a)
uError t1 t2 = Error $ "Cannot unify " ++ show t1 ++ " and " ++ show t2
