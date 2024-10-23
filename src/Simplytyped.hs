{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- //TODO: eliminar
module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-----------------------
-- conversion
-----------------------
buscar :: [String] -> String -> Int -> Int
buscar [] s n = -1
buscar (x:xs) s n = if x == s then n else buscar xs s (n+1)

busqueda :: [String] -> LamTerm -> Term 
busqueda l (LVar s)     = if w == -1 then Free (Global s)
                          else Bound w
                            where
                              w = buscar l s 0
busqueda l (LAbs y typ term) = Lam typ (busqueda (y:l) term)  
busqueda l (LApp t1 t2) = busqueda l t1 :@: busqueda l t2
busqueda l (LLet x t1 t2)  = Let (busqueda l t1) (busqueda (x:l) t2) --LET
busqueda l LZero           = Zero
busqueda l (LSuc term)     = Suc (busqueda l term) -- SUC
busqueda l (LRec t1 t2 t3) = Rec (busqueda l t1) (busqueda l t2) (busqueda l t3) -- R  

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = busqueda []

----------------------------
--- evaluador de términos
----------------------------

-- substituye una variable por un término en otro término
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)

-- convierte un valor en el término equivalente
quote :: Value -> Term
quote (VLam t f) = Lam t f

-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval e (Bound x) = VLam EmptyT (Bound x)
eval e (Lam typ term) = VLam typ term
eval e (Free s) = setVal e s
  where 
    setVal ((name, (v,t)):xs) s =
      if name == s then v
      else setVal xs s
eval e (abs@(Lam typ1 term1):@:v@(Lam typ2 term2)) = -- E-APPABS
  eval e (sub 0 v term1) 
eval e (v@(Lam typ ter) :@: t2) = -- E-APP2
  let t2' = eval e t2
      t2t = quote t2' in
    eval e (v :@: t2t)
eval e (t1 :@: t2) = -- E-APP1
  let t1' = eval e t1
      t1t = quote t1'  in
    eval e (t1t :@: t2) 
eval e (Let (Free s) t2) = sub 0 s t2 -- E-LETV
eval e (Let t1 t2) = --  E-LET
  let t1' = eval e t1 in
    eval e (Let t1' t2)
eval e (Rec t1 t2 Zero) = eval e t1 -- E-RZERO
eval e (Rec t1 t2 (Suc x)) = (t2 :@: (Rec t1 t2 x)) :@: x -- E-RSUC
eval e (Rec t1 t2 t3) = -- E-R
  let t3' = eval e t3 in
    eval e (Rec t1 t2 t3') 

--term = ((Lam (FunT EmptyT EmptyT) (Bound 0)):@:(Free (Global "fr")))
----------------------
--- type checker
-----------------------

-- infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu

