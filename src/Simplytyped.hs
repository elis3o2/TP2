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
busqueda l LNil            = Nil
busqueda l (LCons t1 t2)   = Cons (busqueda l t1) (busqueda l t2)
 

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
sub i t (Let t1 t2) = Let (sub i t t1) (sub (i + 1) t t2)
sub i t Zero        = Zero
sub i t (Suc t')    = sub i t t'
sub i t (Rec t1 t2 t3) = Rec (sub i t t1) (sub i t t2) (sub i t t3)
sub i t Nil         = Nil
sub i t (Cons n vl) = Cons (sub i t n) (sub i t vl)

-- convierte un valor en el término equivalente
quote :: Value -> Term
quote (VLam t f    ) = Lam t f
quote (VNum NZero  ) = Zero
--quote (VNum (NSuc n)) = Suc (quote n)
--quote (VList VNil  )  = Nil
--quote (VList (VCons n vl)) = Cons (quote n) (quote vl)
--
---- convierte un NumVal a un termino equivalente
--quote2 :: NumVal -> Term
--quote2 (NZero)  = Zero
--quote2 (NSuc x) = Suc (quote2 x)

-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval e (Bound x) = VLam EmptyT (Bound x)
eval e (Lam typ term) = VLam typ term
eval e (Free s) = setVal e s
  where
    setVal ((name, (v,t)):xs) s =
      if name == s then v
      else setVal xs s

eval e (abs@(Lam typ1 term1):@:t2) = 
  let t2' = eval e t2       -- E-APP1
      t2t = quote t2'
  in eval e (sub 0 t2t term1)     -- APPABS

eval e (t1 :@: t2) = -- E-APP1
  let t1' = eval e t1
      t1t = quote t1'  in
    eval e (t1t :@: t2)

eval e (Let t1 t2) = 
  let t1' = eval e t1    -- E-LET 
      t1t = quote t1' in -- E-LETV
    eval e (sub 0 t1t t2)

eval e Zero = VNum NZero
eval e (Suc n) = 
  let (VNum n') = eval e n
  in VNum (NSuc n')
  
eval e (Rec t1 t2 Zero) = eval e t1 -- E-RZERO
eval e (Rec t1 t2 (Suc x)) = eval e ((t2 :@: Rec t1 t2 x):@:x) -- E-RSUC

eval e (Rec t1 t2 Nil) = eval e t1  --ERNIL
eval e (Rec t1 t2 (Cons n lv)) = eval e ((t2 :@: (n :@: lv)) :@: (Rec t1 t2 lv)) -- ERCONS 

eval e (Rec t1 t2 t3) = -- E-R
  let t3' = eval e t3
      t3t = quote t3' in
    eval e (Rec t1 t2 t3t) 

eval e Nil = VList VNil
eval e (Cons t1 t2) =  -- E-CONS1 y E-CONS2
  let (VNum t1') = eval e t1
      (VList t2') = eval e t2 in
    VList (VCons t1' t2')
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

checkNat :: Type -> Either String Type
checkNat NatT = ret NatT
checkNat t = matchError NatT t

checkList :: Type -> Either String Type
checkList ListT = ret ListT
checkList t = matchError ListT t

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if tu == t1 then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu

infer' c e (Let t1 t2) = infer' c e t1 >>= \tt1 -> infer' (tt1:c) e t2
infer' c e Zero       = ret NatT
infer' c e (Suc t)    = infer' c e t >>= \tt -> checkNat tt
infer' c e Nil         = ret ListT
infer' c e (Cons n vl) = infer' c e n >>= \tn -> infer' c e vl >>= \tvl ->
    case tn of
        NatT -> case tvl of
                ListT -> ret ListT
                _     -> matchError ListT tvl
        _    -> matchError NatT tn

infer' c e (Rec t1 t2 t3) =
  infer' c e t1 >>= \tt1 ->
    infer' c e t2 >>= \tt2 ->
      case tt2 of
        (FunT (FunT tt1' NatT) tt1'') -> if tt1' == tt1 && tt1'' == tt1 then
                                         infer' c e t3 >>= \tt3 -> checkList tt3
                                         else matchError tt1 tt1' 
        (FunT (FunT NatT ListT) (FunT tt1' tt1'')) -> if tt1' == tt1 && tt1'' == tt1 then
                                                      infer' c e t3 >>= \tt3 -> checkNat tt3
                                                      else matchError tt1 tt1' 
        _          -> notfunError tt2
