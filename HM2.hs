-- This module defines and benchmarks a Hindley-Milner
-- type-checker.

import FMap

-- expressions and types

data E = Var String
       | App E E
       | Lam String E
       | Con Int

data T = TVar Int
       | TFun T T
       | TInt
       | TAny           -- equivalent to unnamed variable
       deriving Text

-- monad

data M a = M (State -> (a,State))
type State = (Int,Table (Maybe T))
data Maybe a = Yes a | No

unit x = M(\s->(x,s))
M x `bind` f = M (\s->let (v,s') = x s
                          M y = f v
		      in y s')

fresh = M(\(n,t)->(TVar n,(n+1,t)))
getv i = M(\(n,t)->(assocT t i,(n,t)))
setv i v = M(\(n,t)->(v,(n,updateT i (Yes v) t)))

run (M x) = let (v,(n,_)) = x (0,initT No) in
            show n++" variables used\n"++v

x`andThen` y = x `bind` \_->y
bin op x y = x `bind` \u-> y `bind` \v-> unit (u `op` v)

-- unification
unify x y = indir x `bind` \x'->
            indir y `bind` \y'->
	    case (x',y') of
	      (TAny,_) -> unit y'
	      (_,TAny) -> unit x'
	      (TVar m,TVar n) ->
	        if m==n then unit x' else setv m (TVar n)
	      (TVar m,t) -> setv m t
	      (t,TVar n) -> setv n t
	      (TFun a b,TFun c d) -> 
	        bin TFun (unify a c) (unify b d)
	      (TInt,TInt) -> unit TInt
	      _ -> error ("Cannot unify "++show x'++" and "++
	                  show y'++"\n")
	 
indir (TVar m) = getv m `bind` \z->case z of
                   Yes t -> indir t
		   No -> unit (TVar m)
indir t = unit t

-- instantiation
inst t = indir t `bind` \t'-> case t' of
           TFun a b -> bin TFun (inst a) (inst b)
	   _ -> unit t'

-- typechecker
tc g (Var s) t = unify (assoc g s) t
tc g (Con n) t = unify TInt t
tc g (App a b) t = tc g b TAny `bind` \s'->
                   tc g a (TFun s' t) `bind` \(TFun _ t')->
		   unit t'
tc g (Lam s e) t = 
  indir t `bind` \t->
  case t of
    TFun x y ->
      tc ((s,x):g) e y `andThen`
      unit (TFun x y)
    _ -> fresh `bind` \x->
         tc ((s,x):g) e TAny `bind` \y'->
	 unify t (TFun x y') `andThen`
	 unit (TFun x y')

-- benchmark
ap = Lam "f" (Lam "x" (App (Var "f") (Var "x")))
bm 0 = ap
bm n = App (bm (n-1)) ap

main = interact (\_ -> run (tc [] (bm 1000) TAny `bind` \t->
			    inst t `bind` \t'->
			    unit (show t')))
