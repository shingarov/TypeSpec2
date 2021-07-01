module TypeCheck(typecheck) where
import TermType
import FMap

-- check the 2-level types

data T2 = T2BaseS | T2BaseD | T2Void | T2Pair T2 T2 |
          T2Fun T2 T2 | T2UFun T2 T2 | T2SumS T2 T2 |
	  T2SumD T2 T2 | T2TagS String T2 T2 | T2Poly T2 |
	  T2TagD String T2 T2 |
	  T2Var Int | T2Label Int T2 | T2Delay T2 | T2Sum T2 |
	  T2Monad T2 | T2RefS T2 | T2RefD T2
	  deriving (Show,Eq)

showtype t = let (t',ls) = getlabels (prune [] t) in
             showt t'++
	     if null ls then "" else
	     " where "++foldr1 (\x y->x++", "++y)
	                  ["_"++show l++"="++showt t''
			  |(l,t'')<-ls]

showt (T2Fun a b) = sht"->" (showt'' a) (showt b)
showt (T2UFun a b) = sht"@>" (showt'' a) (showt b)
showt (T2Label i a) = "_"++show i++": "++showt a
showt t = showt'' t

showt'' (T2SumS a b) = sht "+" (showt' a) (showt'' b)
showt'' (T2SumD a b) = sht "++" (showt' a) (showt'' b)
showt'' (T2TagS c a b) = sht "|" (c++"@ "++showt' a) (showt'' b)
showt'' (T2TagD c a b) = sht "|" (c++" "++showt' a) (showt'' b)
showt'' t = showt' t
sht op a b = a++op++b

showt' T2BaseS = "Base@"
showt' T2BaseD = "Base"
showt' T2Void = "void"
showt' (T2Poly t) = "poly "++showt' t
showt' (T2Pair a b) = "("++showt a++","++showt b++")"
showt' (T2Delay a) = "delay "++showt' a
showt' (T2Sum a) = "sum "++showt' a
showt' (T2Var x) = "_"++show x
showt' (T2Monad a) = "M "++showt' a
showt' (T2RefS a) = "ref@ "++showt' a
showt' (T2RefD a) = "ref "++showt' a
showt' t = "("++showt t++")"

prune xs (T2Label i t) = let t' = prune (i:xs) t in
                         if i `elem` frees t' then T2Label i t'
			 else t'
prune xs (T2Var i) = T2Var i
prune xs (T2Fun a b) = pr2 xs T2Fun a b
prune xs (T2UFun a b) = pr2 xs T2UFun a b
prune xs (T2SumS a b) = pr2 xs T2SumS a b
prune xs (T2SumD a b) = pr2 xs T2SumD a b
prune xs (T2TagS c a b) = pr2 xs (T2TagS c) a b
prune xs (T2TagD c a b) = pr2 xs (T2TagD c) a b
prune xs (T2Pair a b) = pr2 xs T2Pair a b
prune xs (T2Poly a) = T2Poly (prune xs a)
prune xs (T2Delay a) = T2Delay (prune xs a)
prune xs (T2Sum a) = T2Sum (prune xs a)
prune xs (T2Monad a) = T2Monad (prune xs a)
prune xs (T2RefS a) = T2RefS (prune xs a)
prune xs (T2RefD a) = T2RefD (prune xs a)
prune xs t = t

pr2 xs t a b = t (prune xs a) (prune xs b)

frees (T2Label i t) = frees t
frees (T2Var i) = [i]
frees (T2Fun a b) = fr2 a b
frees (T2UFun a b) = fr2 a b
frees (T2SumS a b) = fr2 a b
frees (T2SumD a b) = fr2 a b
frees (T2TagS c a b) = fr2 a b
frees (T2TagD c a b) = fr2 a b
frees (T2Pair a b) = fr2 a b
frees (T2Poly a) = frees a
frees (T2Delay a) = frees a
frees (T2Sum a) = frees a
frees (T2Monad a) = frees a
frees (T2RefS a) = frees a
frees (T2RefD a) = frees a
frees _ = []

fr2 a b = frees a ++ frees b

getlabels (T2Label i t) = let (t',ls)=getlabels t in 
                          (T2Var i,(i,t'):ls)
getlabels (T2Fun a b) = gl2 T2Fun a b
getlabels (T2UFun a b) = gl2 T2UFun a b
getlabels (T2SumS a b) = gl2 T2SumS a b
getlabels (T2SumD a b) = gl2 T2SumD a b
getlabels (T2TagS c a b) = gl2 (T2TagS c) a b
getlabels (T2TagD c a b) = gl2 (T2TagD c) a b
getlabels (T2Pair a b) = gl2 T2Pair a b
getlabels (T2Poly a) = let (a',ls) = getlabels a in
                       (T2Poly a',ls)
getlabels (T2Delay a) = let (a',ls) = getlabels a in
                        (T2Delay a',ls)
getlabels (T2Sum a) = let (a',ls) = getlabels a in
                        (T2Sum a',ls)
getlabels (T2Monad a) = let (a',ls) = getlabels a in
                        (T2Monad a',ls)
getlabels (T2RefS a) = let (a',ls) = getlabels a in
                        (T2RefS a',ls)
getlabels (T2RefD a) = let (a',ls) = getlabels a in
                        (T2RefD a',ls)

getlabels t = (t,[])

gl2 c a b = let (a',ls1) = getlabels a
                (b',ls2) = getlabels b
	    in (c a' b',ls1++[x|x<-ls2,not(x`elem`ls1)])

-- monad to manage type variables and collect constraints for
-- checking at the end.

data M a = M (State->(a,State))
type State = (Int,Table (Perhaps T2),M ())
data Perhaps a = Yes a | No

unit x = M (\s->(x,s))
M x `bind` f = M (\s->case x s of 
                        (v, s') -> case f v of 
			  M y -> y s')
x `andThen` y = x `bind` \_->y
app f x = x `bind` (unit.f)
bin op x y = x `bind` \u->app (op u) y

fresh = M (\(i,xs,cs)->(i,(i+1,xs,cs)))
-- checking is turned off for now.
--check m = M(\(i,xs,c)->((),(i,xs,c `andThen` m)))
check m = unit ()
runchecks = M (\(i,xs,M c)->c (i,xs,unit ()))
getv w = M(\(i,xs,cs)->(assocT xs w,(i,xs,cs)))
setv w x = M(\(i,xs,cs)->((),(i,updateT w (Yes x) xs,cs)))

-- unification of two-level types, AC-unification of tags
indir (T2Var w) = getv w `bind` \b->case b of
                    Yes z->indir z
		    No -> unit (T2Var w)
indir t = unit t

unify eqs t t'= if (t,t') `elem` eqs then unit ()
                else indir t `bind` \t1->
                     indir t' `bind` \t1'->
	             unify' ((t,t'):eqs) t1 t1'

unify' eqs (T2Var w) (T2Var x) = if w==x then unit () else 
                                 setv w (T2Var x)
unify' eqs (T2Var w) t = setv w t
unify' eqs t (T2Var w) = setv w t
unify' eqs T2BaseS T2BaseS = unit ()
unify' eqs T2BaseD T2BaseD = unit ()
unify' eqs T2Void T2Void = unit ()
unify' eqs (T2Pair a b) (T2Pair c d) = bu eqs a b c d
unify' eqs (T2Fun a b) (T2Fun c d) = bu eqs a b c d
unify' eqs (T2UFun a b) (T2UFun c d) = bu eqs a b c d
unify' eqs (T2SumS a b) (T2SumS c d) = bu eqs a b c d
unify' eqs (T2SumD a b) (T2SumD c d) = bu eqs a b c d
unify' eqs (T2Poly a) (T2Poly b) = unify eqs a b
unify' eqs a@(T2TagS _ _ _) b@(T2TagS _ _ _) = acunify T2TagS eqs a b
unify' eqs a@(T2TagD _ _ _) b@(T2TagD _ _ _) = acunify T2TagD eqs a b
unify' eqs (T2Delay a) (T2Delay b) = unify eqs a b
unify' eqs (T2Sum a) (T2Sum b) = unify eqs a b
unify' eqs (T2Monad a) (T2Monad b) = unify eqs a b
unify' eqs (T2RefS a) (T2RefS b) = unify eqs a b
unify' eqs (T2RefD a) (T2RefD b) = unify eqs a b
unify' eqs a b = uniferr a b

bu eqs a b c d = unify eqs a c `andThen` unify eqs b d

acunify tag eqs a b = 
              gettags a `bind` \(atags,avar)->
              gettags b `bind` \(btags,bvar)->
	      fresh `bind` \c->
	      foldr andThen (unit ())
	        [unify eqs tp (assoc btags tg) 
		| (tg,tp)<-atags, tg `elem` dom btags]
	      `andThen`
	      unify eqs avar 
	        (mk tag c [(tg,tp)
		          |(tg,tp)<-btags, not (tg`elem`dom atags)])
	      `andThen`
	      unify eqs bvar 
	        (mk tag c [(tg,tp)
		          |(tg,tp)<-atags, not (tg`elem`dom btags)])
mk tag c = foldr (\(tg,tp)->tag tg tp) (T2Var c)
gettags a = indir a `bind` \a'-> case a' of
	      T2TagS c t x -> gettags x `bind` \(tgs,vr)->
	                      unit ((c,t):tgs,vr)
	      T2TagD c t x -> gettags x `bind` \(tgs,vr)->
	                      unit ((c,t):tgs,vr)
	      _ -> unit ([],a')

uniferr a b = inst [] a `bind` \a'->
              inst [] b `bind` \b'->
	      error ("in 2-level type checking: cannot unify\n    "
	        ++showtype a'++"\nand "++showtype b')

inst vs t = case t of
  T2Var i -> getv i `bind` \b->case b of
               Yes t'-> case t' of
	                  T2Var j -> inst vs t'
			  _ -> if i `elem` vs then unit (T2Var i)
			       else app (T2Label i) 
			                (inst (i:vs) t')
	       No -> unit (T2Var i)
  T2Pair a b -> bin T2Pair (inst vs a) (inst vs b)
  T2Fun a b -> bin T2Fun (inst vs a) (inst vs b)
  T2UFun a b -> bin T2UFun (inst vs a) (inst vs b)
  T2SumS a b -> bin T2SumS (inst vs a) (inst vs b)
  T2SumD a b -> bin T2SumD (inst vs a) (inst vs b)
  T2TagS c a b -> bin (T2TagS c) (inst vs a) (inst vs b)
  T2TagD c a b -> bin (T2TagD c) (inst vs a) (inst vs b)
  T2Poly a -> app T2Poly (inst vs a)
  T2Delay a -> app T2Delay (inst vs a)
  T2Sum a -> app T2Sum (inst vs a)
  T2Monad a -> app T2Monad (inst vs a)
  T2RefS a -> app T2RefS (inst vs a)
  T2RefD a -> app T2RefD (inst vs a)
  _ -> unit t

tc g (Var s) = unit (assoc g s)
tc g (App a b) = tc g a `bchk` \ta->
                 tc g b `bchk` \tb->
		 fresh `bind` \t->
		 unify [] (T2Fun tb (T2Var t)) ta `andThen`
		 unit (T2Var t)
tc g (Lam x e) = fresh `bind` \t->
                 tc ((x,T2Var t):g) e `bchk` \te->
		 unit (T2Fun (T2Var t) te)
tc g (Let x e1 e2) = tc g e1 `bchk` \t1->
		     tc ((x,t1):g) e2 `bchk` \t2->
		     unit t2
tc g (Pair e1 e2) = tc g e1 `bchk` \t1->
                    tc g e2 `bchk` \t2->
		    unit (T2Pair t1 t2)
tc g (Fst e) = tc g e `bind` \te->
               fresh `bind` \a-> fresh `bind` \b->
	       unify [] te (T2Pair (T2Var a) (T2Var b)) `andThen` 
	       unit (T2Var a)
tc g (Snd e) = tc g e `bind` \te->
               fresh `bind` \a-> fresh `bind` \b->
	       unify [] te (T2Pair (T2Var a) (T2Var b)) `andThen` 
	       unit (T2Var b)
tc g (InlS e) = tc g e `bchk` \te->
                fresh `bind` \a->
		unit (T2SumS te (T2Var a))
tc g (InrS e) = tc g e `bchk` \te->
                fresh `bind` \a->
		unit (T2SumS (T2Var a) te)
tc g (InlD e) = tc g e `bchk` \te->
                fresh `bind` \a->
		unit (T2SumD te (T2Var a))
tc g (InrD e) = tc g e `bchk` \te->
                fresh `bind` \a->
		unit (T2SumD (T2Var a) te)
tc g (CaseS e1 a e2 b e3) =
  tc g e1 `bind` \t1->
  fresh `bind` \ta-> fresh `bind` \tb->
  unify [] (T2SumS (T2Var ta) (T2Var tb)) t1 `andThen`
  tc ((a,T2Var ta):g) e2 `bchk` \t2->
  tc ((b,T2Var tb):g) e3 `bind` \t3->
  unify [] t2 t3 `andThen`
  unit t2
tc g (CaseD e1 a e2 b e3) =
  tc g e1 `bind` \t1->
  fresh `bind` \ta-> fresh `bind` \tb->
  unify [] (T2SumD (T2Var ta) (T2Var tb)) t1 `andThen`
  tc ((a,T2Var ta):g) e2 `bchk` \t2->
  tc ((b,T2Var tb):g) e3 `bind` \t3->
  unify [] t2 t3 `andThen`
  unit t2
tc g (IntS _) = unit T2BaseS
tc g (IntD _) = unit T2BaseD
tc g (StrS _) = unit T2BaseS
tc g (StrD _) = unit T2BaseD
tc g (BoolS _) = unit T2BaseS
tc g (BoolD _) = unit T2BaseD
tc g Void = unit T2Void
tc g (Fix e) = tc g e `bind` \te->
               fresh `bind` \c->
	       unify [] te (T2Fun (T2Var c) (T2Var c)) `andThen`
	       unit (T2Var c)
tc g (Lift e) = tc g e `bind` \te->
                unify [] te T2BaseS `andThen`
		unit T2BaseD
tc g (EqS e1 e2) = tc g e1 `bind` \t1->
                   tc g e2 `bind` \t2->
		   unify [] t1 T2BaseS `andThen`
		   unify [] t2 T2BaseS `andThen`
		   unit T2BaseS
tc g (EqD e1 e2) = tc g e1 `bind` \t1->
                   tc g e2 `bind` \t2->
		   unify [] t1 T2BaseD `andThen`
		   unify [] t2 T2BaseD `andThen`
		   unit T2BaseD
tc g (ArithS op e1 e2) = tc g e1 `bind` \t1->
                   tc g e2 `bind` \t2->
		   unify [] t1 T2BaseS `andThen`
		   unify [] t2 T2BaseS `andThen`
		   unit T2BaseS
tc g (ArithD op e1 e2) = tc g e1 `bind` \t1->
                   tc g e2 `bind` \t2->
		   unify [] t1 T2BaseD `andThen`
		   unify [] t2 T2BaseD `andThen`
		   unit T2BaseD
tc g (TagS c e) = tc g e `bind` \te->
                  fresh `bind` \x->
                  unit (T2TagS c te (T2Var x))
tc g (CaseTagS e cs) =
  tc g e `bind` \te->
  fresh `bind` \res->
  foldr (bin(\(v,z)->T2TagS v z)) --(unit T2Void)
                                  (fresh `bind` (unit.T2Var))
				  -- this change allows
				  -- non-exhaustive cases.
    [fresh `bind` \z->
     tc ((v,T2Var z):g) e' `bchk` \te'->
     unify [] te' (T2Var res) `andThen`
     unit (c,T2Var z) 
    | (c,(v,e'))<-cs] `bind` \tcs->
  unify [] te tcs `andThen`
  unit (T2Var res)
tc g (TagD c e) = tc g e `bind` \te->
                  fresh `bind` \x->
                  unit (T2TagD c te (T2Var x))
tc g (CaseTagD e cs) =
  tc g e `bind` \te->
  fresh `bind` \res->
  foldr (bin(\(v,z)->T2TagD v z)) --(unit T2Void)
                                  (fresh `bind` (unit.T2Var))
				  -- this change allows
				  -- non-exhaustive cases.
    [fresh `bind` \z->
     tc ((v,T2Var z):g) e' `bchk` \te'->
     unify [] te' (T2Var res) `andThen`
     unit (c,T2Var z) 
    | (c,(v,e'))<-cs] `bind` \tcs->
  unify [] te tcs `andThen`
  unit (T2Var res)
tc g (IfS e1 e2 e3) =
  tc g e1 `bind` \t1->
  tc g e2 `bind` \t2->
  tc g e3 `bind` \t3->
  unify [] t1 T2BaseS `andThen`
  unify [] t2 t3 `andThen`
  unit t2
tc g (IfD e1 e2 e3) =
  tc g e1 `bind` \t1->
  tc g e2 `bind` \t2->
  tc g e3 `bind` \t3->
  unify [] t1 T2BaseD `andThen`
  unify [] t2 t3 `andThen`
  unit t2
tc g (Poly e) = tc g e `bchk` \te-> unit (T2Poly te)
tc g (Spec e) = tc g e `bind` \te->
                fresh `bind` \c->
		unify [] te (T2Poly (T2Var c)) `andThen`
		unit (T2Var c)
tc g (ULam s e) = fresh `bind` \c->
                  tc ((s,T2Var c):g) e `bind` \te->
		  unit (T2UFun (T2Var c) te)
tc g (UApp e1 e2) = tc g e1 `bind` \t1->
                    tc g e2 `bind` \t2->
		    fresh `bind` \c->
		    unify [] t1 (T2UFun t2 (T2Var c)) `andThen`
		    unit (T2Var c)
tc g (UFix e) = fresh `bind` \c->
                fresh `bind` \d->
		let tp = T2UFun (T2Var c) (T2Var d) in
                tc g e `bind` \te->
		unify [] te (T2UFun tp tp) `andThen`
		unit tp
tc g (ULet s e1 e2) = tc g e1 `bind` \t1->
                      tc ((s,t1):g) e2  
tc g (InD e) = app T2Sum (tc g e)
tc g (CaseInD e0 a e1) =
  tc g e0 `bind` \t0 ->
  fresh `bind` \ta->
  unify [] (T2Sum (T2Var ta)) t0 `andThen`
  tc ((a,T2Var ta):g) e1
tc g (Unit e) = app T2Monad (tc g e)
tc g (MLet x e1 e2) = tc g e1 `bind` \t->
                      fresh `bind` \a->
		      unify [] t (T2Monad (T2Var a)) `andThen`
		      tc ((x,T2Var a):g) e2 `bind` \t'->
		      fresh `bind` \b->
		      unify [] t' (T2Monad (T2Var b)) `andThen`
		      unit t'
tc g (RefS e) = app (T2Monad . T2RefS) (tc g e)
tc g (RefD e) = app (T2Monad . T2RefD) (tc g e)
tc g (DerefS e) = tc g e `bind` \t->
                  fresh `bind` \a->
		  unify [] t (T2RefS (T2Var a)) `andThen`
		  unit (T2Monad (T2Var a))
tc g (DerefD e) = tc g e `bind` \t->
                  fresh `bind` \a->
		  unify [] t (T2RefD (T2Var a)) `andThen`
		  unit (T2Monad (T2Var a))
tc g (AssignS e1 e2) = tc g e1 `bind` \t1->
                       tc g e2 `bind` \t2->
		       unify [] t1 (T2RefS t2) `andThen`
		       unit (T2Monad T2Void)
tc g (AssignD e1 e2) = tc g e1 `bind` \t1->
                       tc g e2 `bind` \t2->
		       unify [] t1 (T2RefD t2) `andThen`
		       unit (T2Monad T2Void)
tc g (Prompt e) = tc g e `bind` \t->
                  fresh `bind` \a ->
		  unify [] t (T2Monad (T2Var a)) `andThen`
		  unit t


x `bchk` f = x `bind` \t->check (wft t) `andThen` f t
wft t = indir t `bind` \t'-> case t' of
          T2UFun _ _ -> 
	    inst [] t' `bind` \t''->
	    error ("in 2-level typechecking: bad use of\n    "++
	           showtype t'')
	  _ -> unit ()

typecheck t = 
  let M f = (tc [] t `bind` \tp->
             indir tp `bind` \tp'->
	     case tp' of
	       T2Monad _ -> unit True
	       _ -> unit False) in
  case f (0,initT No,unit ()) of
    (b,_) -> b
             -- indicate whether result is a computation or not

