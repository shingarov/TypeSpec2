module TwoLevelUnification where
import TwoLevelTypes
import FMap

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

