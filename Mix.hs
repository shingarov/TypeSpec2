module Mix where
import Types
import FMap
import Monad
import Unify
--import VoidErasure
import ArityRaiser
import Parser(prettyprint)
import TypeCheck(typecheck)
import Freevars
import Trace
import ShowType

-- the partial evaluator itself:
-- mix :: context -> expr -> static val -> scope ->
--                           transformed expr
-- rename variables in residual program, integral unfolding
-- context maps vars -> (static val,replacement exp)
--   (bound vars in replacement exps need not be renamed)

mix g e t = app (\x->(x,t)) (mix' g e t)
     -- label each residual expr with its static value

-- pjt: is the compiler smart enough to lift (assoc g s)?
mix' g (Var s) t = let entry = assoc g s in
	unify t (fst entry) `andThen` 
	unit (snd entry)
mix' g (Pair u v) t = fresh2 `bind` \(x,y)->
                      unify t (SPair x y) `andThen`
	              bin TPair (mix g u x) (mix g v y)
mix' g (Fst u) t = fresh `bind` \x->
                   app TFst (mix g u (SPair t x))
mix' g (Snd u) t = fresh `bind` \x->
                   app TSnd (mix g u (SPair x t))
mix' g (InlS u) t = fresh `bind` \x->
                    unify t (SInl x) `andThen`
                    mix' g u x
mix' g (InrS u) t = fresh `bind` \x->
                    unify t (SInr x) `andThen`
                    mix' g u x
mix' g (CaseS u a v b w) t =
  fresh `bind` \x->
  mix' g u x `bind` \u'->
  demon x (\x'-> case x' of
    SInl y -> mix' ((a,(y,u')):g) v t
    SInr y -> mix' ((b,(y,u')):g) w t
    _ -> showtype x' `bind` \xt->
         failM ("CaseS demon invoked on "++xt++" in:\n"++
               show (CaseS u a v b w)))
mix' g (InlD u) t = fresh2 `bind` \(x,y)->
                    unify t (SSum x y) `andThen`
	            app TInl (mix g u x)
mix' g (InrD u) t = fresh2 `bind` \(x,y)->
                    unify t (SSum x y) `andThen`
	            app TInr (mix g u y)
mix' g (CaseD u a v b w) t =
  fresh2 `bind` \(x,y)->
  tri (\u' (a',v') (b',w')->TCase u' a' v' b' w')
    (mix g u (SSum x y))
    (rename a $ \a'->unit a' `pair` mix ((a,(x,TVar a')):g) v t)
    (rename b $ \b'->unit b' `pair` mix ((b,(y,TVar b')):g) w t)
mix' g (Lam v e) t = fresh2 `bind` \(x,y)->
                     unify t (SFun x y) `andThen`
		     (rename v $ \v'->
	              app (TLam v') 
		        (mix ((v,(x,TVar v')):g) e y))
mix' g (App u v) t = fresh `bind` \x->
                     -- making the calls to mix in this order
	             -- dramatically improves performance.
		     bin (\a b->TApp b a)
		       (mix g v x)
		       (mix g u (SFun x t))
mix' g (Let a u v) t = fresh `bind` \x->
                       bin (\u' (a',v')->TLet a' u' v') 
		         (mix g u x) 
		         (rename a $ \a'->
			  unit a' `pair`
			  mix ((a,(x,TVar a')):g) v t)
mix' g (IntS n) t = unify t (SInt n) `andThen` unit TVoid
mix' g (IntD n) t = unify t SIntD `andThen` unit (TInt n)
mix' g (StrS n) t = unify t (SStr n) `andThen` unit TVoid
mix' g (StrD n) t = unify t SIntD `andThen` unit (TStr n)
mix' g (BoolS n) t = unify t (SBool n) `andThen` unit TVoid
mix' g (BoolD n) t = unify t SBoolD `andThen` unit (TBool n)
mix' g (ArithD op u v) t =
  unify t SIntD `andThen`
  mix g u SIntD `bind` \u'->
  mix g v SIntD `bind` \v'->
  unit (TArith op u' v')
mix' g (ArithS op u v) t =
  fresh2 `bind` \(a,b)->
  mix g u a `bind` \_->
  mix g v b `bind` \_->
  demon a $ expectSInt ("mix/ArithS(1) "++op) [u,v] $ \m->
  demon b $ expectSInt ("mix/ArithS(2) "++op) [u,v] $ \n->
  unify t (SInt (case op of
                   "+" -> m+n
		   "-" -> m-n
		   "*" -> m*n
		   "/" -> m`div`n)) `andThen`
  unit TVoid
mix' g Void t = unify t SVoid `andThen` unit TVoid
mix' g (Fix e) t = app TFix (mix g e (SFun t t))
mix' g (Lift e) t = 
  fresh `bind` \x->
  mix g e x `bind` \e'->
  demon x $ \x'-> case x' of
    SInt n -> unify t SIntD `andThen` unit (TInt n)
    SStr s -> unify t SStrD `andThen` unit (TStr s)
    SBool b -> unify t SBoolD `andThen` unit (TBool b)
    _ -> showtype x' `bind` \xt->
         failM ("Lift: cannot lift "++xt)
mix' g (EqS e1 e2) t = fresh2 `bind` \(x,y)->
                       mix g e1 x `bind` \e1'->
	               mix g e2 y `bind` \e2'->
		       demon x $ \x' ->
		       demon y $ \y' ->
		       unify t (SBool (x'==y'))
		       `andThen`
		       unit TVoid
mix' g (EqD e1 e2) t = unify t SBoolD `andThen`
                       fresh `bind` \z->
                       mix g e1 z `bind` \e1'->
                       mix g e2 z `bind` \e2'->
		       unit (TEq e1' e2')
mix' g (TagS s u) t = fresh `bind` \x->
                      unify t (STag s x) `andThen`
		      mix' g u x
mix' g (CaseTagS u cs) t =
  fresh `bind` \x->
  (case cs of 
     [(con,_)] -> fresh `bind` \y-> unify x (STag con y)
     _ -> unit ()) `andThen`
  mix' g u x `bind` \u'->
  demon x (\x'-> case x' of
    STag s y -> if s `elem` dom cs then
                  let (a,v) = assoc cs s in
		  mix' ((a,(y,u')):g) v t
		else showtype x' `bind` \xt->
		     failM ("No match in case: "++xt++
		           " does not match "++show(map fst cs)++
			   "\n")
    SVoid -> -- i.e. this case is dead code.
             unit TVoid -- this might not be type-correct
    _ -> failM ("CaseTagS demon invoked on "++show x'++
	       " in:\n"++show (CaseTagS u cs)))
mix' g (IfS e1 e2 e3) t =
  fresh `bind` \b->
  mix' g e1 b `bind` \_ ->
  demon b (\b'-> case b' of
    SBool bv -> if bv then mix' g e2 t else mix' g e3 t
    _ -> showtype b' `bind` \bt->
         failM ("No match in if@: "++bt++" is not a boolean"))
mix' g (IfD e1 e2 e3) t =
  mix g e1 SBoolD `bind` \e1' ->
  mix g e2 t `bind` \e2' ->
  mix g e3 t `bind` \e3' ->
  unit (TIf e1' e2' e3')
mix' g (TagD s u) t = 
  fresh `bind` \x->
  fresh `bind` \y->
  unify t (STagD s x y) `andThen`
  mix g u x `bind` \u'->
  unit (TTag s u')
mix' g (CaseTagD u cs) t =
  fresh `bind` \v->
  mix g u v `bind` \u'->
  foldr (\(c,(x,e)) cs'->
           fresh `bind` \w->
	   fresh `bind` \z->
	   unify v (STagD c w z) `andThen`
	   (rename x $ \x'->
	    mix ((x,(w,TVar x')):g) e t `bind` \e'->
	    cs' `bind` \cs''->
	    unit ((c,(x',w,e')):cs'')))
    (unit [])
    cs `bind` \cs'->
  unit (TCaseTag u' cs')
-- polyvariance:
{-mix' g (Poly e) t = demon t $ \z-> case z of
        SPair x y ->
          bin TPair (mix g e x)
	            (mix g (Poly e) y)
	SVoid -> unit TVoid
	_ -> expectError "mix/Poly" [e] "Pair x y/SVoid" z
mix' g (Spec e) t = fresh2 `bind` \(x,y)->
                    mix g e x `bind` \e'->
	            find x e' y
  where find x e' y = 
          indirect x `bind` \x'->case x' of
	    SVar w -> -- no backtracking in this case
	              setvar w (SPair t y) `andThen` unit (TFst e')
	    SPair _ x'' -> 
	         (unify x' (SPair t y) `andThen` unit (TFst e'))
	         `orelse`
		 find x'' (TSnd e',x'') y
	    _ -> expectError "mix/Spec" [e] "SPair/SVoid" x'
-}
mix' g (Poly e) t = 
  demon t $ \t'-> case t' of
    SVoid -> -- i.e. poly with no variants
             unit (TTup [])
    SPoly set -> mapSet (mix g e) set $ \variants->
                 unit (TTup variants)
mix' g (Spec e) t = fresh `bind` \x->
                    mix g e x `bind` \e'->
		    singleton t `bind` \(set,inx)->
		    unify x (SPoly set) `andThen`
		    demon inx (expectSInt "mix/Spec" [e] $ \i->
		    unit (TPrj i e'))
-- unfolding
mix' g (ULam s e) t =
-- pjt: does the compiler lift (freevars e) out of the lambda?
  let fvs0 = freevars e
      fvs = restrict (\n->n/=s&&n`elem`fvs0) g in
  unify t (SClos (map fst fvs) (map (fst.snd) fvs) s e) `andThen`
  unit (dprod (map snd fvs))
mix' g (UApp e1 e2) t =
  fresh2 `bind` \(y,z)->
  mix' g e1 y `bind` \e1'->
  mix' g e2 z `bind` \e2'-> 
  demon y $ \y'->case y' of
    SClos ns0 ss0 x e0->
      mix' ((x,(z,e2')):cpts ns0 ss0 e1') e0 t
    SFix f ns0 ss0 x e0->
      mix' ((x,(z,e2')):(f,(y',e1')):cpts ns0 ss0 e1') e0 t
    _ -> expectError "mix/UApp" [e1,e2] "SClos" y'
mix' g (ULet x e1 e2) t =
  fresh `bind` \z->
  mix' g e1 z `bind` \e1'->
  mix' ((x,(z,e1')):g) e2 t
mix' g (UFix e) t =
  fresh `bind` \z->
  mix' g e z `bind` \e'->
  demon z $ \z'->case z' of
    SClos ns0 ss0 x e0->
      -- Evaluate e0 without a binding for x. Result must be
      -- a SClos, which we fix up afterwards.
      fresh `bind` \y->
      mix' (cpts ns0 ss0 e') e0 y `bind` \e0'->
      demon y $ \y'->case y' of
        SClos ns1 ss1 x1 e1->
	  unify t (SFix x ns1 ss1 x1 e1) `andThen`
	  unit e0'
	_ -> expectError "mix/UFix(2)" [e] "SClos" y'
    _ -> expectError "mix/UFix" [e] "SClos" z'

-- constructor specialisation
mix' g (InD e) t = fresh `bind` \x->
                   mix g e x `bind` \e'->
		   singleton x `bind` \(set,inx)->
		   unify t (SIn set) `andThen`
		   demon inx (expectSInt "mix/InD" [e] $ \i->
		   unit (TIn i e'))
mix' g (CaseInD e u f) t =
  fresh `bind` \x->
  mix g e x `bind` \e'->
  demon x $ \z-> case z of
    SIn set -> rename u $ \u'->
               mapSet (\sv->app(\e'->(sv,e')) 
	                       (mix ((u,(sv,TVar u')):g) f t)) 
		      set $ 
	       \cases->
	       unit (TCaseN e' u' cases)
    SVoid -> -- i.e. set with no constructors
             rename u $ \u'->
	     unit (TCaseN e' u' [])
    _ -> expectError "mix/CaseInD" [e] "SIn" z
mix' g (Unit e) t = fresh2 `bind` \(x,y)->
                    unify t (SFun x (SMonad (SPair y x))) `andThen`
		    mix g e y `bind` \e'->
		    rename "s" $ \s->
		    unit (TLam s (TUnit (TPair e' (TVar s,x),SPair y x)
		                 ,SMonad (SPair y x)))
mix' g (MLet x e1 e2) t =
  fresh2 `bind` \(t1,t2)-> fresh2 `bind` \(s1,s2)-> fresh `bind` \s3->
  unify t (SFun s1 (SMonad (SPair t2 s3))) `andThen`
  mix g e1 (SFun s1 (SMonad (SPair t1 s2))) `bind` \e1'->
  rename x $ \x'->
  mix ((x,(t1,TFst (TVar x',SPair t1 s2))):g) e2 
      (SFun s2 (SMonad (SPair t2 s3))) `bind` \e2'->
  rename "s" $ \s->
  unit (TLam s (TMLet x' (TApp e1' (TVar s,s1),SMonad (SPair t1 s2))
                         (TApp e2' (TSnd (TVar x',SPair t1 s2), s2),
			           SMonad (SPair t2 s3))
               ,SMonad (SPair t2 s3)))
mix' g (RefD e) t =
  fresh2 `bind` \(t1,s1)->
  unify t (SFun s1 (SMonad (SPair (SRef t1) s1))) `andThen`
  mix g e t1 `bind` \e'->
  rename "s" $ \s'->
  rename "r" $ \r'->
  unit (TLam s' (TMLet r' (TMkref e',SMonad (SRef t1))
                          (TUnit (TPair (TVar r',SRef t1) (TVar s',s1),
			          SPair (SRef t1) s1),
			   SMonad (SPair (SRef t1) s1)),
		 SMonad (SPair (SRef t1) s1)))
mix' g (DerefD e) t =
  fresh2 `bind` \(s1,t1)->
  unify t (SFun s1 (SMonad (SPair t1 s1))) `andThen`
  mix g e (SRef t1) `bind` \e'->
  rename "s" $ \s'->
  rename "x" $ \x'->
  unit (TLam s' (TMLet x' (TDeref e', SMonad t1)
                          (TUnit (TPair (TVar x',t1) (TVar s',s1),
			          SPair t1 s1),
			   SMonad (SPair t1 s1)),
		 SMonad (SPair t1 s1)))
mix' g (AssignD e1 e2) t =
  fresh2 `bind` \(s1,t1)->
  unify t (SFun s1 (SMonad (SPair SVoid s1))) `andThen`
  mix g e1 (SRef t1) `bind` \e1'->
  mix g e2 t1 `bind` \e2'->
  rename "s" $ \s'->
  rename "x" $ \x'->
  unit (TLam s' (TMLet x' (TAssign e1' e2',SMonad SVoid)
                          (TUnit (TPair (TVoid,SVoid) (TVar s',s1),
			          SPair SVoid s1),
			   SMonad (SPair SVoid s1)),
		 SMonad (SPair SVoid s1)))
mix' g (RefS e) t =
  freshs 4 `bind` \[s,t',s1,n1]->
  unify t (SFun s (SMonad (SPair n1 s1))) `andThen`
  mix g e t' `bind` \e'->
  demon s $ \s' ->
    case s' of
      SStore n ts -> 
        rename "s" $ \svar->
	unify s1 (SStore (n+1) (SPair t' ts)) `andThen`
	unify n1 (SInt (n+1)) `andThen`
        unit (TLam svar (TUnit (TPair (TVoid, n1)
	                              (TPair (TVar svar, s')
				             e',
				       s1),
				SPair n1 s1),
			 SMonad (SPair n1 s1)))
      _ -> failM ("RefS demon invoked on "++show s'++
                 " in:\n"++show (RefS e))
mix' g (DerefS e) t =
  freshs 3 `bind` \[s, t', tl]->
  unify t (SFun s (SMonad (SPair tl s))) `andThen`
  mix g e t' `bind` \e'->
  demon s $ \s' ->
    case s' of
      SStore n ts ->
        demon t' $ \t'' ->
          case t'' of
            SInt l ->
	      -- no need to wait for ts, it is available as soon as 
	      -- SStore is available
	      rename "s" $ \svar->
	      let select@(_, tl1) = make_select (n-l) ts (TVar svar, s') in
	        unify tl tl1 `andThen`
        	unit (TLam svar (TUnit (TPair select (TVar svar, s'),
         	                        SPair tl s'),
        			 SMonad (SPair tl s')))
            _ -> failM ("DerefS/SInt demon invoked on "++show t'++
                 " in:\n"++show (DerefS e))
      _ -> failM ("DerefS/SStore demon invoked on "++show s'++
                 " in:\n"++show (DerefS e))
mix' g (AssignS e1 e2) t =
  freshs 4 `bind` \[s1, s2, t1, t2] ->
  unify t (SFun s1 (SMonad (SPair SVoid s2))) `andThen`
  mix g e1 t1 `bind` \e1'->
  mix g e2 t2 `bind` \e2'->
  demon s1 $ \s' ->
    case s' of
      SStore n ts ->
        demon t1 $ \t1' ->
          case t1' of
            SInt l ->
	      rename "s" $ \svar ->
	      let replace@(_,ts')
                    = make_replace (n-l) ts (TVar svar, ts) e2' in
		unify s2 (SStore n ts') `andThen`
	        unit (TLam svar (TUnit (TPair (TVoid, SVoid) replace,
                                        SPair SVoid s2),
				 SMonad (SPair SVoid s2)))
            _ -> failM ("AssignS/SInt demon invoked on "++show t1'++
                 " in:\n"++show (AssignS e1 e2))
      _ -> failM ("AssignS/SStore demon invoked on "++show s'++
                 " in:\n"++show (AssignS e1 e2))
mix' g (Prompt e) t =
  freshs 4 `bind` \[s1, s2, t1, s3] ->
  unify t (SFun s1 (SMonad (SPair t1 s2))) `andThen`
  mix g e (SFun s1 (SMonad (SPair t1 s3))) `bind` \e'->
  demon s3 $ \s3' ->
  demon s1 $ \s1' ->
  case (s1', s3') of
    (SStore n1 ts1, SStore n2 ts2)
      | n1 == n2 -> unify s2 s3' `andThen`
                    unit (fst e')
      | otherwise ->
        rename "s" $ \svar-> rename "v" $ \vvar->
	let (rterm,rtype) = make_remove (n2-n1) ts2 (TVar svar, ts2) in
	unify s2 (SStore n1 rtype) `andThen`
	unit (TLam svar (TMLet vvar (TApp e' (TVar svar, s1),
	                             SMonad (SPair t1 s3))
				    (TUnit (TPair (TFst (TVar vvar,
				                         SPair t1 s3),
						   t1)
						  (rterm, SStore n1 rtype),
					    (SPair t1 s2)),
				     SMonad (SPair t1 s2)),
			 SMonad (SPair t1 s2)))
    _ -> failM ("Prompt/SStore demon invoked on "++show (s1',s3')++
                 " in:\n"++show (Prompt e))
mix' g u t = error ("No match for mix "++
                   unwords [show g, show u, show t])

make_select i (SPair e spine) x
  | i==0      = (TFst x, e)
  | otherwise = make_select (i-1) spine (TSnd x, spine)

make_replace i (SPair e spine) x new@(_,t)
  | i==0      = (TPair new (TSnd x, spine), SPair t spine)
  | otherwise = (TPair (TFst x, e) rest, SPair e restt)
       where rest@(_, restt) = make_replace (i-1) spine (TSnd x, spine) new

make_remove 0 _ x = x
make_remove i (SPair e spine) x = make_remove (i-1) spine (TSnd x, spine)

  
sprod = foldr SPair SVoid
dprod = fst.foldr (\(s,e) (tl,tls)-> 
                   (TPair (e,s) (tl,tls), (SPair s tls)))
		  (TVoid,SVoid)
cpts [] [] e = []
cpts (n:ns) (s:ss) e = 
  (n,(s,TFst (e,sprod (s:ss)))):
  cpts ns ss (TSnd (e,sprod(s:ss)))


runmix dbg t = (if dbg then show t else "")++
               (let isM = typecheck t in
	       seq isM$
               let M f = fresh `bind` \v->
			 (if isM then
			    fresh2 `bind` \(tout, sout)->
			    unify v (SFun (SStore 0 SVoid)
			               (SMonad (SPair tout sout)))
			  else unit ())
			 `andThen`
                         mix [] t v `bind` \t'->
			 tr dbg "Specialisation proper complete\n" $
			 -- complete sets
			 unify completesets SVoid `andThen`
			 (tr dbg "Sets completed\n" $
			 -- set any remaining uninstantiated
			 -- static values to Void.
			 arityraise t')
	       in
           case f [] (1,initT (Empty []),0,[]) of
	       -- preallocated SVars: completesets = 0
	     Yes (((n,env,tv,tvs),t'):_)->
	       (if dbg then "Static variables: "++show n++"\n" else "")++
	       "Residual type: "++showstat env (SVar 1)++"\n"++
	       "Residual code:\n"++prettyprint t'++"\n"++
	       (if dbg then 
	       "where\n"++
	       unlines ["TVar "++show i++" = "++show e|
	                (i,e)<-tvs]++
	          "Env: "++show env++"\n"
		else "")
	     No s -> error (s++"\n"))

tr dbg s x = if dbg then trace s x else x

