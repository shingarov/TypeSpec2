module Generator
import Types
import Monad

type EnvEntry = (String, TTerm)
type Env = [EnvEntry]

newtype Generator a = G (Env -> Stat -> M TTerm)

-- polymorphic in annotations?

gen_var :: G a
gen_var = G (\g -> let entry = assoc g s in
             \t -> unify t (fst entry) `andThen` 
	           unit (snd entry))

gen_pair :: G a -> G b -> G (PAIR a b)
gen_pair = wrap2_simple gen_pair_worker
gen_pair_worker gen_a gen_b t = 
	fresh2 `bind` \(x,y)->
	unify t (SPair x y) `andThen`
	bin TPair (wrapt gen_a x) (wrapt gen_b y)

gen_fst :: G (PAIR a b) -> G a
gen_fst = wrap1_simple gen_fst_worker
gen_fst_worker gen_a t =
	fresh `bind` \x->
	app TFst (wrapt gen_a (SPair t x))

gen_snd :: G (PAIR a b) -> G b
gen_snd = wrap1_simple gen_snd_worker
gen_snd_worker gen_a t =
	fresh `bind` \x->
	app TSnd (wrapt gen_a (SPair x t))

gen_inls :: G a -> G (SUM a b)
gen_inls = wrap1_simple gen_inls_worker
gen_inls_worker gen_a t =
	fresh `bind` \x->
	unify t (SInl x) `andThen`
	gen_a x

gen_inrs :: G a -> G (SUM b a)
gen_inrs = wrap1_simple gen_inrs_worker
gen_inrs_worker gen_a t =
	fresh `bind` \x->
	unify t (SInr x) `andThen`
	gen_a x

gen_cases :: G (SUM a b) -> String -> G c -> String -> G c -> G c
gen_cases (ggen_u) a (ggen_v) b (ggen_w) =
	wrap3 gen_cases_worker ggen_u ggen_v ggen_w
  where gen_cases_worker gen_u gen_v gen_w g =
	fresh `bind` \x->
	gen_u g x `bind` \u'->
	demon x (\x'-> case x' of
	  SInl y -> gen_v ((a,(y,u')):g) t
	  SInr y -> gen_w ((b,(y,u')):g) t
	  _ -> fail ("CaseS demon invoked on "++show x'++" in:\n"++
               "(CaseS u a v b w)"))

gen_inld :: G a -> G (DSUM a b)
gen_inld = wrap1_simple gen_inld_worker
gen_inld_worker gen_a t =
	fresh2 `bind` \(x,y)->
	unify t (SSum x y) `andThen`
	app TInl (wrapt gen_a x)

gen_inrd :: G a -> G (DSUM b a)
gen_inrd = wrap1_simple gen_inld_worker
gen_inrd_worker gen_a t =
	fresh2 `bind` \(x,y)->
	unify t (SSum x y) `andThen`
	app TInr (wrapt gen_a y)

gen_cased :: G (DSUM a b) -> String -> G c -> String -> G c -> G c
gen_cased (ggen_u) a (ggen_v) b (ggen_w) =
	wrap3 gen_cased_worker ggen_u ggen_v ggen_w
  where gen_cased_worker gen_u gen_v gen_w g =
	fresh2 `bind` \(x,y)->
	tri (\u' (a',v') (b',w')->TCase u' a' v' b' w')
	(wrapt (gen_u g) (SSum x y))
	(rename a $ \a'->unit a' `pair` wrapt (gen_v ((a,(x,TVar a')):g)) t
	(rename b $ \b'->unit b' `pair` wrapt (gen_w ((b,(y,TVar b')):g) w) t)
mix' g (Lam v e) t = fresh2 `bind` \(x,y)->
                     unify t (SFun x y) `andThen`
		     (rename v $ \v'->
	              app (TLam v') 
		        (mix ((v,(x,TVar v')):g) e y))
gen_app :: G (FUN a b) -> G a -> G b
gen_app = wrap2_simple gen_app_worker
gen_app_worker gen_u gen_v t =
	fresh `bind` \x->
	-- making the calls to mix in this order
	-- dramatically improves performance.
	bin (\a b->TApp b a)
	(wrapt gen_v x)
	(wrapt gen_u (SFun x t))
mix' g (Let a u v) t = fresh `bind` \x->
                       bin (\u' (a',v')->TLet a' u' v') 
		         (mix g u x) 
		         (rename a $ \a'->
			  unit a' `pair`
			  mix ((a,(x,TVar a')):g) v t)

gen_ulam :: String -> G b -> G (SFUN a b)
-- but this destroys type checking
gen_ulam :: (G a -> G b) -> G (SFUN a b)
-- but how do I get at the free variables?
-- I can't put them in a list because their G types may be different
-- but I need them to generate the residual code for the static lambda...
mix' g (ULam s e) t =
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

	
wrap3 worker (G gen_a) (G gen_b) (G gen_c) =
	G (worker gen_a gen_b gen_c)
wrap3_simple simple_worker =
	wrap3 (\gen_a gen_b gen_c g ->
		simple_worker (gen_a g) (gen_b g) (gen_c g))

wrap2 worker (G gen_a) (G gen_b) =
	G (worker gen_a gen_b)
wrap2_simple simple_worker =
	wrap2 (\gen_a gen_b g -> simple_worker (gen_a g) (gen_b g))

wrap1 worker (G gen_a) =
	G (worker gen_a)
wrap1_simple simple_worker =
	wrap1 (\gen_a g -> simple_worker (gen_a g))

wrapt m t = app (\x->(x,t)) (m t)


