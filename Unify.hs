module Unify where
import Types
import FMap
import Monad
import List
import ShowType

-- unification of static values; graph unification
-- not a particularly good graph unification because we only
-- remember seeing unification tasks on path from the root.

unify x y = unify' [] x y

unify' seen x y = indirect x `bind` \x'->
                  indirect y `bind` \y'->
		  case (x',y') of
		    (SVar x'',SVar y'')->
		      if x''==y'' then unit () else
		      if x''<y'' then setvar y'' x' else
		      setvar x'' y'
		    (SVar x'',_)->setvar x'' y'
		    (_,SVar y'')->setvar y'' x'
		    (_,_)-> 
		      if (x',y')`elem`seen then unit ()
		      else unify'' ((x',y'):seen) x' y'

unify'' seen (SInl x) (SInl y) = unify' seen x y
unify'' seen (SInr x) (SInr y) = unify' seen x y
unify'' seen (STag s x) (STag t y) | s==t = unify' seen x y
unify'' seen x@(STagD _ _ _) y@(STagD _ _ _) = acunify seen x y
unify'' seen (SPair x y) (SPair x' y') = 
  unify' seen x x' `andThen` unify' seen y y'
unify'' seen (SSum x y) (SSum x' y') = 
  unify' seen x x' `andThen` unify' seen y y'
unify'' seen (SFun x y) (SFun x' y') = 
  unify' seen x x' `andThen` unify' seen y y'
unify'' seen SVoid SVoid = unit ()
unify'' seen (SInt n) (SInt n') | n==n' = unit ()
unify'' seen SIntD SIntD = unit ()
unify'' seen (SBool b) (SBool b') | b==b' = unit ()
unify'' seen SBoolD SBoolD = unit ()
unify'' seen (SStr s) (SStr s') | s==s' = unit ()
unify'' seen SStrD SStrD = unit ()
unify'' seen (SClos ns ss x e) (SClos ns' ss' x' e') 
  | x==x' && e==e' && ns==ns'
  = foldr andThen (unit ())
      [unify' seen z z' | (z,z')<-zip ss ss']
unify'' seen (SFix f ns ss x e) (SFix f' ns' ss' x' e')
  | f==f' && x==x' && e==e' && ns==ns'
  = foldr andThen (unit ())
      [unify' seen z z' | (z,z')<-zip ss ss']
unify'' seen (SSet s x) (SSet t y) =
  setunite (SSet s x) (SSet t y)
unify'' seen (SIn s) (SIn t) =
  unify' seen s t
unify'' seen (SPoly s) (SPoly t) =
  unify' seen s t
unify'' seen (SMonad s) (SMonad t) =
  unify' seen s t
unify'' seen (SRef s) (SRef t) = 
  unify' seen s t
unify'' seen (SStore m s) (SStore n t) 
  | m == n
  = unify' seen s t
unify'' seen x y = 
  showtype x `bind` \xt->
  showtype y `bind` \yt->
  failM ("Cannot unify:\n"++xt++"\nwith\n"++yt)

acunify seen x y =
  gettags x `bind` \(csx,vx) ->
  gettags y `bind` \(csy,vy) ->
  fresh `bind` \v->
  setvar vx 
    (retag [(c,yi) | (c,yi)<-csy, not(c`elem`map fst csx)] v) `andThen`
  (if vx/=vy then setvar vy 
    (retag [(c,xi) | (c,xi)<-csx, not(c`elem`map fst csy)] v)
   else unit ()) `andThen`
  foldr andThen (unit ())
    [unify' seen xi yi | (c,xi)<-csx, (c',yi)<-csy, c==c'] 

gettags (SVar v) = unit ([],v)
gettags (STagD s u v) =
  indirect v `bind` \v'->
  gettags v' `bind` \(ts,w) ->
  unit ((s,u):ts,w)

retag cs v = foldr (\(c,u) w->STagD c u w) v cs

{-subst env u = case u of
  SVar n -> if n `elem` dom env then subst env (assoc env n)
            else SVar n
  SInl x -> SInl (subst env x)
  SInr y -> SInr (subst env y)
  STag s x -> STag s (subst env x)
  SPair x y-> SPair (subst env x) (subst env y)
  SSum x y-> SSum (subst env x) (subst env y)
  SFun x y-> SFun (subst env x) (subst env y)
  SVoid -> SVoid
  SInt n -> SInt n
  SIntD -> SIntD
  SClos ns ss x e -> SClos ns (map (subst env) ss) x e
  SFix f ns ss x e -> SFix f ns (map (subst env) ss) x e
-}

-- some useful fns for error checking

expectSInt s es f x = case x of
  SInt n -> f n
  _ -> expectError s es "SInt n" x

expectSPair s es f x = case x of
  SPair a b -> f a b
  _ -> expectError s es "SPair x y" x

expectSFun s es f x = case x of
  SFun a b -> f a b
  _ -> expectError s es "SFun x y" x

expectSMonad s es f x = case x of
  SMonad a -> f a
  _ -> expectError s es "SMonad a" x

expectSRef s es f x = case x of
  SRef a -> f a
  _ -> expectError s es "SRef a" x

expectError s es p x = 
  error ("No match in "++s++":\n"++show x++" found where "++
              "("++p++") expected\n"++show es)

-- Polyvariance requires an implementation of INDEXED SETS.
-- Sets are created with 
--   singleton x
-- and can be united with
--   setunite x t
-- Each element is assigned an index, and elements can be
-- processed in index order using mapSet.

-- a set
--    SSet s x
-- where s is a tree of elements, and x is a static variable,
-- represents a set containing at least s elements. If x is
-- instantiated to Void, this is all the set contains. Otherwise
-- x is eventually instantiated to a LARGER set, which this one
-- is equal to. 
--
-- Thus sets can always be extended until the final variable 
-- becomes Void. At this point indices can be assigned to the
-- elements.
--
-- Uninstantiated set variables are set to Void by demons waiting
-- on variable completesets; they are run *before* other
-- variables are voided. 

singleton x = fresh2 `bind` \(set,inx)->
              let s = SSet (Elem x inx) set in
	      indexdemon s `andThen` 
	      completiondemon set `andThen`
	      unit (s,inx)

setunite x y =
  indset x `bind` \s@(SSet _ (SVar x'))->
  indset y `bind` \t@(SSet _ (SVar y'))->
  if x'==y' then unit ()   -- because set ids are unique
  else (fresh `bind` \z->
        let new = SSet (Union s t) z in
	setvar x' new `andThen` 
        setvar y' new `andThen`
        indexdemon new `andThen` 
        completiondemon z)

indset set@(SSet s (SVar x)) =
  getvar x `bind` \x'->case x' of
    Yes x'' -> indset x''
    No _ -> unit set

completiondemon (SVar x) =
  demon completesets (\_ ->
  getvar x `bind` \x'->case x' of
    Yes _ -> unit TVoid
    No _ -> setvar x SVoid `andThen` unit TVoid) `andThen`
  unit ()

completesets = SVar 0 -- preallocated

indexdemon (SSet s x) =
  demon x (\s'->
    case s' of
      SVoid -> assignindexes 0 [s] `andThen` unit TVoid
      _ -> unit TVoid)
  `andThen` unit ()

assignindexes k [] = unit ()
assignindexes k (Elem x (SVar i):xis) =
  getvar i `bind` \i'->case i' of
    Yes _ -> -- already has an index
             assignindexes k xis
    No _ -> setvar i (SInt k) `andThen`
            assignindexes (k+1) xis
assignindexes k (Union (SSet x _) (SSet y _):z) =
  assignindexes k (x:y:z)

-- mapSet f s k calls f ONCE for each set element, after comparing
-- elements by unification. Because calling f may itself
-- instantiate elements further, we only unify elements when one
-- has already been passed to f. The results are formed into a 
-- list in index order, which is finally passed to the 
-- continuation k.

mapSet f (SSet els s) k = mapS [els] s [] []
  where mapS (Union (SSet es _) (SSet es' _):q) s seen vals =
          mapS (es:es':q) s seen vals
        mapS (Elem x (SVar i):q) s seen vals =
          -- if i is bound, then this element is the same as
	  -- another and can be ignored.
	  getvar i `bind` \i'->case i' of
	    Yes _ -> mapS q s seen vals
	    No _ ->
	      -- try to unify (x,i) with previously seen els.
	      -- if that fails, apply f.
	      foldr orelse 
	        (f x `bind` \val->
		 mapS q s ((x,i):seen) ((val,SVar i):vals))
	        [indirect (SVar j) `bind` \j'-> 
		 setvar i j' `andThen` unify x y `andThen`
		 mapS q s seen vals
		|(y,j)<-seen]
        mapS [] s seen vals =
	  demon s $ \s'->case s' of
	    SSet (Union (SSet l lv) (SSet r rv)) sv ->
	      -- set has more elements. by comparing backpointers
	      -- we avoid repeating the ones we already did.
	      if s==lv then mapS [r] sv seen vals
	      else mapS [l] sv seen vals
	    SVoid ->
	      -- no more elements. read indices, sort, call
	      -- continuation.
              wrapup vals []

	wrapup [] ws =
	  k (sort ws)
	wrapup ((v,i):vals) ws =
	  demon i (\(SInt i')-> wrapup vals ((v,i'):ws))

        sort [] = []
	sort ((v,i):ws) = 
	  let (lo,hi) = partition (\(w,j)->j<i) ws in
	    sort lo++[v]++sort hi

-- setElements can only be used AFTER sets have been completed, i.e.
-- during arity raising.

setElements (SSet els s) = 
  indirect s `bind` \s'-> case s' of
    SVar _ -> failM "setElements: incomplete set encountered"
    SVoid  -> getels els `bind` \els'->
              unit (order els')
    _ -> setElements s'
  where getels (Elem x i) = indirect i `bind` \(SInt i')-> unit [(x,i')]
        getels (Union (SSet s _) (SSet t _)) = bin (++) (getels s) (getels t)

	-- order and remove duplicate indices.
        order [] = []
	order ((x,i):xis) = order (filter (\(y,j)->j<i) xis) ++ [x] ++
	                    order (filter (\(y,j)->j>i) xis)
