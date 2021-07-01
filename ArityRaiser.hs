-- After specialisation, we arity raise by transforming expressions and bound
-- variables of static pair type to a sequence of such. This is a
-- generalisation of void erasure. It requires the introduction of some new
-- syntax to express the result, such as n-ary let and letrec.
--
-- This pass also resolves forward references.

module ArityRaiser(arityraise) where
import Types
import FMap
import Monad
import Unify
import Freevars
import ShowType

arityraise t = mapvars (\w->
		       getvar w `bind` \z->case z of
			 Yes _ -> unit ()
			 No _ -> setvar w SVoid) `andThen`
	       araise t `bind` \ts->
	       case ts of
	         [] -> unit Void
		 _ -> unit (foldr1 Pair ts)
		 

araise (term, t) = representation t `bind` \r->
                   if null r then unit [] else araise' term r

araise' term r = case term of
  TVar s -> unit (map Var (raisevar s r))
  TApp u v -> araise u `bind` \us->
              araise v `bind` \vs->
	      unit [foldl App u' vs | u'<-us]
  TLam s u -> araise u `bind` \us->
              let (SFun a _:_) = r in
	      representation a `bind` \as->
	      let ss = raisevar s as in
	      unit [foldr Lam u' ss | u'<-us]
  TPair u v-> bin (++) (araise u) (araise v)
  TFst u -> app (take (length r)) (araise u)
  TSnd u -> app (reverse.take (length r).reverse) (araise u)
  TInl u -> app (\us->[Tags "Inl" us]) (araise u)
  TInr u -> app (\us->[Tags "Inr" us]) (araise u)
--TCase, now obsolete
  TTag s u -> app (\us->[Tags s us]) (araise u)
  TCaseTag u cs ->
    araise u `bind` \[u']->
    foldr (bin (:)) (unit [])
      [ araise e `bind` \es->
        representation t `bind` \r->
	let xs = raisevar x r in
	unit [(c,(xs,e')) | e'<-es]
      | (c,(x,t,e))<-cs] `bind` \css->
    unit [CaseTags u' cases | cases<-foldr (zipWith (:)) (repeat []) css]
  TIf e1 e2 e3-> araise e1 `bind` \[b]->
                 araise e2 `bind` \e2s->
		 araise e3 `bind` \e3s->
		 unit [IfD b e2' e3' | (e2',e3')<-zip e2s e3s]
  TInt n -> unit [IntD n]
  TBool n-> unit [BoolD n]
  TStr n -> unit [StrD n]
  TArith op u v -> bin (\[x] [y]->[ArithD op x y]) (araise u) (araise v)
  TEq u v -> bin (\[x] [y]->[EqD x y]) (araise u) (araise v)
  TVoid -> unit []
  TFix u -> if length r==1 then
              araise u `bind` \[u']->unit [Fix u']
	    else let rt = foldr SPair SVoid r 
	             (name,u') = 
		       case u of
		         (TLam n _,_) -> (n,u)
			 _ -> ("$rec",
			       (TLam "$rec" 
			             (TApp u (TVar "$rec", rt), rt),
                                SFun rt rt))
                 in
	         araise' (TLet name (TFix u', rt) (TVar name, rt)) r
  TLet a (TFix (TLam b u,_),t) v | a==b -> 
    araise u `bind` \us->
    let as = if length us==1 then [a] else 
               map (((a++"_")++).show) [1..length us] 
        aus = zip as us 
    in
    araise v `bind` \vs->
    if null as then unit vs else
    unit (map (Letrecs aus) vs)
  TLet a u v -> araise u `bind` \us->
                araise v `bind` \vs->
		let as=case us of
		         [_] -> [a]
			 _ -> map (((a++"_")++).show) [1..length us] in
		if null as then unit vs else
		let aus = zip as us in
		unit (map (Lets aus) vs)

  TRef w -> gettvar w `bind` \u-> araise' u r
--TError
  TIn k e -> araise' (TTag ("In"++show k) e) r
  TCaseN e x cs -> 
    araise' (TCaseTag e [("In"++show i,(x,t,c)) | (i,(t,c))<-zip [0..] cs]) r
  TPrj i (e,t) -> indirect t `bind` \(SPoly set) ->
                  setElements set `bind` \els->
		  foldr (bin (:)) (unit []) 
		    (map representation els) `bind` \rs->
		  araise (e,t) `bind` \es->
		  unit (drop (length (concat (take i rs))) 
		             (take (length (concat (take (i+1) rs))) es))
  TTup es -> foldr (bin (++)) (unit []) (map araise es)
--TUnit
--TMLet
--TMkref
--TDeref
--TAssign
  _ -> error ("No match in araise: "++show term++" : "++show r++"\n")

raisevar s [_] = [s]
raisevar s ts = [s++"_"++show i | (i,_)<-zip [1..] ts]

-- representation takes a residual type and returns a list of types of the
-- components of its representation. One point types are transformed to void, 
-- but other type recursions have to be rejected!

representation t = repr [] t
  where repr seen t =
          if t`elem`seen then 
	    showtype (last seen) `bind` \t'->
	    failM ("Arity raiser: type with infinite representation:\n"++t')
	  else let r = repr (t:seen) in
	         indirect t `bind` \t'->
		 onepoint t' `bind` \one->
		 if one then unit [] else
		 case t' of
		   SInl u -> r u
		   SInr u -> r u
		   STag s u -> r u
		   SClos _ ss _ _ -> r (foldr SPair SVoid ss)
		   SFix _ _ ss _ _ -> r (foldr SPair SVoid ss)
		   SStore _ s -> r s
		   SPair u v -> 
		     bin (++) (r u) (r v)
		   SFun u v ->
		     r v `bind` \vs->
		     unit [SFun u v' | v'<-vs]
		   SPoly set ->
		     if set==SVoid then unit [] else
		     setElements set `bind` \ts->
		     foldr (bin (++)) (unit []) (map representation ts)
		   _ -> unit [t']

-- The one point test ALSO needs to handle graphs!
onepoint s = onepoint' [] s

onepoint' seen (SVar w) = if w `elem` seen then unit True else
                          getvar w `bind` \(Yes s)->
                          onepoint' (w:seen) s
onepoint' seen (SInl s) = onepoint' seen s
onepoint' seen (SInr s) = onepoint' seen s
onepoint' seen (STag s x) = onepoint' seen x
onepoint' seen (STagD s x y) = unit False
onepoint' seen (SPair x y) = bin (&&) (onepoint' seen x) 
                                      (onepoint' seen y)
onepoint' seen (SSum x y) = unit False
onepoint' seen (SFun x y) = onepoint' seen y
onepoint' seen SVoid = unit True
onepoint' seen (SInt _) = unit True
onepoint' seen SIntD = unit False
onepoint' seen (SStr _) = unit True
onepoint' seen SStrD = unit False
onepoint' seen (SBool _) = unit True
onepoint' seen SBoolD = unit False
onepoint' seen (SClos _ ss _ _) = foldr (bin (&&)) (unit True)
                                    (map (onepoint' seen) ss)
onepoint' seen (SFix _ _ ss _ _) = foldr (bin (&&)) (unit True)
                                     (map (onepoint' seen) ss)
onepoint' seen (SIn s) = indirect s `bind` \z->unit (s==SVoid)
onepoint' seen (SPoly s) = indirect s `bind` \z->
                           if z==SVoid then unit True else
			   setElements s `bind` \ts->
			   foldr (bin (&&)) (unit True)
			     (map (onepoint' seen) ts)
onepoint' seen (SMonad s) = unit False
onepoint' seen (SRef s) = onepoint' seen s
onepoint' seen (SStore _ s) = onepoint' seen s
