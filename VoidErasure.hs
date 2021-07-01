module VoidErasure(eraseVoid) where
import Types
import FMap
import Monad
import Unify
import Freevars

{- After specialisation, we eliminate useless expressions.
   Expressions of a one-point type are replaced by Void.
   Void arguments are dropped, as are Void components of pairs.
   At the same time forward references are resolved, and we
   perform a kind of arity raising: selectors of pairs are
   simplified. IS THIS THE RIGHT PLACE TO DO THIS?
-}

eraseVoid t = mapvars (\w->
		       getvar w `bind` \z->case z of
			 Yes _ -> unit ()
			 No _ -> setvar w SVoid) `andThen`
	      stripVoid t

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
onepoint' seen (SMonad s) = unit False
onepoint' seen (SRef s) = onepoint' seen s
onepoint' seen (SStore _ s) = onepoint' seen s

stripVoid (term,t) = onepoint t `bind` \b->
                     if b then unit Void else stripVoid' term t
stripVoid' (TVar s) t = unit (Var s)
stripVoid' (TApp u v) t = stripVoid u `bind` \u'->
                          stripVoid v `bind` \v'->
			  case v' of
			    Void -> unit u'
			    _ -> unit (mkapp u' v')
stripVoid' (TLam s u) t = residstat t `bind`
                          expectSFun "stripVoid'/TLam" [TLam s u]
			    (\a b->
			     onepoint a `bind` \elim->
			     if elim then stripVoid u
			     else app (lam s) (stripVoid u))
stripVoid' (TPair u v) t = stripVoid u `bind` \u'->
                           stripVoid v `bind` \v'->
			   case u' of
			     Void -> unit v'
			     _ -> case v' of
			            Void -> unit u'
				    _ -> unit (Pair u' v')
stripVoid' (TFst u) t = 
  residstat (snd u) `bind` 
  expectSPair "stripVoid'/TFst" [u] 
    (\a b->
     onepoint b `bind` \elim->
     if elim then stripVoid u 
     else stripVoid u `bind` \u'->case u' of   -- `arity raising'
            Pair x y -> unit x
	    _ -> unit (Fst u'))
stripVoid' (TSnd u) t = 
  residstat (snd u) `bind`
  expectSPair "stripVoid'/TSnd" [u]
    (\a b->
    onepoint a `bind` \elim->
    if elim then stripVoid u 
    else stripVoid u `bind` \u'->case u' of   -- `arity raising'
            Pair x y -> unit y
	    _ -> unit (Snd u'))
stripVoid' (TInl u) t = app InlD (stripVoid u)
stripVoid' (TInr u) t = app InrD (stripVoid u)
stripVoid' (TCase u a v b w) t = 
  tri (\u' v' w'->CaseD u' a v' b w')
    (stripVoid u) (stripVoid v) (stripVoid w)
stripVoid' (TTag s u) t = app (TagD s) (stripVoid u)
stripVoid' (TCaseTag u cs) t = bin CaseTagD (stripVoid u)
                                 (foldr (bin (:)) (unit [])
				    [app (\e'->(c,(x,e')))
				       (stripVoid e)
				    | (c,(x,e))<-cs])
stripVoid' (TIf e1 e2 e3) t = 
  stripVoid e1 `bind` \e1'->
  stripVoid e2 `bind` \e2'->
  stripVoid e3 `bind` \e3'->
  unit (IfD e1' e2' e3')
stripVoid' (TInt n) t = unit (IntD n)
stripVoid' (TBool n) t = unit (BoolD n)
stripVoid' (TStr n) t = unit (StrD n)
stripVoid' (TArith op u v) t = 
  bin (ArithD op) (stripVoid u) (stripVoid v)
stripVoid' (TEq u v) t = bin EqD (stripVoid u) (stripVoid v)
stripVoid' TVoid t = unit Void
stripVoid' (TFix u) t = app Fix (stripVoid u)
stripVoid' (TLet a u v) t = stripVoid u `bind` \u'->
                            stripVoid v `bind` \v'->
			    case u' of
			      Void -> unit v'
			      _ -> unit (llet a u' v')
stripVoid' (TRef w) t = gettvar w `bind` \u->
                        stripVoid' u t
stripVoid' (TError s) t = unit (Error s)
stripVoid' (TIn k e) t = app (InN k) (stripVoid e)
stripVoid' (TCaseN e u cases) t = 
  tri CaseN (stripVoid e) (unit u)
    (foldr (bin (:)) (unit []) (map stripVoid cases))
stripVoid' (TUnit e) t = stripVoid e `bind` \ e' -> unit (Unit e')
stripVoid' (TMLet s u v) t = stripVoid u `bind` \u' ->
                             stripVoid v `bind` \v' ->
			     case u' of 
                               Unit Void -> unit v'
			       _ -> unit (mlet s u' v')
stripVoid' (TMkref e) t = stripVoid e `bind` \e' ->
                          case e' of
			    Void -> unit (Unit Void)
			    _ -> unit (RefD e')
stripVoid' (TDeref e) t = stripVoid e `bind` \e' ->
                          case e' of
			    Void -> unit Void
			    _ -> unit (DerefD e')
stripVoid' (TAssign u v) t = stripVoid u `bind` \u' ->
                             stripVoid v `bind` \v' ->
                             case u' of
			       Void -> unit (Unit Void)
			       _ -> unit (AssignD u' v')
stripVoid' u t = error ("No match in stripVoid' "++show u++" "++
                        show t++"\n")

mlet s (Unit e1) e2 | e1==Var s = e2
                    | otherwise = llet s e1 e2
mlet s (MLet x e1 e2) e3 = MLet x e1 (mlet s e2 e3)
mlet s (Let x e1 e2) e3 = llet x e1 (mlet s e2 e3)
mlet s e1 (Unit (Var x)) | x==s = e1
mlet s e1 e2 = MLet s e1 e2

llet s Void e = e
llet s (Var t) e | s==t = e
llet s e1 e2 = Let s e1 e2

mkapp (Lam x e1) e2 = llet x e2 e1
mkapp e1 e2 = App e1 e2

lam x (App e1 (Var y)) | x==y && not (x `elem` freevars e1) = e1
lam x e = Lam x e

-- residstat takes the static value a resid exp was derived from,
-- and returns a val representing its type.
residstat t = indirect t `bind` \t'-> case t' of
                SInl u -> residstat u
		SInr u -> residstat u
		STag s u -> residstat u
		SClos _ ss _ _ -> 
		  residstat (foldr SPair SVoid ss)
		SFix _ _ ss _ _ -> 
		  residstat (foldr SPair SVoid ss)
		SStore _ s ->
		  residstat s
		_ -> unit t'

