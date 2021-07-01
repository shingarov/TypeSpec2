module Freevars where

import TermType

freevars e = case e of
  Var s -> [s]
  App a b -> fv2 a b
  Lam s e -> [v|v<-freevars e, v/=s]
  Let s e1 e2 -> fv2 (Lam s e2) e1
  Pair a b -> fv2 a b
  Fst a -> freevars a
  Snd a -> freevars a
  InlS a -> freevars a
  InrS a -> freevars a
  CaseS x a u b v -> fv2 x (Pair (Lam a u) (Lam b v))
  InlD a -> freevars a
  InrD a -> freevars a
  CaseD x a u b v -> fv2 x (Pair (Lam a u) (Lam b v))
  Fix e -> freevars e
  Lift e -> freevars e
  EqS a b -> fv2 a b
  EqD a b -> fv2 a b
  TagS s e -> freevars e
  TagD s e -> freevars e
  CaseTagS x cs -> fv2 x (foldr Pair Void [Lam i e|(_,(i,e))<-cs])
  CaseTagD x cs -> fv2 x (foldr Pair Void [Lam i e|(_,(i,e))<-cs])
  Poly e -> freevars e
  Spec e -> freevars e
  ULam x e -> freevars (Lam x e)
  UApp a b -> fv2 a b
  UFix a -> freevars a
  ULet x a b -> fv2 a (Lam x b)
  InD e -> freevars e
  CaseInD x a u -> fv2 x (Lam a u)
  Unit e -> freevars e
  MLet x e1 e2 -> fv2 e1 (Lam x e2)
  RefS e -> freevars e
  RefD e -> freevars e
  DerefS e -> freevars e
  DerefD e -> freevars e
  AssignS e1 e2 -> fv2 e1 e2
  AssignD e1 e2 -> fv2 e1 e2
  Prompt e -> freevars e
  ArithD op e1 e2 -> fv2 e1 e2
  ArithS op e1 e2 -> fv2 e1 e2
  IfS e1 e2 e3 -> fv2 e1 (Pair e2 e3)
  IfD e1 e2 e3 -> fv2 e1 (Pair e2 e3)
  _ -> []
 where fv2 a b = let fb = freevars b in
                 [v|v<-freevars a,not(v`elem`fb)]++fb
