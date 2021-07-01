module ShowType (showstat, showtype) where
import FMap
import Monad
import StatType
import Parser(prettyprint)

showtype t = get varvals `bind` \vs-> unit (showstat vs t)

-- showstat handles graph values
showstat env v = 
  let sv = sharedvars env v
      unfold (SVar w) = if w `elem` sv then SVar w 
                        else case assocT env w of
			       Full z->unfold z
			       Empty _->SVar w
      unfold (SInl s) = SInl (unfold s)
      unfold (SInr s) = SInr (unfold s)
      unfold (STag s x) = STag s (unfold x)
      unfold (STagD s x y) = STagD s (unfold x) (unfold y)
      unfold (SPair x y) = SPair (unfold x) (unfold y)
      unfold (SSum x y) = SSum (unfold x) (unfold y)
      unfold (SFun x y) = SFun (unfold x) (unfold y)
      unfold SVoid = SVoid
      unfold (SInt n) = SInt n
      unfold SIntD = SIntD
      unfold (SStr s) = SStr s
      unfold SStrD = SStrD
      unfold (SBool b) = SBool b
      unfold SBoolD = SBoolD
      unfold (SClos ns ss x e) = SClos ns (map unfold ss) x e
      unfold (SFix f ns ss x e) = SFix f ns (map unfold ss) x e
      unfold (SIn s) = SIn (unfold s)
      unfold (SPoly s) = SPoly (unfold s)
      unfold (SSet s (SVar w)) =
        case assocT env w of
	  Full z@(SSet _ _) -> unfold z
	  Full SVoid -> SSet (unfoldSet s) SVoid
	  Empty _ -> SSet (unfoldSet s) (SVar w)
      unfold (SMonad s) = SMonad (unfold s)
      unfold (SRef s) = SRef (unfold s)
      unfold (SStore n s) = SStore n (unfold s)
      unfoldSet (Elem x i) = Elem (unfold x) (unfold i)
      unfoldSet (Union (SSet x u) (SSet y v)) =
        Union (SSet (unfoldSet x) u) (SSet (unfoldSet y) v)
  in showS (unfold v) ++
     if null sv then "\n" else
     "\nwhere\n"++
     unlines [showS (SVar v)++" = "++
              showS (unfold (let Full z=assocT env v in z))
             | v<-sv]

sharedvars env v = sr [v] [] []
  where sr [] s r = s
        sr (t:ts) s r =
	  case t of
	    SVar w -> if w `elem` s then sr ts s r else
	              if w `elem` r then sr ts (w:s) r else
		      case assocT env w of
		        Full z|nevershare z -> sr (z:ts) s r
		        Full z->sr (z:ts) s (w:r)
			Empty _->sr ts s r
	    SInl t'-> sr (t':ts) s r
	    SInr t'-> sr (t':ts) s r
	    STag _ x -> sr (x:ts) s r
	    STagD _ x y -> sr (x:y:ts) s r
	    SPair x y-> sr (x:y:ts) s r
	    SSum x y-> sr (x:y:ts) s r
	    SFun x y-> sr (x:y:ts) s r
	    SVoid -> sr ts s r
	    SInt n -> sr ts s r
	    SIntD -> sr ts s r
	    SStr n -> sr ts s r
	    SStrD -> sr ts s r
	    SBool n -> sr ts s r
	    SBoolD -> sr ts s r
	    SClos _ ss _ _ -> sr (ss++ts) s r
	    SFix _ _ ss _ _ -> sr (ss++ts) s r
	    SIn t' -> sr (t':ts) s r
	    SPoly t' -> sr (t':ts) s r
	    SSet els (SVar w) ->
	      case assocT env w of
	        Full z->sr (z:ts) s r
		Empty _-> sr (getels els++ts) s r
	    SMonad x -> sr (x:ts) s r
	    SRef x -> sr (x:ts) s r
	    SStore _ x -> sr (x:ts) s r
	getels (Elem x i) = [x]
	getels (Union (SSet x _) (SSet y _)) =
	  getels x++getels y
	nevershare z =
	  case z of
	    SVoid -> True
	    SInt _ -> True
	    SIntD -> True
	    SStr _ -> True
	    SStrD -> True
	    SBool _ -> True
	    SBoolD -> True
	    SPair _ _ -> True
	    -- loops involving pairs will cause the arity raiser to fail...
	    _ -> False

showS (SSum x y) = showS1 x++"+"++showS1 y
showS (SFun x y) = showS1 x++"->"++showS y
showS (STagD s e SVoid) = s++showSTup e
showS (STagD s e f) = s++showSTup e++" | "++showS f
showS (SIn s@(SSet _ (SVar _))) = "In "++showS0 s
showS (SIn SVoid) = "void"
showS (SIn (SSet els _)) = 
  foldr1 (\x y->x++" | "++y) 
    ["In"++show i++showSTup t | (i,t)<-zip [0..] (listels els)]
showS x = showS1 x

showS1 (SInl e) = "inl "++showS0 e
showS1 (SInr e) = "inr "++showS0 e
--showS1 (STag s e) = s++"@ "++showS0 e
--showS1 (STagD s e SVoid) = s++" "++showS0 e
--showS1 (STagD s e f) = s++" "++showS0 e++" | "++showS1 f
showS1 (STag s e) = s++"@"++showSTup e
showS1 (STagD s e SVoid) = s++showSTup e
showS1 (SIn s@(SSet _ (SVar _))) = "In "++showS0 s
showS1 (SIn SVoid) = "void"
showS1 (SPoly s@(SSet _ (SVar _))) = "tuple "++showS0 s
showS1 (SMonad s) = "M "++ showS0 s
showS1 (SRef s) = "ref "++showS0 s
showS1 (SStore n s) = "Store "++show n++" "++showS0 s
showS1 x = showS0 x

showS0 (SVar k) = "_"++show k
showS0 (SPair x y) = "("++showS x++","++showS y++")"
showS0 SVoid = "void"
showS0 (SInt k) = show k
showS0 (SIntD) = "int"
showS0 (SStr k) = show k
showS0 (SStrD) = "string"
showS0 (SBool k) = show k
showS0 (SBoolD) = "bool"
showS0 (SClos ns vs x t) = "clos["++x++","++prettyprint t++","++
                          show ns++","++show(map showS vs)++"]"
showS0 (SFix f ns vs x t) = 
  "rec["++f++","++x++","++prettyprint t++","++
                          show ns++","++show(map showS vs)++"]"
showS0 (SPoly SVoid) = "void"
showS0 (SPoly (SSet els _)) =
  "("++foldr1 (\x y->x++","++y) (map showS (listels els))++")"
showS0 (SSet els _) = "{"++showSet els++"}"
showS0 x = "("++showS x++")"

showSTup (SPair x y) = " "++showS0 x++showSTup y
showSTup SVoid = ""
showSTup x = " "++showS0 x

showSet (Elem x i) = showS i++":"++showS x
showSet (Union (SSet x _) (SSet y _)) = showSet x++","++showSet y

listels (Elem x i) = [x]
listels (Union (SSet x _) (SSet y _)) = listels x++listels y
