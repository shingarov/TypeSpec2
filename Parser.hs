module Parser where
import Parselib3
import PP
import Types
import Char

{- Grammar we parse:
exp ::= \var.exp | let var=exp in exp 
      | ulet var=exp in exp
      | mlet var=exp in exp -- monadic let
      | case exp of inl var:exp, inr var:exp esac
      | case exp of Inl var:exp, Inr var:exp esac
      | case exp of In var:exp esac
      | case exp of cases | app=app
      | poly exp | \@var.exp | app
app ::= app cls | fst cls | snd cls | inl cls | inr cls |
        Inl cls | Inr cls | tag cls | lift cls | fix cls |
	spec cls | app@cls | ufix cls | In cls | cls 
cls ::= var | (exp,exp) | (exp) | num | void
cases ::= {tag var:exp}*-,

Nonterminals take list of unfoldable variables as parameter.
-}

parseexpr = parse expr . lexer

expr = 
  unitP Lam `doP` key "\\" `apP` kind Id `doP` key "." `apP` expr
  `orelse`
  unitP ULam `doP` key "\\@" `apP` kind Id `doP` key "." `apP` expr
  `orelse`
--  unitP Let `doP` key "let" `apP` kind Id `doP` key "="
--    `apP` expr `doP` key "in" `apP` expr
  unitP (\(f,xs) e1 e2->Let f (xs e1) e2) 
   `doP` key "let" `apP` lhs `doP` key "=" `apP` expr `doP` key "in" `apP` expr
  `orelse`
  unitP (\(f,xs) e1 e2->Let f (Fix (Lam f (xs e1))) e2)
   `doP` key "letrec" `apP` lhs `doP` key "=" `apP` expr `doP` key "in" `apP` expr
  `orelse`
--  unitP ULet `doP` key "ulet" `apP` kind Id `doP` key "="
--    `apP` expr `doP` key "in" `apP` expr
--  `orelse`
--  unitP ULet `doP` key "let" `doP` key "@" `apP` kind Id `doP` key "="
--    `apP` expr `doP` key "in" `apP` expr
--  `orelse`
  unitP (\(f,xs) e1 e2->ULet f (xs e1) e2) 
   `doP` key "let" `doP` key "@" `apP` lhs `doP` key "=" `apP` expr `doP` key "in" `apP` expr
  `orelse`
  unitP (\(f,xs) e1 e2->ULet f (UFix (ULam f (xs e1))) e2)
   `doP` key "letrec" `doP` key "@" `apP` lhs `doP` key "=" `apP` expr `doP` key "in" `apP` expr
  `orelse`
--  unitP MLet `doP` key "mlet" `apP` kind Id `doP` key "=" -- Monadic Let
--    `apP` expr `doP` key "in" `apP` expr
--  `orelse`    
  unitP (\x f->f x) `doP` key "case" `apP` expr `doP` key "of"
        `apP` cases True `doP` key "esac"
  `orelse`
  unitP (\x f->f x) `doP` key "case" `doP` key "@" `apP` expr `doP` key "of"
        `apP` cases False `doP` key "esac"
  `orelse`
  unitP IfS `doP` key "if" `doP` key "@" `apP` expr `doP` key "then"
    `apP` expr `doP` key "else" `apP` expr
  `orelse`
  unitP IfD `doP` key "if" `apP` expr `doP` key "then"
    `apP` expr `doP` key "else" `apP` expr
  `orelse`
  unitP Poly `doP` key "poly" `apP` expr
  `orelse`
-- Monadic features
--  unitP RefS `doP` key "ref" `doP` key "@" `apP` closed
--  `orelse`
--  unitP DerefS `doP` key "!@" `apP` appl
--  `orelse`
--  unitP DerefD `doP` key "!" `apP` appl
--  `orelse`
--  unitP Prompt `doP` key "#" `apP` appl
--  `orelse`
-- End Monadic Features 
--  noassoc (unitP AssignS `doP` key ":=@" 
--	   `orelse`
--	   unitP AssignD `doP` key ":=")
    (noassoc (unitP EqS `doP` key "=" `doP` key "@"
              `orelse`
	      unitP EqD `doP` key "=")
      (lassoc (arith ["+","-"])
         (lassoc (arith ["*","/"])
	  appl)))

arith ops = 
  unitP ArithS `apP` anyOf key ops `doP` key "@"
  `orelse`
  unitP ArithD `apP` anyOf key ops

lhs = unitP mklhs
      `apP` (unitP Poly `doP` key "poly" `orelse` unitP id) 
      `apP` kind Id
      `apP` many ((unitP ULam `doP` key "@" `orelse` unitP Lam) `apP` kind Id)
  where mklhs p f xs = (f, \e -> p (foldr (.) id xs e))

appl =
    (prims 
       [("fst",Fst),("snd",Snd),("inl",InlS),("inr",InrS),
        ("Inl",InlD),("Inr",InrD),("lift",Lift),("fix",Fix),
	("spec",Spec),("ufix",UFix),("In",InD),
	("unit",Unit),("ref",RefD)]
     `orelse`
     unitP TagS `apP` kind TagId `doP` key "@" 
       `apP` (unitP tagargs `apP` many closed)
     `orelse`
     unitP TagD `apP` kind TagId `apP` (unitP tagargs `apP` many closed)
     `orelse`
       lassoc' (unitP UApp `doP` key "@"
                `orelse` unitP App)
               closed)
  where tagargs [] = Void
        tagargs es = foldr1 Pair es

lassoc' op e = e `bindP` \v ->
               many (op `pairP` e) `bindP` \opws ->
	       unitP (foldl (\u (oper,w)->u `oper` w) v opws)

prims ps = unitP appargs `apP`
           foldr1 orelse [unitP f `doP` key k `apP` closed
                         | (k,f)<-ps] `apP`
           many ((unitP UApp `doP` key "@" `orelse` unitP App)
                 `pairP` closed)
  where appargs = foldl (\e1 (op,e2) -> e1 `op` e2)

closed = 
  unitP Var `apP` kind Id
  `orelse`
  unitP (\x->TagS x Void) `apP` kind TagId `doP` key "@"
  `orelse`
  unitP (\x->TagD x Void) `apP` kind TagId
  `orelse`
  unitP IntS `apP` (unitP read `apP` kind Numeral)
  `orelse`
  unitP StrS `apP` kind StringConst
  `orelse`
  unitP Void `doP` key "void"
  `orelse`
  unitP (BoolS True) `doP` key "true"
  `orelse`
  unitP (BoolS False) `doP` key "false"
  `orelse`
  unitP (\x f->f x) `doP` key "(" `apP` expr
    `apP` (unitP (\y x->Pair x y) `doP` key ","
             `apP` expr `doP` key ")"
           `orelse`
	   unitP id `doP` key ")")

cases d =
--  (if d then failP else 
--   unitP (\(_,(a,u)) (_,(b,v)) e->CaseS e a u b v)
--    `apP` onecase (key "inl") `doP` key "," 
--    `apP` onecase (key "inr"))
--  `orelse`
--  (if not d then failP else
--   unitP (\(_,(a,u)) (_,(b,v)) e->CaseD e a u b v)
--    `apP` onecase (key "Inl")`doP` key"," 
--    `apP` onecase (key "Inr"))
--  `orelse`
  unitP (\cs e->(if d then CaseTagD else CaseTagS) e cs) 
    `apP` (onecase (kind TagId) `sepby` key ",")
  `orelse`
  (if not d then failP else 
   unitP (\(_,(a,u)) e -> CaseInD e a u)
    `apP` onecase (key "In"))
  
onecase t = t `pairP` 
            (unitP mkbranch `apP` many (kind Id) `doP` key ":" `apP` expr)

mkbranch [] e = ("_", e)
mkbranch [x] e = (x, e)
mkbranch xs e = 
  let n = concat xs in
    (n, rebind xs (Var n) e)
  where rebind [x] e1 e2 = ULet x e1 e2
        rebind (x:xs) e1 e2 = ULet x (Fst e1) (rebind xs (Snd e1) e2)

p `sepby` s = 
  (consP p (many (unitP id `doP` s `apP` p))) `opt` []

data Tok = Sym | Id | TagId | Numeral | StringConst | White deriving Eq
lexer = strip White .parse (many tok).addPositions
tok   = (string "--" `doP` skipto (literal '\n')) `as` White
	`orelse`
	anyOf string (["+","-","*","/",":=@","!@",":=","#",".",
	               "!","=",":",",","\\@","@","\\","(",")"])
          `as` Sym
        `orelse`
	(word `bindP` \w->
	 if w `elem` keywords then unitP w `as` Sym
	 else if isUpper (head w) then unitP w `as` TagId
	 else unitP w `as` Id)
	`orelse`
	number `as` Numeral
	`orelse`
	unitP id `doP` literal '"' `apP` 
	  many (satisfy (/='"')) `doP` literal '"' `as` StringConst
	`orelse`
	some (satisfy isSpace) `as` White
	`orelse`
	(string "{-" `doP` skipto (string "-}")) `as` White

keywords = words (
  "let in case of esac poly fst snd lift fix ufix unit ref mlet"
  ++" spec void ulet delay force In if then else true false letrec")
  -- deleted keywords: inl, inr, Inl, Inr (now obsolete)
key s = unitP fst `apP` literal (s,Sym)

skipto p = p `orelse` (unitP id `doP` token `apP` skipto p)

prettyprint e = pretty 80 60 (ppexpr e)

ppexpr (Lam x e) = text ("\\"++x++".") <> ppexpr e
ppexpr (ULam x e) = text ("\\@"++x++".") <> ppexpr e
--ppexpr (Let x e1 e2) = sep [text ("let "++x++" = ")<>ppexpr e1,
--                            text "in "<>ppexpr e2]
ppexpr (Let x (Fix (Lam y e1)) e2) | x==y =
  sep [text"letrec "<>ppdef (text x) e1,
       text"in "<>ppexpr e2]
ppexpr (Lets xes e2) = 
  sep [text"let "<>foldr1 ($$) [ppdef (text x) e | (x,e)<-xes],
       text"in "<>ppexpr e2]
ppexpr (Letrecs xes e2) = 
  sep [text"letrec "<>foldr1 ($$) [ppdef (text x) e | (x,e)<-xes],
       text"in "<>ppexpr e2]
ppexpr (Let x e1 e2) = sep [text"let "<>ppdef (text x) e1,
                            text"in "<>ppexpr e2]
ppexpr (ULet x e1 e2) = sep [text"let@ "<>ppdef (text x) e1,
                            text"in "<>ppexpr e2]
--ppexpr (ULet x e1 e2) = sep [text ("ulet "++x++" = ")<>ppexpr e1,
--                            text "in "<>ppexpr e2]
ppexpr (MLet x e1 e2) = sep [text ("mlet "++x++" = ")<>ppexpr e1,
                            text "in "<>ppexpr e2]
ppexpr (CaseD e1 a e2 b e3) = 
  sep [text "case "<>sep[ppexpr e1,nest (-5) (text "of")],
       nest 2 (ppc "Inl" a e2)<>text",", nest 2 (ppc "Inr" b e3), text"esac"]
ppexpr (CaseS e1 a e2 b e3) = 
  sep [text "case@ "<>sep[ppexpr e1,nest (-5) (text "of")],
       nest 2 (ppc "inl" a e2)<>text",", nest 2 (ppc "inr" b e3)]
ppexpr (CaseN e u es) =
  sep (text "case "<>sep [ppexpr e, nest (-5) (text "of")]:
       if null es then [text"esac"] else
         ([nest 2 (ppc ("In"++show i) u e)<>text ","
          | (i,e)<-zip [0..length es-2] es]++
	  [nest 2 (ppc ("In"++show (length es-1)) u (last es)),text"esac"]))
ppexpr (CaseInD e1 s e2) =
  sep [text "case "<>sep[ppexpr e1,nest (-5) (text "of")],
       nest 2 (ppc "In" s e2),
       text "esac"]
ppexpr (CaseTagD e1 cs) =
  sep ((text "case "<>sep[ppexpr e1,nest (-5) (text "of")]):
       [nest 2 (ppc c x e)<>text"," | (c,(x,e))<-init cs]++
       [let (c,(x,e)) = last cs in nest 2 (ppc c x e),
        text "esac"])
ppexpr (CaseTagS e1 cs) =
  sep ((text "case@ "<>sep[ppexpr e1,nest (-5) (text "of")]):
       [nest 2 (ppc c x e)<>text"," | (c,(x,e))<-init cs]++
       [let (c,(x,e)) = last cs in nest 2 (ppc c x e),
        text "esac"])
ppexpr (CaseTags e1 cs) =
  sep ((text "case "<>sep[ppexpr e1, nest (-5) (text "of")]):
       [nest 2 (ppc c (unwords xs) e)<>text"," | (c,(xs,e))<-init cs]++
       [let (c,(xs,e)) = last cs in nest 2 (ppc c (unwords xs) e),
        text "esac"])
ppexpr (IfS e1 e2 e3) = 
  sep[text"if@ "<>ppexpr e1,
      nest 2 (text"then "<>ppexpr e2),
      nest 2 (text"else "<>ppexpr e3)]
ppexpr (IfD e1 e2 e3) = 
  sep[text"if "<>ppexpr e1,
      nest 2 (text"then "<>ppexpr e2),
      nest 2 (text"else "<>ppexpr e3)]

ppexpr (ArithD op e e') = sep [ppappl e, text (op++" ")<>ppappl e']
ppexpr (ArithS op e e') = sep [ppappl e, text (op++"@ ")<>ppappl e']
ppexpr (EqS e e') = ppop "=@" e e'
ppexpr (EqD e e') = ppop "=" e e'
ppexpr e = ppappl e

ppdef lhs (Poly e) = ppdef' (text "poly "<>lhs) e
ppdef lhs e = ppdef' lhs e

ppdef' lhs (Lam x e) = ppdef' (lhs<>text(" "++x)) e
ppdef' lhs (ULam x e) = ppdef' (lhs<>text("@"++x)) e
ppdef' lhs e = sep [lhs<>text " =", nest 2 (ppexpr e)]
        
ppop op e e' = sep [ppappl e, text (op++" ")<>ppappl e']

ppc s x e = text (s++" "++x++": ")<>ppexpr e

ppappl (App e1 e2) = sep [ppappl e1, nest 2 (ppclosed e2)]
ppappl (UApp e1 e2) = sep [ppappl e1<>text"@", 
                           nest 2 (ppclosed e2)]
ppappl (Fst e) = pppr "fst" e
ppappl (Snd e) = pppr "snd" e
ppappl (InlD e) = pppr "Inl" e
ppappl (InrD e) = pppr "Inr" e
ppappl (InlS e) = pppr "inl" e
ppappl (InrS e) = pppr "inr" e
ppappl (Lift e) = pppr "lift" e
ppappl (Poly e) = pppr "poly" e
ppappl (Spec e) = pppr "spec" e
ppappl (InD e) = pppr "In" e
ppappl (Fix e) = pppr "fix" e
ppappl (UFix e) = pppr "ufix" e
ppappl (Error s) = sep [text "error", 
                        nest 2 (text ("\""++s++"\""))]
ppappl (InN k e) = pppr ("In"++show k) e
ppappl (TagD c e) = pppr c e
ppappl (TagS c e) = pppr (c++"@") e
ppappl (Tags s es) | not (null es) = text (s++" ")<>sep(map ppclosed es)
-- Monadic Features
ppappl (Unit e) = pppr "unit" e
ppappl (RefS e) = pppr "ref@" e
ppappl (RefD e) = pppr "ref" e
ppappl (DerefS e) = pppr "!@" e
ppappl (DerefD e) = pppr "!" e
ppappl (Prompt e) = pppr "#" e
ppappl (AssignS e1 e2) = sep [ppappl e1<>text ":=@",ppappl e2]
ppappl (AssignD e1 e2) = sep [ppappl e1<>text ":=", ppappl e2]
ppappl e = ppclosed e

pppr s e = sep [text s, nest 2 (ppclosed e)]

ppclosed (Var s) = text s
ppclosed (IntD n) = text (show n)
ppclosed (StrD s) = text (show s)
ppclosed (BoolD s) = text (show s)
ppclosed (IntS n) = text (show n++"@")
ppclosed (StrS s) = text (show s++"@")
ppclosed (BoolS n) = text (show n++"@")
ppclosed Void = text "void"
ppclosed (Pair e1 e2) = text "("<>sep[ppexpr e1<>text",",
                                      ppexpr e2]<>text")"
ppclosed (Tags s []) = text s
ppclosed e = text "("<>ppexpr e<>text ")"
