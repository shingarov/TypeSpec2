-- Parsing library in Haskell
--
-- This version produces good error messages and fixes a long-time space leak

module Parselib3 where
import Char
--import Seq

infixl 8 `apP`, `doP`, `bindP`
infixr 6 `consP`, `pairP`
infix  5 `opt`
infix  4 `as`
infixr 2 `orelse`

-- positions
data Position = NoPos | Pos Int Int String | EndofFile deriving (Eq,Ord,Show)
addPositions xs = [(Pos i j l,c) | (l,i)<-zip (lines xs) [1..],
                                   let l'=tabs 0 l,
                                   (c,j)<-zip (l'++"\n") [1..length l'+1]]
			 -- take the opportunity to force l
  where tabs k [] = []
        tabs k ('\t':cs) | k`mod`8==7 = ' ':tabs(k+1) cs
	                 | otherwise  = ' ':tabs(k+1) ('\t':cs)
	tabs k (c:cs) = c:tabs(k+1)cs
displayPos EndofFile = "end of file\n"
displayPos (Pos i j l) =
    "on line "++show i++":\n"++
    l++"\n"++
    [if c=='\t' then '\t' else ' ' | c<-take (j-1) l]++"^\n" 
displayPos NoPos = "at unknown position\n"

column (Pos i j l) = j
column EndofFile = 0

-- the parsing monad -- keeps track of high water mark

newtype Parser t a = P ([(Position,t)] -> Result t a)
newtype Result t a = 
  R (Position->(Position,Maybe (a,[(Position,t)],Maybe(Result t a))))
-- a result maps the high-water mark so far, to
--   a high water mark including the next attempt at parsing
--   Maybe indicating whether or not a parse was found
--   value and remaining input
--   Maybe indicating whether or not more parses *might* be found, permitting
--   more space efficient code in the deterministic case.
unParser (P p) = p
unR (R x) = x

pos [] = EndofFile
pos ((p,_):_) = p

unitP x = P (\ts->R$ \p->(p,Just(x,ts,Nothing)))
P p `bindP` f = P$ \ts->after (p ts) f
  where after (R r) f = R$ \h->
          case r h of
	    (h',Nothing) -> (h',Nothing)
	    (h',Just(x,ts',Nothing)) -> unR (unParser (f x) ts') h'
	    (h',Just(x,ts',Just r')) ->
	      unR (unParser (f x) ts' `orelseR` after r' f) h'
          
      
-- primitives that depend on the monad
failP = P (\ts->failR)
failR = R(\h->(h,Nothing))

P f `orelse` P g = P$ \ts->f ts`orelseR`g ts
R f `orelseR` R g = R$ \h->
  case f h of
    (h',Nothing) -> g h'
    (h',Just(x,ts',Nothing)) -> (h',Just(x,ts',Just (R g)))
    (h',Just(x,ts',Just r)) -> (h',Just(x,ts',Just(r `orelseR` (R g))))

P f `opt` x = P$ \ts->R$ \h->
  case unR (f ts) h of
    (h',Nothing) -> (h',Just(x,ts,Nothing))
    (h',Just(y,ts',_)) -> (h',Just(y,ts',Nothing))

token = P$ \ts -> 
  case ts of
    (p,t):ts' -> R$ \h->(h,Just(t,ts',Nothing))
    [] -> R$ \h->(h,Nothing)

eof = P$ \ts ->
  case ts of
    t:ts' -> failR
    [] -> R$ \h->(h,Just((),[],Nothing))

position = P$ \ts ->R$ \h->(h,let p=pos ts in seq p$Just(p,ts,Nothing))

hwm p = P$ \ts-> R$ \h-> let h'=max h p in seq h'$(h',Just((),ts,Nothing))
highwater = position `bindP` hwm

reparse (P f) ss = P$ \ts->rep (f ss) ts
  where rep (R r) ts = R$ \h->
	  case r h of
	    (h',Nothing) ->fixh ts h' Nothing
	    (h',Just(x,ss',Nothing)) -> 
	      fixh ts h' (Just (x,ss'++ts,Nothing))
	    (h',Just(x,ss',Just r')) ->
	      fixh ts h' (Just (x,ss'++ts,Just (rep r' ts)))
        fixh ts h z = let h'=if h==EndofFile then pos ts else h in
	                seq h' (h',z)

-- operations useful in any monad
mapP f x = x `bindP` \v -> unitP (f v)
binP op x y = x `bindP` \v ->
              y `bindP` \w ->
              unitP (v `op` w)
apP = binP (\f x -> f x)
doP = binP const
consP = binP (:)
pairP = binP (\x y->(x,y))

-- low-level parsing primitives
satisfy p = token `bindP` \tok -> if p tok
                                  then highwater `bindP` \_ -> unitP tok
				  else failP
literal t = satisfy (==t)

-- parsing combinators
many p = some p `opt` []
some p = p `consP` many p
lassoc op e = e `bindP` \v ->
              many (op `pairP` e) `bindP` \opws ->
	      unitP (strictfoldl (\u (oper,w)->u `oper` w) v opws)
rassoc op e = e `bindP` \v ->
              (op `apP` unitP v `apP` rassoc op e) `opt` v
noassoc op e = e `bindP` \v ->
               (op `apP` unitP v `apP` e) `opt` v
offside e = position `bindP` \p ->
            many (position `bindP` \q ->
	          if column p<=column q then 
		    token `bindP` \t -> unitP (q,t)
		  else
		    failP) `bindP` \inp ->
	    reparse e inp

strictfoldl op z [] = z
strictfoldl op z (x:xs) = 
    let z' = op z x in
    seq z' (strictfoldl op z' xs)

-- combinators for lexical analysis
string s = foldr consP (unitP []) (map literal s)
anyOf f = foldr orelse failP . map f
word = satisfy isAlpha `consP` many (satisfy isAlphanum)
number = some (satisfy isDigit)

-- combinators for a separate lexical analyser
x `as` t = position `bindP` \p -> x `bindP` \v -> unitP (p,(v,t))
data Token = Symbol | Ident | Number | StrTok | WhiteSpace 
             deriving (Eq,Show)
strip t' xs = [(p,(v,t)) | (p,(v,t))<-xs, t/=t']
kind t = token `bindP` \(v,t') -> if t==t' 
                                  then highwater `bindP` \_ -> unitP v 
				  else failP
lit s = literal (s,Symbol)

-- invoking a parser
parse p ts = 
  case unR (unParser (unitP id `doP` highwater `apP` p `doP` eof) ts) NoPos of
    (h,Nothing) -> error ("Syntax error: "++displayPos h)
    (h,Just(x,ts',_)) -> x
