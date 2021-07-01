-- Parsing library in Haskell
module Parselib2 where
import Char

infixl 8 `apP`, `doP`, `bindP`
infixr 6 `consP`, `pairP`
infix  5 `opt`
infix  4 `as`
infixr 2 `orelse`

-- positions
data Position = NoPos | Pos Int Int String | EndofFile deriving (Eq,Ord,Show)
addPositions xs = [(Pos i j l,c) | (l,i)<-zip (lines xs) [1..],
                                   (c,j)<-zip (l++"\n") [1..length l+1]]
			 -- take the opportunity to force l
displayPos EndofFile = "end of file\n"
displayPos (Pos i j l) =
    "on line "++show i++":\n"++
    l++"\n"++
    [if c=='\t' then '\t' else ' ' | c<-take (j-1) l]++"^\n" 
displayPos NoPos = "at unknown position\n"

column (Pos i j l) = j
column EndofFile = 0

-- the parsing monad -- keeps track of high water mark
data Parser t a = Parser ([(Position,t)] -> ([(a,[(Position,t)])],Position))
unParser (Parser p) = p

pos [] = EndofFile
pos ((p,_):_) = p

unitP x = Parser (\ts -> ([(x,ts)],NoPos))
Parser p `bindP` f = 
   Parser (\ts ->
   let (ps,hwm) = p ts
       (qss,hwms) = unzip [unParser (f u) ts' | (u,ts')<-ps]
   in (concat qss, foldl max hwm hwms))

-- primitives that depend on the monad
failP = Parser (\ts -> ([],NoPos))
Parser p `orelse` Parser q = Parser (\ts -> 
                             let (ps,hwm) = p ts
			         (qs,hwm') = q ts
			     in (ps++qs,max hwm hwm'))
Parser p `opt` x = Parser (\ts -> let (ps,hwm) = p ts in
                                  ([case ps of
				       [] -> (x,ts)
				       vts:_ -> vts],
				   hwm))
token = Parser (\ts -> case ts of
                          (p,t):ts' -> ([(t,ts')],NoPos)
                          [] -> ([],NoPos))
eof = Parser (\ts -> case ts of
                        t:ts' -> ([],NoPos)
                        [] -> ([((),[])],NoPos))
position = Parser (\ts -> ([(pos ts,ts)],NoPos))
hwm p = Parser (\ts -> ([((),ts)],p))
highwater = position `bindP` hwm

reparse (Parser p) ss = Parser (\ts->
  let (ps,hwm) = p ss in
  ([(u,ss'++ts) | (u,ss')<-ps],hwm))

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
string :: Eq a => [a] -> Parser a [a]
string = foldr consP (unitP []) . map literal
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
parse p ts = case unParser (p `doP` eof) ts of
                         ([],errpos) -> error ("Syntax error: "++
			                       displayPos errpos)
                         ((v,_):_,_) -> v
