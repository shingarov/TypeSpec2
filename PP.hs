module PP where

infixr $$    -- vertical composition
infixr <>    -- horizontal composition

data Cxt = BestNest Int Int Int     -- best w r (nest k *)
         | TextLeft LString Cxt     -- C[text s <> *]
--	 | Sep [Doc] Cxt            -- C[sep[*,y1...yn]]
         | SepNest Int [Doc] Cxt    -- C[sep[*,nest k y1...nest k yn]]
	 | Fit Cxt                  -- C[fit *]
	 | Beside Doc Cxt           -- C[* <> y]
--	 | Above Doc Cxt            -- C[* $$ y]
         | AboveNest Int Doc Cxt    -- C[* $$ nest k y]
	 
type Doc = Cxt -> Perhaps String -> String
data Perhaps a = Yes a | No
type LString = (Int,String)   -- save the length

(p $$ q) c bt = case c of
  AboveNest k y c' -> (p $$ (q$$nest k y)) c' bt
  Beside y c' -> (p $$ (q<>y)) c' bt
  Fit c' -> case bt of Yes s->s           -- fail and backtrack
  SepNest k ys c' -> (p $$ (q $$ nest k (foldr1 ($$) ys))) c' bt
  _ -> p (AboveNest 0 q c) bt

(p <> q) c bt = p (Beside q c) bt

(nest n p) c bt = case c of
  BestNest w r k -> p (BestNest w r (k+n)) bt
  TextLeft s c' -> p c bt
  SepNest k ys c' -> let k' = k-n in
                     seq k' (nest n (sepNest p k' ys) c' bt)
  Fit c' -> nest n (fit p) c' bt
  Beside y c' -> nest n (p<>y) c' bt
  AboveNest k y c' -> let k' = k-n in
                      seq k' (nest n (aboveNest p k' y) c' bt)
(sepNest p k ys) c bt = p (SepNest k ys c) bt
(aboveNest p k y) c bt = p (AboveNest k y c) bt


(sep []) c bt = error "sep [] is undefined"
(sep [p]) c bt = p c bt
(sep (p:ys)) c bt = p (SepNest 0 ys c) bt

text s = textL (length s,s)
(textL (ls,s)) c bt = case c of
  BestNest w r k -> if nice w r k ls then line k s else
                    case bt of No -> line k s
		               Yes s' -> s'
  TextLeft (lt,t) c' -> textL (ls+lt,t++s) c' bt
  SepNest k ys c' -> let k' = k-ls in
                     seq k' (textBeside (ls,s) (sepNest empty k' ys) c' bt)
  Fit c' -> textL (ls,s) c' bt
  Beside y c' -> textBeside (ls,s) y c' bt
  AboveNest k y c' -> textAboveNest (ls,s) k y c' bt

textBeside (ls,s) y c bt = case c of
  BestNest w r k -> if nice w r k ls then y (TextLeft (ls,s) c) bt
                    else case bt of No -> y (TextLeft (ls,s) c) bt
		                    Yes s' -> s'
  TextLeft (lt,t) c' -> textBeside (lt+ls,t++s) y c' bt
  SepNest k ys c' -> let k' = k-ls in seq k' $
                     textBeside (ls,s) 
                       (sepNest (empty<>y) k' ys)
		       c' bt
  Fit c' -> textBeside (ls,s) (fit y) c' bt
  Beside z c' -> textBeside (ls,s) (y<>z) c' bt
  AboveNest k z c' -> let k' = k-ls in seq k' $
                      textBeside (ls,s) (aboveNest (empty<>y) k' z) c' bt

textAboveNest (ls,s) k' y c bt = case c of
  BestNest w r k -> if nice w r k ls then line k s++nest k' y c No
                    else case bt of No -> line k s++nest k' y c No
		                    Yes s' -> s'
  TextLeft (lt,t) c' -> let k'' = k'+lt in
                        seq k'' (textAboveNest (ls+lt,t++s) k'' y c' bt)
  SepNest k ys c' -> let k'' = k-k' in
                     seq k'' $
		       textAboveNest (ls,s) k' 
                         (y $$ nest k'' (foldr1 ($$) ys)) 
			 c' bt
  Fit c' -> case bt of Yes s' -> s'
  Beside z c' -> textAboveNest (ls,s) k' (y<>z) c' bt
  AboveNest k z c' -> let k'' = k-k' in
                      seq k'' $ textAboveNest (ls,s) k' (y$$nest k'' z) c' bt

empty c bt = case c of
  SepNest k ys c' -> textBeside (1," ") (fit (foldr1 (<+>) ys)) c' 
                     (Yes ((empty $$ nest k (foldr1 ($$) ys)) c' bt))
  Beside y c' -> y (TextLeft (0,"") c') bt
  AboveNest k y c' -> textAboveNest (0,"") k y c' bt

p <+> q = p <> text " " <> q

fit p c bt = p (Fit c) bt

nice w r k ls = ls <= (r `min` ((w-k) `max` 0))

line k s = [' ' | i<-[1..k]]++s++"\n"

pretty w r d = d (BestNest w r 0) No
