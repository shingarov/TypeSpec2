module TwoLevelTypes where

data T2 = T2BaseS | T2BaseD | T2Void | T2Pair T2 T2 |
          T2Fun T2 T2 | T2UFun T2 T2 | T2SumS T2 T2 |
	  T2SumD T2 T2 | T2TagS String T2 T2 | T2Poly T2 |
	  T2TagD String T2 T2 |
	  T2Var Int | T2Label Int T2 | T2Delay T2 | T2Sum T2 |
	  T2Monad T2 | T2RefS T2 | T2RefD T2
	  deriving (Show,Eq)

showtype t = let (t',ls) = getlabels (prune [] t) in
             showt t'++
	     if null ls then "" else
	     " where "++foldr1 (\x y->x++", "++y)
	                  ["_"++show l++"="++showt t''
			  |(l,t'')<-ls]

showt (T2Fun a b) = sht"->" (showt'' a) (showt b)
showt (T2UFun a b) = sht"@>" (showt'' a) (showt b)
showt (T2Label i a) = "_"++show i++": "++showt a
showt t = showt'' t

showt'' (T2SumS a b) = sht "+" (showt' a) (showt'' b)
showt'' (T2SumD a b) = sht "++" (showt' a) (showt'' b)
showt'' (T2TagS c a b) = sht "|" (c++"@ "++showt' a) (showt'' b)
showt'' (T2TagD c a b) = sht "|" (c++" "++showt' a) (showt'' b)
showt'' t = showt' t
sht op a b = a++op++b

showt' T2BaseS = "Base@"
showt' T2BaseD = "Base"
showt' T2Void = "void"
showt' (T2Poly t) = "poly "++showt' t
showt' (T2Pair a b) = "("++showt a++","++showt b++")"
showt' (T2Delay a) = "delay "++showt' a
showt' (T2Sum a) = "sum "++showt' a
showt' (T2Var x) = "_"++show x
showt' (T2Monad a) = "M "++showt' a
showt' (T2RefS a) = "ref@ "++showt' a
showt' (T2RefD a) = "ref "++showt' a
showt' t = "("++showt t++")"

prune xs (T2Label i t) = let t' = prune (i:xs) t in
                         if i `elem` frees t' then T2Label i t'
			 else t'
prune xs (T2Var i) = T2Var i
prune xs (T2Fun a b) = pr2 xs T2Fun a b
prune xs (T2UFun a b) = pr2 xs T2UFun a b
prune xs (T2SumS a b) = pr2 xs T2SumS a b
prune xs (T2SumD a b) = pr2 xs T2SumD a b
prune xs (T2TagS c a b) = pr2 xs (T2TagS c) a b
prune xs (T2TagD c a b) = pr2 xs (T2TagD c) a b
prune xs (T2Pair a b) = pr2 xs T2Pair a b
prune xs (T2Poly a) = T2Poly (prune xs a)
prune xs (T2Delay a) = T2Delay (prune xs a)
prune xs (T2Sum a) = T2Sum (prune xs a)
prune xs (T2Monad a) = T2Monad (prune xs a)
prune xs (T2RefS a) = T2RefS (prune xs a)
prune xs (T2RefD a) = T2RefD (prune xs a)
prune xs t = t

pr2 xs t a b = t (prune xs a) (prune xs b)

frees (T2Label i t) = frees t
frees (T2Var i) = [i]
frees (T2Fun a b) = fr2 a b
frees (T2UFun a b) = fr2 a b
frees (T2SumS a b) = fr2 a b
frees (T2SumD a b) = fr2 a b
frees (T2TagS c a b) = fr2 a b
frees (T2TagD c a b) = fr2 a b
frees (T2Pair a b) = fr2 a b
frees (T2Poly a) = frees a
frees (T2Delay a) = frees a
frees (T2Sum a) = frees a
frees (T2Monad a) = frees a
frees (T2RefS a) = frees a
frees (T2RefD a) = frees a
frees _ = []

fr2 a b = frees a ++ frees b

getlabels (T2Label i t) = let (t',ls)=getlabels t in 
                          (T2Var i,(i,t'):ls)
getlabels (T2Fun a b) = gl2 T2Fun a b
getlabels (T2UFun a b) = gl2 T2UFun a b
getlabels (T2SumS a b) = gl2 T2SumS a b
getlabels (T2SumD a b) = gl2 T2SumD a b
getlabels (T2TagS c a b) = gl2 (T2TagS c) a b
getlabels (T2TagD c a b) = gl2 (T2TagD c) a b
getlabels (T2Pair a b) = gl2 T2Pair a b
getlabels (T2Poly a) = let (a',ls) = getlabels a in
                       (T2Poly a',ls)
getlabels (T2Delay a) = let (a',ls) = getlabels a in
                        (T2Delay a',ls)
getlabels (T2Sum a) = let (a',ls) = getlabels a in
                        (T2Sum a',ls)
getlabels (T2Monad a) = let (a',ls) = getlabels a in
                        (T2Monad a',ls)
getlabels (T2RefS a) = let (a',ls) = getlabels a in
                        (T2RefS a',ls)
getlabels (T2RefD a) = let (a',ls) = getlabels a in
                        (T2RefD a',ls)

getlabels t = (t,[])

gl2 c a b = let (a',ls1) = getlabels a
                (b',ls2) = getlabels b
	    in (c a' b',ls1++[x|x<-ls2,not(x`elem`ls1)])

