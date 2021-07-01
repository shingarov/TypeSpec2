module FMap(AList(..),update,assoc,remove,dom,ran,restrict,mapran,
            Table, initT, assocT, updateT, applytoT)
where
-- finite maps

type AList a b = [(a,b)]

update x y xys = (x,y):xys
assoc xys x = case [y | (x',y)<-xys, x==x'] of
                (y:_) -> y
		[] -> error (show x++" not found in "++
		             show xys++"\n")
remove x xys = restrict (/=x) xys
dom xys = map fst xys
ran xys = map snd xys
restrict p xys = [(x,y)|(x,y)<-xys, p x]
mapran f xys = [(x,f y)|(x,y)<-xys]

-- infinite tables indexed by Int

{- 4-way trees: element 0 is stored at the root, and the subtrees
   hold elements equivalent to 0, 1, 2 and 3 mod 4.
   Not a big win over binary trees in my tests, but maybe is for
   bigger examples.
-}

data Table a = Node a (Table a) (Table a) (Table a) (Table a)
              | Init a
  deriving Show

initT x = Init x

recurseT t x k = recurseT' t x id k

recurseT' :: Table a -> Int -> (Table a->Table a) ->
               ((a->Table a)->a->b) -> b
recurseT' (Node v t1 t2 t3 t4) x build k =
  if x==0 then k (build.(\v'->Node v' t1 t2 t3 t4)) v else
    case x `mod` 4 of
      0 -> recurseT' t1 (x`div`4-1) 
             (build.(\t->Node v t t2 t3 t4)) k
      1 -> recurseT' t2 (x`div`4) 
             (build.(\t->Node v t1 t t3 t4)) k
      2 -> recurseT' t3 (x`div`4) 
             (build.(\t->Node v t1 t2 t t4)) k
      3 -> recurseT' t4 (x`div`4) 
             (build.(\t->Node v t1 t2 t3 t)) k
recurseT' t@(Init v) x build k =
  recurseT' (Node v t t t t) x build k

updateT x y t = recurseT t x (\build _ -> build y)
applytoT t x f = recurseT t x (\build v -> build (f v))
assocT t x = recurseT t x (\_ v->v)


{- clever datatype with list of binary trees, of strictly
   increasing depth, except for the first two which can be
   equal. We hold the variables backwards for fast access to
   the recently allocated ones.
 
   Less efficient in tests than 4-way trees.

data Table a = Table Int            -- num elements
                     a              -- initial element
		     [(Int,Tree a)] -- contents and sizes
  deriving Show
data Tree a = Leaf a | Node a (Tree a) (Tree a)
  deriving Show

initT x = Table (-1) x []

recurseT (Table n z ts) x k =
  let (n',ts') = if n<x then (x,iter(x-n) (extend z) ts)
                 else (n,ts)
  in recurseT' ts' (n'-x) (Table n' z) k
recurseT' ((m,t):mts) i build k =
  if i<m then recurseT'' m t i (build.(\t'->((m,t'):mts))) k
  else recurseT' mts (i-m) (build.((m,t):)) k
recurseT'' 1 (Leaf a) 0 build k = k (build.Leaf) a
recurseT'' m (Node a l r) i build k =
  if i==0 then k (build.(\a'->Node a' l r)) a else
  let m' = m`div`2 in
  if i<=m' then
    recurseT'' m' l (i-1) (build.(\l'->Node a l' r)) k
  else
    recurseT'' m' r (i-m'-1) (build.(\r'->Node a l r')) k

extend z mts@((m1,t1):(m2,t2):mts') | m1==m2 =
  ((m1+m2+1,Node z t1 t2):mts')
extend z mts = (1,Leaf z):mts

iter 0 f x = x
iter n f x = f (iter (n-1) f x)

updateT x y t = recurseT t x (\build _ -> build y)
applytoT t x f = recurseT t x (\build v -> build (f v))
-- explicit def of assoc to avoid extending table just to
-- discover variable is undefined.
assocT (Table n z mts) x = 
  if n<x then z else 
    recurseT' mts (n-x) (error "assoc/build") (\_ v->v)
-}
