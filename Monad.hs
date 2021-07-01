module Monad where
import Types
import FMap

infixr 1 `andThen`

-- partial evaluation can:
-- * allocate fresh variables
-- * unify static values
-- * create demons that run when variables are instantiated.
-- * backtrack
-- * rename variables to avoid name capture

data SpecMonad a = M ([String] -> MState -> Perhaps [(MState,a)]) 
  deriving (Show)
data Perhaps a = Yes a | No String deriving (Show)
type MState = (Int,               -- next fresh variable
               Table VarState,   -- variable instantiations
               Int,               -- next fresh term variable
	       AList Int TTerm'    -- instantiations of term vars
              )
data VarState = Full Stat | Empty [Demon] deriving Show
type Demon = Stat -> SpecMonad ()

-- functions for accessing the state
nextvar u (v,vs,tv,tvs) = (v,(u,vs,tv,tvs))
varvals u (v,vs,tv,tvs) = (vs,(v,u,tv,tvs))
nexttvar u(v,vs,tv,tvs) = (tv,(v,vs,u,tvs))
tvarvals u(v,vs,tv,tvs) = (tvs,(v,vs,tv,u))

unit x = M (\sc s->Yes[(s,x)])
M x `bind` f = M (\sc s->case x sc s of
  Yes svs->foldr1 comb [let M y=f v in y sc s' | (s',v)<-svs]
  No err -> No err)
comb (No _) y = y
comb (Yes xs) y = Yes (xs++(case y of
	                      Yes zs->zs
			      No _ -> []))

failM err = M (\sc s->No err)
get v = M (\sc s->Yes[(s,fst(v (error "get") s))])
set v x = M (\sc s->Yes[(snd(v x s),())])
change v f = M (\sc s->let (old,s') = v new s
                           (new,x) = f old
		       in Yes [(s',x)])
M x `orelse` M y = M (\sc s->comb (x sc s) (y sc s))

rename v k = M (\sc s->let v'=r sc v 0
                           M f=k v'
		       in f (v':sc) s)
  where r sc x n = let x' = mkid x n in
                   if x' `elem` sc then r sc x (n+1)
		   else x'
        mkid x 0 = x
	mkid x 1 = x++"'"
	mkid x n = x++show n

fresh = change nextvar $ \v->(v+1,SVar v)
getvar w = get varvals `bind` \vs->
           case assocT vs w of
	     Full v -> unit (Yes v)
	     Empty _-> unit (No ("getvar "++show w++" not found"))
setvar w x = change varvals (\vs->
               case assocT vs w of
	         Full y -> error ("setvar "++show w++
		             " already defined.\n"++
			     "   old value: "++show y++"\n"++
			     "   new value: "++show x++"\n")
		 Empty ds ->
		   let vs' = updateT w (Full x) vs in
		   case x of
		     SVar u -> -- reinstall demons on new var
		       case assocT vs u of
		         Empty ds' -> 
			   (updateT u (Empty (ds++ds')) vs', [])
			 Full _ ->
			   error ("setvar "++show w++" "++
			          show x++
				  ": 2nd arg instantiated\n")
                     _ -> (vs',ds)) `bind` \ds->
	     -- invoke the demons
	     foldr andThen (unit ()) [d x | d<-ds]
demon u d = indirect u `bind` \u'->case u' of
              SVar w-> -- create demon
	              change nexttvar (\v->(v+1,v)) `bind` \tv->
		      change varvals (\vs->
		        (applytoT vs w (\(Empty ds)->
			   Empty ((\x->d x`bind`settvar tv):ds)),
			 TRef tv))
	      v -> d v

gettvar w = change tvarvals (\tvs->(tvs,assoc tvs w))
settvar w x = change tvarvals (\tvs->(update w x tvs,()))
indirect u = case u of
               SVar w->getvar w `bind` \z->case z of
	                 Yes u'->indirect u'
			 No _ ->unit u
               _ -> unit u

mapvars f = get nextvar `bind` \nv->
            foldr (bin (:)) (unit []) [f i | i<-[0..nv-1]]

app f x = x `bind` (unit.f)
bin op x y = x `bind` \u-> y `bind` \v -> unit (u `op` v)
tri f x y z = x `bind` \u->bin (f u) y z
x `andThen` y = x `bind` \_->y
pair = bin (\x y->(x,y))

fresh2 = fresh `pair` fresh
freshs i | i==0 = unit []
         | otherwise = fresh `bind` \v -> freshs (i-1) `bind` \vs-> unit (v:vs)
