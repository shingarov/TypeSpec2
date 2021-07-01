module TTermType where
import TermType
import StatType

-- typed terms: residual terms are built with type annotations
-- to make void erasure possible.

type TTerm = (TTerm',Stat)

data TTerm' = TVar String
            | TApp TTerm TTerm
	    | TLam String TTerm
	    | TPair TTerm TTerm
	    | TFst TTerm
	    | TSnd TTerm
	    | TInl TTerm
	    | TInr TTerm
	    | TCase TTerm String TTerm String TTerm
	    | TInt Int
	    | TBool Bool
	    | TStr String
	    | TArith String TTerm TTerm
	    | TEq TTerm TTerm
	    | TVoid
	    | TFix TTerm
	    | TLet String TTerm TTerm
	    | TRef Int
	    | TError String
	    | TIn Int TTerm
	    | TCaseN TTerm String [(Stat,TTerm)]
	    | TPrj Int TTerm
	    | TTup [TTerm]
	    | TUnit TTerm
	    | TMLet String TTerm TTerm
	    | TMkref TTerm
	    | TDeref TTerm
	    | TAssign TTerm TTerm
	    | TTag String TTerm
	    | TCaseTag TTerm [(String,(String,Stat,TTerm))]
	    | TIf TTerm TTerm TTerm
  deriving (Show)
