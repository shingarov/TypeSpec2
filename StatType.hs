module StatType where
import TermType

-- static values

data Stat = SVar Int        -- uninstantiated variable
          | SInl Stat       -- static sums
	  | SInr Stat
	  | STag String Stat
	  | STagD String Stat Stat
	  | SPair Stat Stat
	  | SSum Stat Stat  -- dynamic sums
	  | SFun Stat Stat
	  | SVoid           -- value of type 1
	  | SInt Int
	  | SIntD           -- void static val from dynamic int
	  | SBool Bool
	  | SBoolD
	  | SStr String
	  | SStrD
	  | SClos [String] [Stat] String Term
	  | SFix String [String] [Stat] String Term
	  -- indexed sets of static values
	  | SSet Set Stat   -- 2nd cpt is unique SVar -- set ide.
	  | SIn Stat        -- n-ary dynamic sum
	  | SPoly Stat      -- n-ary product
	  -- monadic types
	  | SMonad Stat
	  | SRef Stat
	  | SStore Int Stat
  deriving (Eq, Show)

data Set = Elem Stat Stat -- value and index (unique SVar)
         | Union Stat Stat -- back pointers
	 deriving (Eq, Show)

