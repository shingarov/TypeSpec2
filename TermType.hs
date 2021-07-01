module TermType where

-- Term represents terms of the two-level language.

data Term = Var String
          | App Term Term
	  | Lam String Term
	  | Let String Term Term 
	  | Pair Term Term
	  | Fst Term
	  | Snd Term
	  | InlS Term
	  | InrS Term
	  | CaseS Term String Term String Term
	  | InlD Term
	  | InrD Term
	  | CaseD Term String Term String Term
	  | IntS Int
	  | IntD Int
	  | StrS String
	  | StrD String
	  | BoolS Bool
	  | BoolD Bool
	  | ArithS String Term Term
	  | ArithD String Term Term
	  | IfS Term Term Term
	  | IfD Term Term Term
	  | Void
	  | Fix Term
	  | Lift Term
	  | EqS Term Term
	  | EqD Term Term
	  | TagS String Term
	  | CaseTagS Term [(String,(String,Term))]
	  | TagD String Term
	  | CaseTagD Term [(String,(String,Term))]
	  -- polyvariance
	  | Poly Term
	  | Spec Term
	  -- unfolding
	  | ULam String Term
	  | UApp Term Term
	  | UFix Term
	  | ULet String Term Term
	  -- constructor specialisation
	  | InD Term
	  | CaseInD Term String Term
	  | Error String
	  | InN Int Term
	  | CaseN Term String [Term]
	  -- monadic features
	  | Unit Term
	  | MLet String Term Term
	  | RefS Term
	  | RefD Term
	  | DerefS Term
	  | DerefD Term
	  | AssignS Term Term
	  | AssignD Term Term
	  | Prompt Term
	  -- for result of arity raising
	  | Tags String [Term]
	  | CaseTags Term [(String,([String],Term))]
	  | Lets [(String,Term)] Term
	  | Letrecs [(String,Term)] Term
  deriving (Eq,Show)

