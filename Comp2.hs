import Mix
import Types
import Monad
import FMap
import IO(getFile)
import Parser(parseexpr)

main = getArgs abort (\as->interact (runmix ("-d"`elem`as).mkinput))

mkinput prg = 
  let interp = parseexpr (getFile "interp")
      prg' = compile (read prg)
  in App interp prg'

data LE = Cn Int | Vr Int | Lm Int LE | Ap LE LE | Fx LE
  deriving (Text)

compile (Cn n) = TagS "Cn" (IntS n)
compile (Vr n) = TagS "Vr" (IntS n)
compile (Lm n e) = TagS "Lm" (Pair (IntS n) (compile e))
compile (Ap e e') = TagS "Ap" (Pair (compile e) (compile e'))
compile (Fx e) = TagS "Fx" (compile e)
