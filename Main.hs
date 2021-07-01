import Mix
import Types
import Monad
import FMap
import Parser(parseexpr)
import System

main = do as<-getArgs
          interact (runmix ("-d"`elem`as).parseexpr)
