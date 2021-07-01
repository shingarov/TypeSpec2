import CGI
import Mix
import Types
import Monad
import FMap
import Parser(parseexpr)
import System



main = do dat<- getFormData
          let file=assoc dat "file"
	  rm<-getEnv "REQUEST_METHOD"
	  prog<-if rm=="GET" then readFile file else return $ assoc dat "prog"
          writeCGI "text/html" (output prog)
       where output prog= 
                     htmlpage "Type Specialisation Demo"
                        (form "Demo.cgi"
			  ["<h2>Input to Specialiser</h2>",
			   textarea "prog" (length (lines prog)+1) 
			                   (maxs (35:map length (lines prog))+5)
					   prog,
			   input "SUBMIT" "Respecialize"]++
			   "<h2>Result of Specialisation</h2><pre>"++
                           (runmix False (parseexpr prog))++
			   "</pre>")

maxs =foldr max 0

