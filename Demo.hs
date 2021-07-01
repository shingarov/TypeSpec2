import CGI
import Mix
import Types
import Monad
import FMap
import Parser(parseexpr)


err = \e->appendChan stdout "error" abort done


main = getFormData err $ \dat->
       writeCGI "text/html" (output dat)
         err done
       where output dat= 
                     htmlpage "Type Specialisation Demo"
                        (form "Demo.cgi"
			  ["<h2>Input to Specialiser</h2>",
			   textarea "prog" (length (lines prog)+1) 
			                   (maxs (35:map length (lines prog))+5)
					   prog,
			   input "SUBMIT" "Respecialize"]++
			 form "lastspec.cgi"
			   [input "SUBMIT" "See last specialisation"]++
			   "<h2>Result of Specialisation</h2><pre>"++
                           (runmix False (parseexpr prog))++
			   "</pre>")
		  where prog = assoc dat "prog"

maxs =foldr max 0

htmlpage title body =
  "<title>"++title++"</title><h1>"++title++"</h1>"++body
form act xs = "<form action="++quote act++" method="++quote "get"++">"++
              unlines xs++
	      "</form>"
textarea name rows cols body =
  "<textarea name="++quote name++" rows="++quote (show rows)++
  " cols="++quote(show cols)++">"++body++"</textarea>"
input typ val = 
  "<input type="++quote typ++" value="++quote val++">"
quote s = "\""++s++"\""
