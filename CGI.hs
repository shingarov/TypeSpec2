-- This module defines operations to decode HTML FORM data, for use in
-- CGI programs.

module CGI(getFormData, getPostedData, writeCGI, 
           htmlpage, body, showsource, form, textarea, input, select, ulist, 
	   bold, italic, link, preformat, heading, escape,
	   colour, red, orange, yellow, green, aqua, blue, violet, purple, 
	   black, white, spectrum, cbspectrum) 
where

import Char
import System

getFormData =
  do rm<-getEnv "REQUEST_METHOD"
     if rm=="GET" then getQueryData else getPostedData

getQueryData =
  do inp<-getEnv "QUERY_STRING"
     return (map splitdef (splitat '&' inp))
{-
  getEnv "CONTENT_LENGTH" f $ \len->
  readChan stdin f $ \inp->
  k (map splitdef (splitat '&' (take (read len) inp)))
-}

getPostedData =
  do len <- getEnv "CONTENT_LENGTH"
     inp <- getContents
     return (map splitdef (splitat '&' (take (read len) inp)))

splitat c [] = []
splitat c xs = takeWhile (/=c) xs:splitat c (drop 1 (dropWhile (/=c) xs))

splitdef xs = (unhex (takeWhile (/='=') xs),
               unhex (drop 1 (dropWhile (/='=') xs)))

unhex [] = []
unhex ('+':xs) = ' ':unhex xs
unhex ('%':a:b:xs) = chr (hexdig a*16+hexdig b):unhex xs
unhex (x:xs) = x:unhex xs

hexdig c | '0'<=c && c<='9' = ord c - ord '0'
         | 'a'<=c && c<='f' = ord c - ord 'a' + 10
	 | 'A'<=c && c<='F' = ord c - ord 'A' + 10
	 | otherwise = error ("Bad hex digit '"++[c]++"'\n")

writeCGI typ str =
  putStr ("Content-type: "++typ++"\n\n"++str++"\n")

htmlpage title body =
  "<title>"++escape title++"</title><h1>"++escape title++"</h1>"++body
body textc bgc s = "<body bgcolor="++bgc++" text="++textc++">"++s++"</body>"
showsource name body = 
  body++"<hr>This page was produced by a <a href=\"Haskell.cgi?name="++name++
  "\">Haskell program</a>"
form act xs = "<form action="++quote act++" method="++quote "post"++">"++
              unlines xs++
	      "</form>"
textarea name rows cols body =
  "<textarea name="++quote name++" rows="++quote (show rows)++
  " cols="++quote(show cols)++">"++body++"</textarea>"
input typ val = 
  "<input type="++quote typ++" value="++quote val++">"
quote s = "\""++s++"\""

select name opts = 
 "<select name="++quote name++">"++
 concat ["<option>"++opt | opt<-opts]++
 "</select>"

ulist xs = "<ul>"++concat["<li>"++x | x<-xs]++"</ul>"
bold s = "<b>"++s++"</b>"
italic s = "<i>"++s++"</i>"
link url s = "<a href="++quote url++">"++s++"</a>"
preformat s = "<pre>"++s++"</pre>"
heading n s = "<h"++show n++">"++s++"</h"++show n++">"

escape s = concat [esc c | c<-s]
  where esc '<' = "&lt;"
        esc  c  = [c]

colour c s = "<font color="++c++">"++s++"</font>"
red = "#FF0000"
orange = "#FFAA00"
yellow = "#AAFF00"
green = "#00FFAA"
aqua = "#00AAFF"
blue = "#0000FF"
violet = "#AA00FF"
purple = "#FF00AA"
black = "#000000"
white = "#FFFFFF"

spectrum m n = 
  if n<=2 then "#FF0000" else
  if m<0 then "#FF0000" else
  if m<=n`div`2 then "#"++f m (n`div`2)++"00"
  else "#00"++f (m-n`div`2) (n-n`div`2)
  where f x y = let k=(255*x)`div`y in hex (255-k)++hex k
hex n = [hexd (n`div`16),hexd (n`mod`16)]
hexd n = "0123456789ABCDEF"!!n

cbspectrum m n =
  if n<=2 then "#FF0000" else
  if m<0 then "#FF0000" else
  if m>n then "#0000FF" else
  let k=(255*m)`div`n in
  "#"++hex(255-k)++"00"++hex k
