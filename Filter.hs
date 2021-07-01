main = interact f

f [] = []
f ('=':xs) = case xs of
  '\n':ys -> f ys
  '3':'D':ys -> '=':f ys
  '2':'E':ys -> '.':f ys
  'F':'4':ys -> "\\^o"++f ys
  _ -> error ("unexpected escape.\n="++takeWhile (/='\n') xs)
f (x:xs) = x:f xs
