module LatexOutputHelper where

class ShowLatex a where
 showLatex :: a -> String

separate :: ShowLatex a => String -> [a] -> String
separate s (hd:tl1@(hd2:tl2)) = (showLatex hd) ++ s ++ (separate s tl1)
separate s (hd:[]) = (showLatex hd)
separate s [] = ""


math :: String -> String
math s = if (length s) > 0 then "$" ++ s ++ "$"
                           else ""

bold :: String -> String
bold s = "\\textbf{" ++ s ++ "}"


putEol :: String -> String
putEol s = s ++ "\\\\"


verbatim :: String -> String
verbatim s = "\\begin{verbatim}" ++ s ++ "\\end{verbatim}"


insertEol :: String -> String -> String
insertEol sa sb = sa ++ "\n" ++ sb
