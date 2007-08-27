module LatexOutputHelper where

class ShowLatex a where
 showLatex :: a -> String

instance ShowLatex Bool where
 showLatex b = if b then "1" else "."


separate :: ShowLatex a => String -> [a] -> String
separate s os = foldl1 (\a1 a2 -> (a1 ++ s ++ a2)) $ map showLatex os

math :: String -> String
math s = if (length s) > 0 then ("$" ++ s ++ "$") else ""

bold :: String -> String
bold s = "\\textbf{" ++ s ++ "}"


putEol :: String -> String
putEol s = s ++ "\\\\"


verbatim :: String -> String
verbatim s = "\\begin{verbatim}" ++ s ++ "\\end{verbatim}"


insertEol :: String -> String -> String
insertEol sa sb = sa ++ "\n" ++ sb
