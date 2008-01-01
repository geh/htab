module LatexOutputHelper where

import qualified Data.IntSet as IntSet

class ShowLatex a where
 showLatex :: a -> String

instance ShowLatex Bool where
 showLatex b = if b then "1" else "."

instance (ShowLatex a, ShowLatex b) => ShowLatex (a,b) where
 showLatex (a,b) = "(" ++ showLatex a ++ "," ++ showLatex b ++ ")"

instance (ShowLatex a, ShowLatex b, ShowLatex c) => ShowLatex (a,b,c) where
 showLatex (a,b,c) = "(" ++ showLatex a ++ "," ++ showLatex b ++ "," ++ showLatex c ++ ")"

instance (ShowLatex a) => ShowLatex [a] where
 showLatex l = "[" ++ (lseparate ", " l)  ++ "]"

instance ShowLatex Int where
 showLatex = show

instance ShowLatex IntSet.IntSet where
 showLatex = show . IntSet.toList


lseparate :: ShowLatex a => String -> [a] -> String
lseparate _ [] = ""
lseparate s os = foldl1 (\a1 a2 -> (a1 ++ s ++ a2)) $ map showLatex os

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
