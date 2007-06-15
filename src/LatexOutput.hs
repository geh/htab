module LatexOutput where


import LatexOutputHelper
import CommandLine
import Control.Monad.State(lift,StateT)


latexHeader :: String
latexHeader = "\\documentclass[a4paper,10pt]{article}\n\\usepackage{amssymb}\n\\begin{document}\n"

latexFooter :: String
latexFooter = "\\end{document}\n"

section :: String -> String
section name = "\\newpage\\section{" ++ name ++ "}\n"


latexPutCLP :: CmdLineParams -> String -> StateT ma (StateT mb IO) ()
latexPutCLP clp input = if (latexOutput clp) then do let outname = latexName clp
                                                     lift . lift $ appendFile outname (input ++ "\n")  -- liftIO
                                             else return ()


latexInit :: CmdLineParams -> IO ()
latexInit clp = if (latexOutput clp) then do let outname = latexName clp
                                             writeFile outname latexHeader
                                     else return ()

latexEnd :: CmdLineParams -> IO ()
latexEnd clp = if (latexOutput clp) then do let outname = latexName clp
                                            appendFile outname latexFooter
                                     else return ()


