module LatexOutput where


import CommandLine
import Control.Monad.State(lift,StateT)


latexHeader :: String
latexHeader = "\\documentclass[a4paper,10pt]{article}\n\\usepackage{geometry}\\geometry{hmargin=0cm}\n\\usepackage{amssymb}\n\\begin{document}\n"

latexFooter :: String
latexFooter = "\\end{document}\n"

section :: String -> String
section name = "\\newpage\\section{" ++ name ++ "}\n"


latexPutCLP :: CmdLineParams -> String -> StateT ma (StateT mb IO) ()
latexPutCLP clp input = maybe (return ()) doWrite (latexOutput clp)
    where doWrite f = lift . lift $ appendFile f (input ++ "\n")  -- liftIO

latexInit :: CmdLineParams -> IO ()
latexInit clp = maybe (return ()) doWrite (latexOutput clp)
    where doWrite f = writeFile f latexHeader

latexEnd :: CmdLineParams -> IO ()
latexEnd clp = maybe (return ()) doWrite (latexOutput clp)
    where doWrite f = appendFile f latexFooter

