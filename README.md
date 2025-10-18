# HTab, a hybrid logic tableau prover

HTab is a tableau-based satisfiability checker. It currently
handles the hybrid logic H(:,E) with role inclusions,
and terminates on all inputs.

Relevant references for HTab are [1] and [2] for the general tableau algorithm
and [3] for the pattern-based blocking and lazy branching technique currently used.

## Downloading

Download the source code of HTab either using Darcs:

    darcs clone --lazy http://hub.darcs.net/gh/htab

Or [downloading the source code as a zip file](http://hub.darcs.net/gh/htab/dist)
and unpacking it.

## Compiling and using

To build HTab, you will need at least GHC 8.6, and either
[cabal-install](https://wiki.haskell.org/Cabal-Install)
or [stack](http://www.haskellstack.org/).
Dependencies, including [hylolib](http://hackage.haskell.org/package/hylolib),
will be downloaded and compiled automatically.

A summary of the `htab` flags is available by running:

    htab --help

## Model building

HTab can output a model in the dot format for a satisfiable formula by using
the `-m` option with `-d`:

    htab -f input.frm -m model.m -d
    dot model.m  -Tpdf  -omodel.pdf

You will probably need to install the `graphviz` package to get the `dot`
executable.

[1] https://cs.famaf.unc.edu.ar/~hoffmann/publi/2009_m4m_htab.pdf
[2] https://cs.famaf.unc.edu.ar/~hoffmann/publi/2010_jal.pdf
[3] http://www.ps.uni-saarland.de/papers/abstracts/GoetzmannKaminskiSmolkaSpartacus.pdf
