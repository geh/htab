# HTab, a hybrid logic tableau prover

HTab is a tableau-based satisfiability checker. It currently
handles the hybrid logic H(:,E) with role inclusions,
and terminates on all inputs.

## Compiling and using

To build HTab, you will need at least GHC 8.6, and either
[cabal-install](https://wiki.haskell.org/Cabal-Install)
or [stack](http://www.haskellstack.org/).
Dependencies, including `hylolib`

A summary of the `htab` flags is available by running:

    htab --help

## Model building

HTab can output a model in the dot format for a satisfiable formula by using
the `-m` option with `-d`:

    htab -f input.frm -m model.m -d
    dot model.m  -Tpdf  -omodel.pdf

This requires the `graphviz` package to get the `dot` executable.

## Authors

* Carlos Areces
* Juan Heguiabehere
* Guillaume Hoffmann
* Daniel Gorín
