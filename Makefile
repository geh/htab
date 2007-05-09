# Useful commands
# - make         compiles the prover
# - make prof    compiles the prover for profiling
# - make opt     compiles the prover with all optimizations on
# - make static  compiles the prover without dynamic libraries
# - make parsers compiles the parsers
# - make tidy    removes all intermediary tex files (like *.aux)
# - make clean   removes all compiled files (like *.pdf, *.aux)
# - make release creates a tarball that you can give to others

# TODO
# - make docs    compiles your documentation
# - make html    compiles documentation to html

# --------------------------------------------------------------------
# configuration
# --------------------------------------------------------------------

SRC_HYLORES 	= ./src
GHCFLAGS        = -fglasgow-exts -Wall
GHCFLAGSOPT     = -O2
GHCFLAGSSTATIC  = -optl -static
GHCINCLUDE      = -i$(SRC_HYLORES)
#:$(HXMLDIR)/hparser:$(HXMLDIR)/hdom
GHCPACKAGES     = 
GHC             = ghc $(GHCFLAGS) $(GHCINCLUDE)

SOFTWARE        = HTab
VERSION         = 2.0
VERSIONTAG      = htab-1-00  # use: make tagVersion for creating cvs tag
SOFTVERS        = $(SOFTWARE)-$(VERSION)

# You should replace the value of this variable with your project
# directory name.  The default assumption is that the project name
# is the same as the directory name.
MYDIR = HTab
DATE:=$(shell date +%Y-%m-%d)

# Add here any files that you want to compile.  For example:
#   MAKE_DOCS=foo/bar.pdf foo/other.pdf baz/filename.pdf
# If you are making slides instead of documents, you should
# uncomment and modify the MAKE_SLIDES variable.
MAKE_DOCS = src/htab/htabdoc.pdf

# -- Latex or Pdflatex? (pdflatex by default) --
# If you use latex instead of pdflatex, you should change the line
# below as well as uncommenting DVIPDF
LATEX=pdflatex
# LATEX=latex

# -- dvipdf --     (currently off because we use pdflatex)
# If you use latex instead of pdflatex, you should uncomment
# DVIPDF
DVIPDF_CMD=dvips `basename $< .tex`.dvi -o `basename $< .tex`.ps;\
	ps2pdf `basename $< .tex`.ps
#DVIPDF=$(DVIPDF_CMD)

# -- bibtex --     (currently on)
# If you use BibTeX you should uncomment
BIBTEX_CMD=$(LATEX) `basename $<`;\
	   bibtex `basename $< .tex`;
#BIBTEX=$(BIBTEX_CMD)

# -- latex2html -- (currently off)
LATEX2HTML = latex2html -math -math_parsing -local_icons -noimages -split 5
# If you want to use latex2html you should uncomment this line
# and add here any tex files you want compiled to html; for
# example, if you have foo.tex, you should add foo-html
MAKE_HTML = src/htab/htabdoc-html

# --------------------------------------------------------------------
# source stuff
# --------------------------------------------------------------------

IFILE = $(SRC_HYLORES)/Htab
DIFILE = $(SRC_HYLORES)/Htab

OFILE = ./bin/htab
DOFILE = ./bin/htabprof

LEXERS		= $(SRC_HYLORES)/HyLoLexer.hs \
                  $(SRC_HYLORES)/Clexer.hs
PARSERS		= $(SRC_HYLORES)/HyLoParse.hs \
                  $(SRC_HYLORES)/Cparser.hs

# Phony targets do not keep track of file modification times
.PHONY: all clean docs parsers release opt

# --------------------------------------------------------------------
# main targets
# --------------------------------------------------------------------

normal: compile
all: compile docs tidy
release: compile docs html tidy tarball

parsers: $(PARSERS)

doc:  $(MAKE_DOCS)
html: $(MAKE_HTML)

tarball:
	rm -f $(MYDIR)*.tar.gz;\
	cd .. ;\
	tar -czvf $(MYDIR)_$(DATE).tar.gz $(MYDIR);\
	mv $(MYDIR)_$(DATE).tar.gz $(MYDIR)

clean: tidy
	rm -f $(LEXERS) $(PARSERS)
	rm -f $(SRC_HYLORES)/*.{ps,pdf}
	rm -f $(MAKE_HTML)
	rm -rf $(OFILE)

tidy:
	rm -f $(SRC_HYLORES)/*.{dvi,aux,log,bbl,blg,out,toc}
	rm -f $(SRC_HYLORES)/*.{hi,o}

# --------------------------------------------------------------------
# compilation
# --------------------------------------------------------------------

$(LEXERS): %.hs: %.x
	alex -g $<

$(PARSERS): %.hs: %.y
	happy -m `basename $@ .hs` $<

compile: $(LEXERS) $(PARSERS)
	$(GHC) --make $(GHCPACKAGES) $(IFILE).hs -o $(OFILE)

opt: $(LEXERS) $(PARSERS)
	$(GHC) $(GHCFLAGSOPT) --make $(GHCPACKAGES) $(IFILE).hs -o $(OFILE)

static: $(LEXERS) $(PARSERS)
	$(GHC) $(GHCFLAGSSTATIC) --make $(GHCPACKAGES) $(IFILE).hs -o $(OFILE)


prof: $(LEXERS) $(PARSERS)
	$(GHC) -prof -auto-all --make $(GHCPACKAGES) $(DIFILE).hs -o $(DOFILE)

# --------------------------------------------------------------------
# documentation
# --------------------------------------------------------------------

DOC_SRC=$(SRC_HYLORES)/Mstate.lhs $(SRC_HYLORES)/Geni.lhs $(SRC_HYLORES)/Polarity.lhs

$(MAKE_DOCS): %.pdf: %.tex $(DOC_SRC)
	cd `dirname $<`;\
	$(BIBTEX)\
	$(LATEX) `basename $<`;\
	$(LATEX) `basename $<`;\
	$(DVIPDF)

$(MAKE_HTML): %-html: %.tex
	rm -rf $@
	$(LATEX2HTML)  $<
#	mv `basename $< .tex` $@
