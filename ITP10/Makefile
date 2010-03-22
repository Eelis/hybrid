# $Id: Makefile,v 1.2 2009-03-13 08:33:42 blanqui Exp $
MAIN = paper

# for papers: 2 (enlarge by sqrt 2) 
# for slides: 8 (pack 8 on one sheet)
PACK ?= 2

TARGETS = $(MAIN).pdf
SOURCES = $(wildcard *.tex) $(wildcard *.text)

DVIPS2OPTS ?= -O-2cm,-1cm -t a4 -y 1200

export TEXINPUTS

all : $(TARGETS)

############################################################################

WWW = $(HOME)/public_html/$(DIR)

LATEX = latex
PDFLATEX = pdflatex
BIBTEX = bibtex

# latex stuff ##############################################################

.PHONY : *.tex

$(MAIN).dvi : $(INPUTS) $(EPS) 

$(MAIN).pdf : $(INPUTS) $(EPS)

%.dvi : %.tex  $(SOURCES)
	- TEXINPUTS=$(TEXINPUTS) $(LATEX) "\\nonstopmode\\input $<"

%.ps : %.dvi
	dvips $(DVIPSOPTS) -t a4 $< -o $@

%.eps : %.fig
	fig2dev -L eps -m 1.0 $< $@

%.pdf : %.fig
	fig2dev -L pdf -m 1.0 $< $@

%.pdf : %.tex
	- $(PDFLATEX) "\\nonstopmode\\input $<"

%.2.ps : %.dvi
	dvips $(DVIPSOPTS) $(DVIPS2OPTS) $< -o $@

%.8.ps : %.ps
	psnup -l -8 $< > $@

biblio : paper.tex paper.pdf
	bibtex paper

paper.tex : hybrid.tex
	lhs2TeX --poly -o paper.tex hybrid.tex

clean :
	rm -f paper.*

view.$(MAIN) : $(MAIN).pdf
	evince $(MAIN).pdf
