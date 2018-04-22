# name of agda compiler name
AGDA = agda
LATEX = pdflatex

# agda html
AGDAHTMLFLAGS = --html

# agda latex
AGDALATEXFLAGS = --latex

latex/Examples/%.tex : Examples/%.lagda
	$(AGDA) $(AGDALATEXFLAGS) $<

latex/%.tex : %.lagda 
	$(AGDA) $(AGDALATEXFLAGS) $<

bib : latex/resumen.bib
	cd latex; pdflatex resumen.tex; bibtex resumen;pdflatex resumen.tex;pdflatex resumen.tex; cd ..;

resumen : latex/resumen.tex latex/*.tex latex/Examples/*.tex
	cd latex; $(LATEX) resumen.tex; cd ..;	

generic : latex/generic.tex latex/*.tex latex/Examples/*.tex
	cd latex; $(LATEX) generic.tex; cd ..;	

Example : Examples/SystemF.agda
	$(AGDA) $(AGDALIBRARYFLAGS) Examples/SystemF.agda

html : *.lagda
	$(AGDA) $(AGDAHTMLFLAGS)  Examples/SystemF.lagda; $(AGDA) $(AGDAHTMLFLAGS)  Examples/LambdaCalculus.lagda
clean :
	rm *.agdai
