# name of agda compiler name
AGDA = agda
LATEX = pdflatex

STANDARD_LIBRARY_PATH = /home/ernius/.agda-backup/agda-stdlib-0.13/src/

# agda html
AGDAHTMLFLAGS = --html

# agda latex
AGDALATEXFLAGS = --latex

latex/Examples/%.tex : Examples/%.lagda
	$(AGDA) --no-libraries -i . -i $(STANDARD_LIBRARY_PATH) $(AGDALATEXFLAGS) $<

latex/%.tex : %.lagda 
	$(AGDA) --no-libraries -i . -i $(STANDARD_LIBRARY_PATH) $(AGDALATEXFLAGS) $<

bib : latex/resumen.bib
	cd latex; pdflatex resumen.tex; bibtex resumen;pdflatex resumen.tex;pdflatex resumen.tex; cd ..;

resumen : latex/resumen.tex latex/*.tex latex/Examples/*.tex
	cd latex; $(LATEX) resumen.tex; cd ..;	

generic : latex/generic.tex latex/*.tex latex/Examples/*.tex
	cd latex; $(LATEX) generic.tex; cd ..;	

example : *.lagda Examples/*.lagda List/*.lagda
	$(AGDA) --no-libraries -i . -i $(STANDARD_LIBRARY_PATH) Examples/SystemF.lagda

html : *.lagda Examples/*.lagda List/*.lagda
	$(AGDA) --no-libraries -i . -i $(STANDARD_LIBRARY_PATH) $(AGDAHTMLFLAGS)  Examples/SystemF.lagda; $(AGDA) $(AGDAHTMLFLAGS)  Examples/LambdaCalculus.lagda

clean :
	rm *.agdai
