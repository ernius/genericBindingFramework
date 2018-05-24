AGDA = agda
LATEX = pdflatex

# not using libraries (--no-libraries)
STANDARD_LIBRARY_PATH = /home/ernius/.agda/agda-stdlib-0.13/src/

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

docker : *.lagda Examples/*.lagda List/*.lagda
	wget https://github.com/agda/agda-stdlib/archive/v0.13.tar.gz -O /tmp/v0.13.tar.gz
	tar -xzf /tmp/v0.13.tar.gz -C .
	docker pull ecopello/agda:version2.5.2  
	docker run -v $(shell pwd):/tmp/project-build -v $(shell pwd):/tmp/agdalibrary ecopello/agda:version2.5.2 /bin/sh -c 'cd /tmp/project-build; agda --no-libraries -i . -i /tmp/agdalibrary/agda-stdlib-0.13/src Examples/SystemF.lagda'         

clean :
	rm *.agdai
