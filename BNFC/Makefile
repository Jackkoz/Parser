all:
	happy -gca ParGram.y
	alex -g LexGram.x
	latex DocGram.tex; dvips DocGram.dvi -o DocGram.ps
	ghc --make TestGram.hs -o TestGram
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocGram.ps
distclean: clean
	-rm -f DocGram.* LexGram.* ParGram.* LayoutGram.* SkelGram.* PrintGram.* TestGram.* AbsGram.* TestGram ErrM.* SharedString.* Gram.dtd XMLGram.* Makefile*

