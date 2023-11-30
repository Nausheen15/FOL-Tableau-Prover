# Runing fol.sml generates tableau.dot
# Use make to produce a pdf containing the proof tree.

tableau.dot.pdf: tableau.dot.tex
	pdflatex tableau.dot.tex

tableau.dot.tex: tableau.dot
	dot2tex tableau.dot > tableau.dot.tex
