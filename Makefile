THEORY_DIR := Theory
LATEX_SRC := $(wildcard $(THEORY_DIR)/*.tex)
PDF_OUT := $(LATEX_SRC:.tex=.pdf)

$(THEORY_DIR)/%.pdf: $(THEORY_DIR)/%.tex
	latexmk -lualatex -jobname="$(THEORY_DIR)/%A" "$<"

theory: $(PDF_OUT)

clean:
	latexmk -c -jobname="$(THEORY_DIR)/%A" $(LATEX_SRC)

.PHONY: theory clean