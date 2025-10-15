DOC_DIR    := doc
SRC_DIR    := src
THEORY_DIR := theory
GRAPH_FILE := ./dependencies.dot
THEORY_TEX := $(wildcard $(THEORY_DIR)/*.tex)

.PHONY: build doc clean tex

all: build doc

RocqMakefile: _RocqProject
	$(COQBIN)rocq makefile -f _RocqProject -o RocqMakefile

build: RocqMakefile $(wildcard $(SRC_DIR)/*.v)
	@echo "Building Rocq project..."
	$(MAKE) --no-print-directory -f RocqMakefile all
	@echo "Build complete."

doc: build
	@echo "Generating documentation in $(DOC_DIR)"
	mkdir -p $(DOC_DIR)
	rocqnavi -Q $(SRC_DIR) Verilog -d $(DOC_DIR) -dependency-graph $(GRAPH_FILE) -short-names $(wildcard $(SRC_DIR)/*.v) $(wildcard $(SRC_DIR)/*.glob)
	@echo "Documentation generated."
	@echo "See $(DOC_DIR)/index.html"

clean: RocqMakefile
	@echo "Cleaning build artifacts..."
	$(MAKE) --no-print-directory -f RocqMakefile clean
	-rm RocqMakefile RocqMakefile.conf
	-rm -rf $(DOC_DIR)
	-latexmk -cd -C $(THEORY_TEX)
	@echo "Clean complete."

tex: $(THEORY_TEX)
	latexmk -cd -pdf $(THEORY_TEX)
	latexmk -cd -c $(THEORY_TEX)
