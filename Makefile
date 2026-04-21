DOC_DIR      := doc
ROCQ_DIR     := theories
TEX_DIR      := formalisation
PROPOSAL_DIR := proposal
DEPEND_FILE  := .depend.d
TEX_FILES    := $(wildcard $(TEX_DIR)/*.tex)
PROPOSAL_TEX := $(wildcard $(PROPOSAL_DIR)/*.tex)
EXTR_DIR     := extraction

.PHONY: build doc clean tex dep-file

all: build doc

RocqMakefile: _RocqProject
	rocq makefile -f _RocqProject -o RocqMakefile

build: RocqMakefile $(wildcard $(ROCQ_DIR)/*.v)
	@mkdir -p $(EXTR_DIR)
	@echo "Building Rocq project..."
	$(MAKE) --no-print-directory -f RocqMakefile all
	@echo "Build complete."

dep-file: build
	$(COQBIN)rocq dep -f _RocqProject > $(DEPEND_FILE)

doc: build dep-file
	@echo "Generating documentation in $(DOC_DIR)"
	mkdir -p $(DOC_DIR)
	rocqnavi -Q $(ROCQ_DIR) Verilog -d $(DOC_DIR) -file-graph-from-depend $(DEPEND_FILE) -short-names $(wildcard $(ROCQ_DIR)/*.v) $(wildcard $(ROCQ_DIR)/*.glob) -show-type-information-using-coqtop-process
	@echo "Documentation generated."
	@echo "See $(DOC_DIR)/index.html"

clean: RocqMakefile
	@echo "Cleaning build artifacts..."
	$(MAKE) --no-print-directory -f RocqMakefile clean
	-rm RocqMakefile RocqMakefile.conf
	-rm -rf $(DOC_DIR) $(EXTR_DIR)
	-latexmk -cd -c $(TEX_FILES)
	-latexmk -cd -c $(PROPOSAL_TEX)
	@echo "Clean complete."

tex: $(TEX_FILES) $(PROPOSAL_TEX)
	latexmk -cd -pdf $(TEX_FILES)
	latexmk -cd -pdf $(PROPOSAL_TEX)
