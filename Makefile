DOC_DIR      := doc
ROCQ_DIR     := theories
DEPEND_FILE  := .depend.d
EXTR_DIR     := extraction

.PHONY: all build dep-file doc clean docker artifact

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
	rocqnavi -Q $(ROCQ_DIR) Verilog -d $(DOC_DIR) -file-graph-from-depend $(DEPEND_FILE) -short-names $(wildcard $(ROCQ_DIR)/*.v) $(wildcard $(ROCQ_DIR)/*.glob)
	@echo "Documentation generated."
	@echo "See $(DOC_DIR)/index.html"

clean: RocqMakefile
	@echo "Cleaning build artifacts..."
	$(MAKE) --no-print-directory -f RocqMakefile clean
	-rm RocqMakefile RocqMakefile.conf
	-rm -rf $(DOC_DIR) $(EXTR_DIR)
	@echo "Clean complete."

docker:
	docker build . -t docker-verilog
	docker save docker-verilog | gzip -9 > artifact/docker-image.tar.gz

artifact:
	git archive --format=zip --output artifact/sources.zip main
	zip -9 -r artifact.zip artifact/
