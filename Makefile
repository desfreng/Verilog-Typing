DOC_DIR      := doc
ROCQ_DIR     := theories
DEPEND_FILE  := .depend.d
EXTR_DIR     := extraction

.PHONY: all build dep-file doc clean artifact .FORCE

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
	-rm artifact/sources.zip artifact/docker-image.tar.zstd artifact.zip
	@echo "Clean complete."

artifact/sources.zip: .FORCE
	git archive --format=zip --output artifact/sources.zip main

artifact/docker-image.tar.zstd: artifact/sources.zip Dockerfile
	docker build . -t docker-verilog
	docker save docker-verilog | zstd --ultra -22 -T10 > artifact/docker-image.tar.zstd

artifact.zip: artifact/docker-image.tar.zstd
	zip -0 -r artifact.zip artifact/

artifact: artifact.zip

.FORCE:
