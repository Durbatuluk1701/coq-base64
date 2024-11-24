# Coq project makefile

# Documentation target.  Type "make DOC=all-gal.pdf" to make PDF.
DOC	?= gallinahtml

# File $(PROJ) contains the list of source files.
# See "man coq_makefile" for its format.
PROJ	= _CoqProject

# Generated makefile
COQMK	= coq.mk

COQBIN?=
ifneq (,$(COQBIN))
# add an ending /
COQBIN:=$(COQBIN)/
endif

all:	$(COQMK)
	$(MAKE) -f $(COQMK)
	$(MAKE) -f $(COQMK) $(DOC)

$(COQMK): $(PROJ)
	$(COQBIN)coq_makefile -o $(COQMK) -f $(PROJ)

$(PROJ):
	@echo make $@

%:	$(COQMK) force
	$(MAKE) -f $(COQMK) $@

clean:	$(COQMK)
	rm *.vo*
	$(MAKE) -f $(COQMK) clean
	rm $(COQMK) $(COQMK).conf

.PHONY:	all clean force

test: 
	cd extracted && \
	ocamlc -c base64.mli && \
	ocamlc -c base64.ml && \
	ocamlc -c test_base64.ml && \
	ocamlc -o test_base64 base64.cmo test_base64.cmo 