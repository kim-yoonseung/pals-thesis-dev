PROJHOME := $(PWD)

COQFILES := $(wildcard src/**/*.v)

PROOF_BUILD_DIR := .build-proof


.PHONY: all init rsync coq clean coq-quick

coq: Makefile.coq $(COQFILES)
	$(MAKE) -f Makefile.coq

all: init coq

init:
	opam install coq.8.13.2 coq-paco.4.1.1 coq-itree.3.2.0 coq-compcert.3.8

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

rsync:
	./rsync-send.sh
	$(MAKE) -C $(PROOF_BUILD_DIR) coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq*

coq-quick: Makefile.coq $(COQFILES)
	$(MAKE) -f Makefile.coq quick
