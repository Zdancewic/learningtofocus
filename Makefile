# Coq sources
COQDIR = coq
COQLIBDIR = ../lib

# OCaml sources
MLDIRS = common,bw,util

MENHIR=menhir
CP=cpn

all: main.native

main.native:
	ocamlbuild -Is $(MLDIRS) bw/main.native

.PHONY: clean test qc restore

clean:
	ocamlbuild -clean
