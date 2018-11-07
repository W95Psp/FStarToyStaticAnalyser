# For simplified Makefiles, define FSTAR_HOME, then include the file below.
FSTAR=/home/FStar/FStar/bin/fstar.exe
FSTAR_HOME=/home/FStar/FStar/
#include ../Makefile.include

all: ocaml 

include $(FSTAR_HOME)/ulib/ml/Makefile.include



# This target is very concise and re-uses the variables defined in
# Makefile.include. You shouldn't need to call `cp` ever.
ocaml: out Main.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out --codegen OCaml Main.fst
	$(OCAMLOPT) out/Main.ml -o Main.exe
	./Main.exe

# FIXME (Guido): This comment seems very stale. I made the rule look
# exactly as the one for `hello` and this works anyway.
#
# This target demonstrates how to compile with native_ints: the recursive
# invocation of $(MAKE) changes, and so do the include paths for `ocamlopt`.
# In this particular case, we need to compile against the extracted version of
# `FStar.Seq` (it is not realized in ML), so we pass it to `ocamlopt`.

LIB=$(FSTAR_HOME)/ulib
BIN=$(FSTAR_HOME)/bin

ifeq ($(OS),Windows_NT)
FSC     = fsc --mlcompatibility
else
FSC     = fsharpc --mlcompatibility
endif

ifeq ($(OS),Windows_NT)
FSRUNTIME =
else
FSRUNTIME = mono
endif

fs: out Main.fst
	$(FSTAR)   --odir out --codegen OCaml Main.fst
	$(FSRUNTIME) ./out/Main.exe

out:
	mkdir -p out

clean:
	rm -rf out
	rm -f *~
