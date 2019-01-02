STAR=/home/lucas/.opam/default/bin/fstar.exe
#/home/FStar/FStar/bin/fstar.exe
FSTAR_HOME=/home/lucas/.opam/default/lib/fstar/
FSTAR_ULIB=/home/lucas/.opam/default/lib/fstar/
#/home/FStar/FStar/
CAMLDEP=ocamldep

ifndef FSTAR_HOME
   $(error "Please define the `FSTAR_HOME` variable before including this makefile.")
endif

include $(FSTAR_ULIB)/gmake/z3.mk
include $(FSTAR_ULIB)/gmake/fstar.mk

EXEC = Main.out

ifeq ($(OS),Windows_NT)
  MSBUILD = $(FSTAR_HOME)/src/msbuild.bat
else
  # If can't find msbuild, use xbuild, but throw a warning
  MSBUILD = $(shell which msbuild || (echo '\n\n\033[0;31mWarning:\033[0m could not find "msbuild", trying (deprecated) "xbuild"\n\n'>&2; which xbuild))
  # syntax highlightint fix ')
endif

%.uver: %.fst
	$(FSTAR) --use_extracted_interfaces true $^

%.fail-uver: %.fst
	(! $(FSTAR) $^ >/dev/null 2>&1) || (echo "NEGATIVE TEST FAILED ($@)!" ; false)

include $(FSTAR_ULIB)/ml/Makefile.include


ROOTS=$(shell echo *.fst)# AbstractDomain.fst CSet.fst CSetPO.fst DefaultValue.fst EnumerableMap.fst ExtInt.fst GaloisConnection.fst Interval.fst Main.fst Misc.fst PartialOrder.fst StaticAnalyser.fst ToString.fst ToyLanguageDef.fst ToyLanguageInterpreter.fst ZeroOrLess.fst

compile:
	bash compile.sh

gg:
	mkdir -p out
	cp MyIO.ml out/
	# cp /home/FStar/FStar/ulib/ml/FStar_Char.ml out/

# all: verify-all
all: gg codegen compile

exec:
	bash -c "cd out; ./Main.native"

x: clean all

test:
	echo $(OCAMLOPT)

FSTAR_MORESTUFF=--no_extract FStar.BitVector --no_extract MyIO --no_extract FStar.List.Tot --no_extract FStar.List.Tot.Properties --no_extract FStar.Math.Lemmas --no_extract FStar.Math.Lib --no_extract FStar.OrdSet --no_extract FStar.PredicateExtensionality --no_extract FStar.Preorder --no_extract FStar.PropositionalExtensionality --no_extract FStar.Reflection --no_extract FStar.Reflection.Const --no_extract FStar.Reflection.Derived --no_extract FStar.Reflection.Derived.Lemmas --no_extract FStar.Reflection.Formula --no_extract FStar.Seq --no_extract FStar.Seq.Base --no_extract FStar.Seq.Properties --no_extract FStar.StrongExcludedMiddle --no_extract FStar.Tactics --no_extract FStar.Tactics.Derived --no_extract FStar.Tactics.Effect --no_extract FStar.Tactics.Logic --no_extract FStar.Tactics.PatternMatching --no_extract FStar.Tactics.Typeclasses --no_extract FStar.Tactics.Util --no_extract FStar.UInt

# --use_native_int?
codegen:
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(FSTAR_MORESTUFF) --odir out --codegen OCaml Main.fst




# main_ml: AbstractDomain.ml CSet.ml CSetPO.ml DefaultValue.ml EnumerableMap.ml ExtInt.ml GaloisConnection.ml Interval.ml Main.ml Misc.ml PartialOrder.ml StaticAnalyser.ml ToString.ml ToyLanguageDef.ml ToyLanguageInterpreter.ml ZeroOrLess.ml
# 	echo $(OCAMLOPT)
# 	$(OCAMLOPT) out/Main.ml -o Main.exe
# 	./Main.exe
# main: main_fst main_ml

# %.fst.checked:
# 	$(FSTAR) $< --cache_checked_modules

# %.fsti.checked:
# 	$(FSTAR) $< --cache_checked_modules

# %.ml:
# 	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml --extract_module $(basename $(notdir $(subst .checked,,$<))) --cmi

# .depend:
# 	$(FSTAR) --dep full $(ROOTS) --cmi > .depend

# depend: .depend


# verify-all: $(addsuffix .checked, $(ALL_FST_FILES))

# %.checked:
# 	$(FSTAR) --cache_checked_modules $<

# $(EXEC): $(OBJS)
# 	$(CAMLOPT) -o $(EXEC) $(LIBS) $(OBJS)

# .depend: codegen
# 	$(CAMLDEP) *.mli *.ml > .depend

# depend: codegen
# 	$(CAMLDEP) *.mli *.ml > .depend

# include .depend

clean:
	rm -f .depend *.checked
	rm -rf out
