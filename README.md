# FStarToyStaticAnalyser

Brief description of main modules

 - [ToyLanguageDef](ToyLanguageDef.fst): defines the WHILE-like language
 - [GaloisConnection](GaloisConnection.fst): defines a `hasGaloisConnection` class
 - [AbstractDomain](AbstractDomain.fst): defines a what an abstract domain is
 - [StaticAnalyser](StaticAnalyser.fst): core of the analyser
 - [CSet](CSet.fst): enumerable non-ordered sets

## Compiling to native
Just run:
```
make clean
make all
```

This will clean, build and execute the analyser.

Then run `make exec` to run the analyser again.

The analyser look at `*.c` files in the folder `prog-example`. For each file `file`, it produces:
 - `file.ast`: the abstract syntax tree of a program
 - `file.pp`: the pretty-printed version of a program
 - `file.result`: the resulting analysis
