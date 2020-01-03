  { name = "ToyStaticAnalyser";
    sources-directory = ./.;
    sources = [
      "AbstractDomain"
      "CartProdAbs"
      "Congruence"
      "ExtInt"
      "GaloisConnection"
      "Interval"
      "Main"
      "Monad"
      "MyIO"
      # "Printers"
      "StaticAnalyser"
      "TestMetaStar"
      "ToyLanguageDef"
      "ToyLanguageInterpreter"
      "ToyParser"
      "ZeroOrLess"
      # "Zone"
    ];
    ocaml-sources = [
      "MyIO.ml"
    ];
    dependencies =
      with (import /home/lucas/Bureau/Fstar-libs);
      [ ToString
        PartialOrder
        Data.Set.Computable.NonOrdered
        Data.Map.Enumerable.NonOrdered
        (import ./StarCombinator)];
    compile = [{
      module = "Main";
      assets = [];
      binary-name = "main-example-bin";
    }];
  }
