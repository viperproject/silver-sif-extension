This repository contains an extension of the Viper language with modular product programs and information flow specifications according to [this paper](http://pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=EilersMuellerHitz18.pdf).

In particular, this means
- Viper AST node extensions for information flow specifications (SIFLowExp, SIFLowEvent, SIFDeclassifyStmt) in SifAstExtensions.scala
- additional control flow structures for the Viper AST (e.g., try/catch, raise, return, break) to replace goto statements in SifAstExtensions.scala
- additional Viper verification error types in SifError.scala
- a transformation from an extended Viper AST to its product version in the ordinary Viper AST, including some optimizations, in SifExtendedTransformer.scala

Code for extracting counterexamples from product programs in conjunction with the Silicon backend can be found [here](https://github.com/viperproject/silicon-sif-extension).
