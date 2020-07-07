## tct-trs
This package is part of the _Tyrolean Complexity Tool (TcT)_ and provides
automatic complexity analysis of _Term Rewrite Systems (TRSs)_.

This repository provides the `tct-trs` library as well as the `tct-trs` executable.

### Requirements

Executables:
  * [Glasgow Haskell Compiler, version 7.10](http://www.haskell.org/ghc/)
  * [minismt, version 0.6](http://cl-informatik.uibk.ac.at/software/minismt/) or [z3, version 4.3](https://github.com/Z3Prover/z3)
    * We recommend using `minismt`. If you want to use `z3`, see [how to set up z3](#how-to-set-up-z3?).

Other packages:
  * [slogic](https://github.com/ComputationWithBoundedResources/slogic/)
  * [tct-core](https://github.com/ComputationWithBoundedResources/tct-core/)
  * [tct-common](https://github.com/ComputationWithBoundedResources/tct-common/)
  * [term-rewriting-xml](https://github.com/ComputationWithBoundedResources/term-rewriting-xml/)

The tool is only tested under GNU/Linux.


### Installation

#### Using Stack
We recommend using [stack](https://github.com/commercialhaskell/stack) with the accompanied `stack-XXX.yaml` file.
To build and install the package run following command:

```bash
stack install tct-trs
```

#### Using Cabal
For building via `cabal/cabal-install`, make sure that you have [ghc](http://www.haskell.org/ghc/) and [cabal](http://www.haskell.org/cabal/).
To build and install the package run following commands:

```bash
mkdir tct-bundle
cd tct-bundle
git clone https://github.com/ComputationWithBoundedResources/slogic
git clone https://github.com/ComputationWithBoundedResources/tct-core
git clone https://github.com/ComputationWithBoundedResources/tct-common
git clone https://github.com/ComputationWithBoundedResources/tct-trs
git clone https://github.com/ComputationWithBoundedResources/term-rewriting-xml
cabal install **/*.cabal tct-trs
```

### Example Usage
The installation provides an executable `tct-trs`.

```bash
tct-trs --complexity rci examples/RaML/minsort.raml.trs
```

For full options, run `tct-trs --help`.

### FAQ

##### Q:How to set up z3?

To use `z3`, you have to update the default configuration and re-install the executable.

```haskell
module Main (main) where

import Tct.Trs.Config

main :: IO ()
main = trs $ trsConfig `setSolver` ("z3",[])
```

