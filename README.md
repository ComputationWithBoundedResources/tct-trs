[![Build Status](https://travis-ci.org/ComputationWithBoundedResources/tct-trs.svg?branch=master)](https://travis-ci.org/ComputationWithBoundedResources/tct-trs)


tct-trs
=======

This package is part of the _Tyrolean Complexity Tool (TcT)_ and provides
automatic complexity analysis of _Term Rewrite Systems (TRSs)_.

Requirements
------------

  * [Glasgow Haskell Compiler, version >=7.8](http://www.haskell.org/ghc/)
  * [minismt, version 0.6](http://cl-informatik.uibk.ac.at/software/minismt/)
      * requires ttt2, version >= 1.15 (we recommend the latest version
        available at the
        [repository](http://cl2-informatik.uibk.ac.at/mercurial.cgi/ttt2/), as
        there were some compilation problems with the latest available spin-of
        version 1.15)
  * [slogic](https://github.com/ComputationWithBoundedResources/slogic/)
  * [tct-core](https://github.com/ComputationWithBoundedResources/tct-core/)
  * [tct-common](https://github.com/ComputationWithBoundedResources/tct-common/)
  * [tct-trs](https://github.com/ComputationWithBoundedResources/tct-trs/)
  * [term-rewriting-xml](https://github.com/ComputationWithBoundedResources/term-rewriting-xml/)

The tool is only tested under GNU/Linux.


Pitfalls
--------

On default MiniSmt compilation wants to create a static binary. In case it does
not work (you might not have the needed libraries installed), comment out the
STATIC variable of the miniSmt Makefile. camlidl for ttt2 is available at
http://caml.inria.fr/pub/old_caml_site/camlidl/. ttt2 needs to be compiled in
order to provide the module 'Parsec' to MiniSmt.


Installation using Cabal
------------------------

For building, you need
[ghc](http://www.haskell.org/ghc/) and [cabal](http://www.haskell.org/cabal/).
Execute following bash commands to install the packages and executables via
`cabal`.

    mkdir tct-bundle
    cd tct-bundle
    git clone https://github.com/ComputationWithBoundedResources/slogic
    git clone https://github.com/ComputationWithBoundedResources/tct-core
    git clone https://github.com/ComputationWithBoundedResources/tct-common
    git clone https://github.com/ComputationWithBoundedResources/tct-trs
    git clone https://github.com/ComputationWithBoundedResources/term-rewriting-xml
    cabal install **/*.cabal

Usage
-----

The installation provides an executable `tct-trs`. For full options, run
`tct-trs --help`.


Known error codes and solutions
-------------------------------


    Fatal error: the file '/usr/local/bin/camlidl' is not a bytecode executable file

camlidl was compiled with a different version of OCaml and has to be recompiled
(and installed).


    File "src/pb2cnf.ml", line 24, characters 11-30:
    Error: Unbound module Parsec

You need to compile ttt2 first.


    File "src/util/src/util.ml", line 1:
    Error: The implementation src/util/src/util.ml
           does not match the interface src/util/build/util.cmi:
           ...
           In module Arg:
           Values do not match:
             val align :
               ?limit:int -> (key * spec * doc) list -> (key * spec * doc) list
           is not included in
             val align : (key * spec * doc) list -> (key * spec * doc) list
    mk/subdir.mk:72: recipe for target 'src/util/build/util.cmx' failed
    make: *** [src/util/build/util.cmx] Error 2


The archive provided on the homepage sometimes creates that error when being
compiled. Rather use the latest version of ttt2, which is available at
http://cl2-informatik.uibk.ac.at/mercurial.cgi/ttt2/


    /usr/bin/ld: cannot find -lgmp
    /usr/lib/ocaml/libasmrun.a(unix.o): In function `caml_dlopen':
    (.text+0x1d7): warning: Using 'dlopen' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(initgroups.o): In function `unix_initgroups':
    (.text+0x8): warning: Using 'initgroups' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getgr.o): In function `unix_getgrgid':
    (.text+0xfc): warning: Using 'getgrgid' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getgr.o): In function `unix_getgrnam':
    (.text+0xd9): warning: Using 'getgrnam' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getpw.o): In function `unix_getpwnam':
    (.text+0x139): warning: Using 'getpwnam' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getpw.o): In function `unix_getpwuid':
    (.text+0x15c): warning: Using 'getpwuid' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getaddrinfo.o): In function `unix_getaddrinfo':
    (.text+0x224): warning: Using 'getaddrinfo' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(gethost.o): In function `unix_gethostbyaddr':
    (.text+0x1b6): warning: Using 'gethostbyaddr_r' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(gethost.o): In function `unix_gethostbyname':
    (.text+0x22e): warning: Using 'gethostbyname_r' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getproto.o): In function `unix_getprotobynumber':
    (.text+0xd0): warning: Using 'getprotobynumber' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getproto.o): In function `unix_getprotobyname':
    (.text+0xad): warning: Using 'getprotobyname' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getserv.o): In function `unix_getservbyname':
    (.text+0xe0): warning: Using 'getservbyname' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    /usr/lib/ocaml/libunix.a(getserv.o): In function `unix_getservbyport':
    (.text+0x10a): warning: Using 'getservbyport' in statically linked applications requires at runtime the shared libraries from the glibc version used for linking
    collect2: error: ld returned 1 exit status
    File "caml_startup", line 1:
    Error: Error during linking
    Makefile:111: recipe for target 'native' failed
    make: *** [native] Error 2


Disable static compilation of MiniSmt as you do not have the required libraries
available. To do so just comment out the /STATIC/ variable in the Makefile of
MiniSmt.

    src/Tct/Core/Data/Forks.hs:21:40:
    Cannot derive well-kinded instance of form `Foldable (Judgement ...)'
    Class `Foldable' expects an argument of kind `* -> *'
    In the data declaration for `Judgement'

    src/Tct/Core/Data/Forks.hs:49:49:
    Cannot derive well-kinded instance of form `Foldable (Optional ...)'
    Class `Foldable' expects an argument of kind `* -> *'
    In the data declaration for `Optional'
    Failed to install tct-core-3.0.0
    Configuring term-rewriting-xml-0.1.0.0...
    Building term-rewriting-xml-0.1.0.0...
    Preprocessing library term-rewriting-xml-0.1.0.0...
    [1 of 3] Compiling Data.Rewriting.Term.Xml ( src/Data/Rewriting/Term/Xml.hs,
    dist/build/Data/Rewriting/Term/Xml.o ) [flags changed]
    [2 of 3] Compiling Data.Rewriting.Rule.Xml ( src/Data/Rewriting/Rule/Xml.hs,
    dist/build/Data/Rewriting/Rule/Xml.o ) [flags changed]
    [3 of 3] Compiling Data.Rewriting.Problem.Xml (
    src/Data/Rewriting/Problem/Xml.hs, dist/build/Data/Rewriting/Problem/Xml.o )
    [flags changed]
    In-place registering term-rewriting-xml-0.1.0.0...
    Creating package registration file:
    /tmp/pkgConf-term-rewriting-xml-0.1.08599.0
    Installing library in
    /home/alm/.cabal/lib/x86_64-linux-ghc-7.6.3/term-rewriting-xml-0.1.0.0
    Registering term-rewriting-xml-0.1.0.0...
    Installed term-rewriting-xml-0.1.0.0
    cabal: Error: some packages failed to install:
    tct-common-3.0.0 depends on tct-core-3.0.0 which failed to install.
    tct-core-3.0.0 failed during the building phase. The exception was:
    ExitFailure 1
    tct-trs-3.0.0 depends on tct-core-3.0.0 which failed to install.


You need at least ghc-7.8 for TcT!


