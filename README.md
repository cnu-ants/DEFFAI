# DEFFAI

## Requirements

  * OCaml, version 4.13.1 or later.  

## Installation

1) Building from source
```
  opam install .
  dune build
```

## Usage
```
  ./_build/default/transformer/transformer.exe <.bc file> <target function> <k> <loop-count threshold> <.ll output file> ''
```
