# Coq's guard checker implemented in MetaCoq

This repository contains the guard checker of Coq implemented in Coq,
using the MetaCoq project, as part of Yee-Jian Tan's M1 internship in Cambium, Inria Paris,
supervised by Yannick Forster.

## Installation
```sh
opam switch create metacoq-guard --packages="ocaml-variants.4.14.1+options,ocaml-option-flambda"
eval $(opam env --switch=metacoq-guard)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin -n -y "https://github.com/MetaCoq/metacoq.git#v1.3.2-8.19"
opam install coq-metacoq-template coq-metacoq-utils
make -j
```

## Usage

```coq
From MetaCoq.Guarded Require Import plugin.
From MetaCoq Require Import Utils.bytestring.

Open Scope bs.

(* define your fixpoint *)
Fixpoint add (m n : nat) : nat :=
  match m with
  | O => n
  | S m' => add m' (S n)
  end.

MetaCoq Run (check_fix add).
(* accepts a boolean flag on the expected guardedness. *)
MetaCoq Run (check_fix_ci true add).
```

## Credits

This project is based on https://github.com/lgaeher/metacoq/blob/guarded/README_project.md.

