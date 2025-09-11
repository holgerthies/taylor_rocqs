# Solving analytic initial value problems in Rocq

## Overview
This artifact provides a Rocq/Coq formalization of a constructive Taylor-series solver for multivariate analytic ordinary differential equations, together with small demonstrations and reproducible runs.

## Tested environment
The development has been tested with **Coq (Rocq) 8.20.1**.  
The **coq-interval** library is equired for the interval backend,
all other files only depend on the standard library.

## Building the project
From the repository root, generate a Makefile and build:
```bash
coq_makefile -f _CoqProject -o Makefile
make -j
```
## Repository contents
- `_CoqProject` — lists the core library files (example files are not included here).
- `demo.v` — a minimal usage walkthrough.
- `cauchyreal_examples.v` — additional runs and timing measures over exact reals.
- `interval_examples.v` — same for the coq-interval backend.
- `benchmarks/` — raw outputs from executing the examples. The logs correspond to the runs reported in the paper.


