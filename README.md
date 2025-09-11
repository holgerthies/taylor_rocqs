# Solving analytic initial value problems in Rocq

## Overview
This artifact provides a Rocq/Coq formalization of a constructive Taylor-series solver for multivariate analytic ordinary differential equations, together with small demonstrations and reproducible runs.

## Tested environment
The development has been tested with **Coq 8.20.1**.  
The [**coq-interval**](https://github.com/coq-community/coq-interval) library is required for the interval backend.
All other files depend only on the Coq standard library.

## Building the project
From the repository root, generate a Makefile and build:
```bash
coq_makefile -f _CoqProject -o Makefile
make -j
```
### Running examples and benchmarks

The following example files illustrate the solver and reproduce the benchmark runs.
They can be compiled directly with `coqc` or opened interactively in your preferred Coq IDE.

- **Minimal demo:**

    ````bash
    coqc -R . TR demo.v
    ````

- **Exact reals (Cauchy reals):**

    ````bash
    coqc -R . TR cauchyreal_examples.v
    ````

- **Interval backend:**

    ````bash
    coqc -R . TR interval_examples.v
    ````

Benchmark logs corresponding to these runs are provided in the `benchmarks/`
directory.

## Repository contents
- `_CoqProject` — lists the core library files (example files are not included here).
- `demo.v` — a minimal usage example.
- `cauchyreal_examples.v` — additional runs and timing measures over exact reals.
- `interval_examples.v` — same for the coq-interval backend.
- `benchmarks/` — raw outputs from executing the examples. The logs correspond to the runs reported in the paper.


