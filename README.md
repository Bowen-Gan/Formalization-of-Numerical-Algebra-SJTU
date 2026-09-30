# Formalization of Numerical Algebra — SJTU

Lean 4 code from a collaborative numerical-algebra formalization project at the Shanghai Jiao Tong University summer school in Summer 2025. The project explores how algorithms and results from numerical linear algebra can be expressed and proved using Lean and mathlib.

## Background and provenance

This repository is a public copy of materials from an originally private team project, shared by Bowen Gan with the project lead's permission. The materials are collaborative work by the summer-school participants. Bowen Gan participated in the eight-person Gaussian-elimination group, which worked on this component over two weeks.

## Contents

The uploaded materials retain four separate Lean project directories, each with its own Lake configuration and dependency manifest.

| Directory | Main contents |
| --- | --- |
| [`Gaussian_elimination-main`](Gaussian_elimination-main) | Gaussian elimination, elementary matrix operations, row spaces, rank normal forms, and matrix factorizations; also contains ADMM material and earlier drafts. |
| [`CG-main`](CG-main) | Conjugate gradient and steepest descent, with supporting matrix definitions. |
| [`Iterative-main`](Iterative-main) | A separate snapshot containing iterative-method definitions and related drafts. |
| [`Na-main`](Na-main) | A broader collection covering stationary iterations, convergence, Jacobi, Gauss–Seidel, SOR, diagonal dominance, and copies of the Gaussian-elimination and conjugate-gradient work. |

For the Gaussian-elimination component, start with [`Gaussian_elimination.lean`](Gaussian_elimination-main/NumericalAlgrebra/Gaussian_elimination.lean). It contains algorithm definitions and arguments concerning elementary transformations, row-space invariance, and rank and factorization results.

## Working with the code

Install Lean through [elan](https://github.com/leanprover/elan), then clone this repository. All four projects specify `leanprover/lean4:v4.22.0-rc3`; their `lake-manifest.json` files record the dependency revisions. Preserve these manifests when reproducing the original environment.

To inspect the Gaussian-elimination file:

```sh
git clone https://github.com/Bowen-Gan/Formalization-of-Numerical-Algebra-SJTU.git
cd Formalization-of-Numerical-Algebra-SJTU/Gaussian_elimination-main
lake exe cache get
lake env lean NumericalAlgrebra/Gaussian_elimination.lean
```

Open the relevant project directory in VS Code with the Lean 4 extension for interactive inspection. Each directory is a separate Lake project; there is no repository-wide Lake configuration.

## Status

These materials preserve the summer-school project as uploaded, including unfinished proofs and draft files. Several files contain `sorry`, and the diagonal-dominance material also includes explicit axioms. Some root modules import missing files or only a starter module, so a default `lake build` does not provide a complete check of all the uploaded material. In particular, `Na-main/Na.lean` imports `Na.Jacobi.Theorem_4_2_6.Theorem_4_2_6_lemmas`, which is absent from this copy.

The commands above describe how to inspect the code, rather than certify a successful build. Lean accepts `sorry` with a warning; any result relying on a placeholder or an added axiom requires further proof work before it can be treated as fully verified.
