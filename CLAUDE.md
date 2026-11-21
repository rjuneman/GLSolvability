# GLSolvability: instructions for AI assistants

This repository is a Lean 4 formalisation of

> M. del Pino, R. Juneman, M. Musso, *Solvability for the Ginzburg-Landau equation
> linearized at the degree-one vortex*, J. Funct. Anal. 289 (2025) 111105.

The target is Theorem 1.1 of that paper. The human author supervises; you write the Lean code.

## Versions

- Lean `v4.33.1`, Mathlib `v4.33.1` (pinned in `lean-toolchain` and `lake-manifest.json`).
- Never change `lean-toolchain`, `lakefile.toml` or `lake-manifest.json` without asking.

## Layout

- `GLSolvability/Statements/`: definitions and public statements (main theorem, principal
  intermediate results), one declaration per file. **Reviewed and approved by the author.**
- `GLSolvability/Proofs/`: short files, each proving one public statement from `Infra`.
- `GLSolvability/Infra/`: the supporting library, organised by paper section.
- `GLSolvability/Mathlib/`: general results that belong in Mathlib. Mirror Mathlib's paths:
  a candidate for `Mathlib/A/B/C.lean` lives at `GLSolvability/Mathlib/A/B/C.lean`.
- `Challenge.lean`, `Solution.lean` (top level, added later): the main theorem restated using
  only Mathlib, checked by the comparator.
- `blueprint/` (added later): the LaTeX blueprint.

## Rules

1. **Never change a statement without approval.** Do not edit anything in
   `GLSolvability/Statements/`, `Challenge.lean` or `Solution.lean`'s statement, and do not
   change the meaning of any public definition, without asking first. If a proof seems to need
   a different statement, stop and explain why.
2. **No new axioms.** Never use `axiom`, `@[implemented_by]` tricks, `native_decide`, or
   anything that adds assumptions. Unfinished proofs use `sorry` and are reported.
3. **Assumed results are explicit hypotheses**, collected in the places agreed with the author,
   never hidden inside a proof or definition.
4. **Mathematical problems come to the author.** If a step in the paper looks wrong,
   incomplete or ambiguous, stop and describe it. Do not work around it silently.
5. **Build before every commit.** Run `lake build` and fix all errors. Run `lake exe mk_all`
   after adding or removing files, so `GLSolvability.lean` imports everything (CI checks this).
6. **Small commits.** One task per commit, with a plain message such as
   "Add mode k = 0 ODE lemmas". Do not push; the author reviews and pushes.
7. **Keep `PROGRESS.md` up to date**: what was done, what is next, and every remaining `sorry`.

## Conventions

- Follow Mathlib style: naming conventions, `theorem` for propositions, docstrings on every
  public definition and theorem.
- Every new file starts with:

  ```lean
  /-
  Copyright (c) 2026 Rowan Juneman. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Rowan Juneman
  -/
  ```
- Keep files under about 1,000 lines; split them by topic.
- Refer to the paper's numbering in docstrings, e.g. "Lemma 3.5 of the paper".
- Prefer existing Mathlib results to new ones; search before proving.

## Useful commands

- `lake exe cache get`: download precompiled Mathlib.
- `lake build`: build the project.
- `lake exe mk_all`: regenerate the import list in `GLSolvability.lean`.
