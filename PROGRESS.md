# Progress

## Done

- `Challenge.lean` (draft, not yet reviewed by the author): a translation of Sections 1–5 of
  `notes/informal-statements.tex` into Lean, importing only Mathlib. It compiles with
  `lake env lean Challenge.lean`.
- Orthogonality (1.12) and the pairing of Section 1(iii) now use `∫ Re(h ∂_{x_j}W̄)` and require
  only the real part to be integrable, in both the note and `Challenge.lean` (approved by the
  author, 24 Nov 2026). The previous version required `h ∂_{x_j}W̄` itself to be integrable, which
  does not follow from `‖h‖_** < ∞`.

- (A2) is stated for bounded domains (`IsConnected Ω`, which includes nonemptiness) with exterior
  discs of positive radius, in both the note and `Challenge.lean`. (A4) keeps the pointwise
  conclusion `P u = f` (approved by the author, 24 Nov 2026).

## Next

- Author review of the rest of `Challenge.lean`.

## Remaining `sorry`s

- `Challenge.lean`: `GLChallenge.exists_solution_of_orthogonal` (Theorem A) and
  `GLChallenge.exists_solution` (Theorem B). These are the challenge statements and stay `sorry`
  by design; `Solution.lean` will prove them.
