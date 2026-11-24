/-
Copyright (c) 2026 Rowan Juneman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rowan Juneman
-/
import Mathlib

/-!
# Challenge: solvability for the Ginzburg–Landau equation linearized at the degree-one vortex

This file states Theorem 1.1 and Remark 1.2 of

> M. del Pino, R. Juneman, M. Musso, *Solvability for the Ginzburg-Landau equation
> linearized at the degree-one vortex*, J. Funct. Anal. 289 (2025) 111105

as Theorems A and B of `notes/informal-statements.tex` ("the note"), using only Mathlib.
It is a direct translation of Sections 1–5 of the note; the section headings below follow
the note.

## Conventions

* The plane `ℝ²` is `EuclideanSpace ℝ (Fin 2)`. The coordinate `x₁` of the note is `x 0` and
  `x₂` is `x 1`; likewise `∂_{x₁}` is `partialDeriv 0` and `∂_{x₂}` is `partialDeriv 1`.
* `ℝ^m` is `EuclideanSpace ℝ (Fin m)`, and an `m × m` real matrix is a continuous linear map
  `ℝ^m →L[ℝ] ℝ^m`, measured in the operator norm.
* A function that the note defines only on a set `Ω` is a function on all of `ℝ²` here; only
  its values on `Ω` (or on `closure Ω`) enter the hypotheses and conclusions.
* `C²(Ω)` (item (iv) of Section 1) is Mathlib's `ContDiffOn ℝ 2 f Ω`. On an open set `Ω` this
  is equivalent to the existence and continuity of all partial derivatives of order at most two.
* Quantities with values in `[0, ∞]` are taken in `ℝ≥0∞`.
-/

open MeasureTheory Filter Asymptotics Metric Set
open scoped ENNReal ContDiff Topology ComplexConjugate RealInnerProductSpace

namespace GLChallenge

/-- The plane, `EuclideanSpace ℝ (Fin 2)` (item (i) of Section 1 of the note). -/
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Euclidean space `ℝ^m`, the codomain in (A3) and (A4). -/
local notation "ℝ^" m:max => EuclideanSpace ℝ (Fin m)

/-! ## Section 1: Setting and notation -/

/-- The partial derivative `∂_{x_{j+1}} f (x)`: the derivative of `f` at `x` in the direction
of the standard basis vector `e_j`. Where `f` is differentiable at `x` (for instance on an open
set where `f` is `C¹`) this is the classical partial derivative; elsewhere it is `0`, by the
convention of Mathlib's `fderiv`. -/
noncomputable def partialDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (j : Fin 2) (f : ℝ² → F) (x : ℝ²) : F :=
  fderiv ℝ f x (EuclideanSpace.single j 1)

/-- The Laplacian `Δ = ∂²_{x₁} + ∂²_{x₂}` (item (ii) of Section 1 of the note), for functions
with values in any real normed space. For `ℂ`-valued functions it acts on real and imaginary parts
separately, and for `ℝ^m`-valued functions componentwise. -/
noncomputable def laplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ² → F) (x : ℝ²) : F :=
  partialDeriv 0 (partialDeriv 0 f) x + partialDeriv 1 (partialDeriv 1 f) x

/-- The pairing `⟨u, v⟩ = ∫_{ℝ²} Re(u v̄) dx` (item (iii) of Section 1 of the note), with respect
to Lebesgue measure on `ℝ²`. It is meaningful only when `Re(u v̄)` is integrable (the integral of
a non-integrable function is `0` in Mathlib); every use below states integrability separately.
When `u v̄` itself is integrable it equals `Re ∫_{ℝ²} u v̄ dx`. -/
noncomputable def pairing (u v : ℝ² → ℂ) : ℝ :=
  ∫ x, (u x * conj (v x)).re

/-- `f` is locally Hölder continuous on `Ω` (item (v) of Section 1 of the note): there is an
exponent `β ∈ (0, 1)` such that for every compact `K ⊆ Ω` there is `C_K` with
`‖f x - f y‖ ≤ C_K ‖x - y‖ ^ β` for all `x, y ∈ K`. The note defines this for `Ω = ℝ²`, which is
`LocallyHolderOn f univ`; (A2) and (A4) use it on an open set `Ω`. -/
def LocallyHolderOn {F : Type*} [NormedAddCommGroup F] (f : ℝ² → F) (Ω : Set ℝ²) : Prop :=
  ∃ β : ℝ, 0 < β ∧ β < 1 ∧ ∀ K ⊆ Ω, IsCompact K →
    ∃ C : ℝ, ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ β

/-! ## Section 2: The vortex profile (assumed properties)

The profile `w` is a function `ℝ → ℝ`; only its values on `[0, ∞)` are ever used. -/

open Classical in
/-- The vortex `W : ℝ² → ℂ`, `W(x) = w(|x|) (x₁ + i x₂) / |x|` for `x ≠ 0` and `W(0) = 0`, that
is `W = w(r) e^{iθ}` (item (P5) of Section 2 of the note). -/
noncomputable def vortex (w : ℝ → ℝ) (x : ℝ²) : ℂ :=
  if x = 0 then 0
  else (w ‖x‖ : ℂ) * ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) / (‖x‖ : ℂ)

/-- (P1): `w ∈ C²((0, ∞))`, `w'' + (1/r) w' - (1/r²) w + (1 - w²) w = 0` on `(0, ∞)`
(equation (1.3) of the paper), `w(0) = 0`, and `w(r) → 1` as `r → ∞`. -/
def ProfileP1 (w : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 w (Ioi 0) ∧
    (∀ r : ℝ, 0 < r →
      deriv (deriv w) r + (1 / r) * deriv w r - (1 / r ^ 2) * w r + (1 - w r ^ 2) * w r = 0) ∧
    w 0 = 0 ∧ Tendsto w atTop (𝓝 1)

/-- (P2): `0 < w(r) < 1` and `w'(r) > 0` for all `r > 0`. -/
def ProfileP2 (w : ℝ → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → 0 < w r ∧ w r < 1 ∧ 0 < deriv w r

/-- (P3): there is `a > 0` with `w(r) = a r + O(r³)` and `w'(r) = a + O(r²)` as `r → 0⁺`. -/
def ProfileP3 (w : ℝ → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧
    (fun r ↦ w r - a * r) =O[𝓝[>] 0] (fun r ↦ r ^ 3) ∧
    (fun r ↦ deriv w r - a) =O[𝓝[>] 0] (fun r ↦ r ^ 2)

/-- (P4): `w(r) = 1 - 1/(2r²) + O(r⁻⁴)` and `w'(r) = r⁻³ + O(r⁻⁵)` as `r → ∞`
(equation (1.4) of the paper). -/
def ProfileP4 (w : ℝ → ℝ) : Prop :=
  (fun r ↦ w r - (1 - 1 / (2 * r ^ 2))) =O[atTop] (fun r : ℝ ↦ 1 / r ^ 4) ∧
    (fun r ↦ deriv w r - 1 / r ^ 3) =O[atTop] (fun r : ℝ ↦ 1 / r ^ 5)

/-- (P5): the vortex `W = w(r) e^{iθ}` is `C^∞` on `ℝ²`. -/
def ProfileP5 (w : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ (vortex w)

/-- Assumption (P) of Section 2 of the note: the profile `w` satisfies (P1)–(P5). -/
structure ProfileAssumptions (w : ℝ → ℝ) : Prop where
  p1 : ProfileP1 w
  p2 : ProfileP2 w
  p3 : ProfileP3 w
  p4 : ProfileP4 w
  p5 : ProfileP5 w

/-- The linearised operator (1.5) of the paper:
`L[φ] = Δφ + (1 - |W|²) φ - 2 Re(W̄ φ) W`. It is used only for `φ ∈ C²(ℝ²)`. -/
noncomputable def linearizedOp (w : ℝ → ℝ) (φ : ℝ² → ℂ) (x : ℝ²) : ℂ :=
  laplacian φ x + ((1 - ‖vortex w x‖ ^ 2 : ℝ) : ℂ) * φ x
    - 2 * ((conj (vortex w x) * φ x).re : ℂ) * vortex w x

/-! ## Section 3: Assumed results from the literature -/

/-- (A1), nondegeneracy ([14, Thm 3.2], [4, Thm 1.1] of the paper): if `φ ∈ C²(ℝ²)` is bounded
and `L[φ] = 0` on `ℝ²`, then `φ = c₀ iW + c₁ ∂_{x₁} W + c₂ ∂_{x₂} W` for some real `c₀, c₁, c₂`. -/
def Nondegeneracy (w : ℝ → ℝ) : Prop :=
  ∀ φ : ℝ² → ℂ, ContDiff ℝ 2 φ → (∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M) →
    (∀ x, linearizedOp w φ x = 0) →
    ∃ c₀ c₁ c₂ : ℝ, ∀ x, φ x = (c₀ : ℂ) * (Complex.I * vortex w x)
      + (c₁ : ℂ) * partialDeriv 0 (vortex w) x + (c₂ : ℂ) * partialDeriv 1 (vortex w) x

/-- The exterior sphere condition of (A2): for every `y ∈ ∂Ω` there is a closed disc `D` of
positive radius with `D ∩ Ω̄ = {y}`. (If radius `0` were allowed, `D = {y}` would always work and
every set would satisfy the condition.) -/
def ExteriorDiscCondition (Ω : Set ℝ²) : Prop :=
  ∀ y ∈ frontier Ω, ∃ z : ℝ², ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ∩ closure Ω = {y}

/-- (A2), the Dirichlet problem for scalar operators (Gilbarg–Trudinger, Theorem 6.13). Let
`Ω ⊆ ℝ²` be a bounded domain (a nonempty, connected, bounded open set; Mathlib's `IsConnected`
includes nonemptiness) satisfying the exterior sphere condition with discs of positive radius,
and let `b : Ω → ℝ²` and `c, f : Ω → ℝ` be bounded and locally Hölder continuous, with `c ≤ 0`.
Then for every continuous `g : ∂Ω → ℝ` there is `u ∈ C²(Ω) ∩ C(Ω̄)` with
`Δu + b · ∇u + c u = f` in `Ω` and `u = g` on `∂Ω`. -/
def DirichletSolvability : Prop :=
  ∀ Ω : Set ℝ², IsOpen Ω → IsConnected Ω → Bornology.IsBounded Ω → ExteriorDiscCondition Ω →
    ∀ (b : ℝ² → ℝ²) (c f : ℝ² → ℝ),
      (∃ M : ℝ, ∀ x ∈ Ω, ‖b x‖ ≤ M) → (∃ M : ℝ, ∀ x ∈ Ω, |c x| ≤ M) →
      (∃ M : ℝ, ∀ x ∈ Ω, |f x| ≤ M) →
      LocallyHolderOn b Ω → LocallyHolderOn c Ω → LocallyHolderOn f Ω →
      (∀ x ∈ Ω, c x ≤ 0) →
      ∀ g : ℝ² → ℝ, ContinuousOn g (frontier Ω) →
        ∃ u : ℝ² → ℝ, ContDiffOn ℝ 2 u Ω ∧ ContinuousOn u (closure Ω) ∧
          (∀ x ∈ Ω, laplacian u x + (b x 0 * partialDeriv 0 u x + b x 1 * partialDeriv 1 u x)
            + c x * u x = f x) ∧
          ∀ y ∈ frontier Ω, u y = g y

/-- The operator `P u = Δu + B₁ ∂_{x₁} u + B₂ ∂_{x₂} u + C u` of Section 3 of the note, acting on
`u : ℝ² → ℝ^m` with matrix-valued coefficients `B₁ = B 0`, `B₂ = B 1` and `C`. -/
noncomputable def ellipticOp {m : ℕ} (B : Fin 2 → ℝ² → (ℝ^m →L[ℝ] ℝ^m))
    (C : ℝ² → (ℝ^m →L[ℝ] ℝ^m)) (u : ℝ² → ℝ^m) (x : ℝ²) : ℝ^m :=
  laplacian u x + B 0 x (partialDeriv 0 u x) + B 1 x (partialDeriv 1 u x) + C x (u x)

/-- (A3), interior gradient estimate: for `m ∈ {1, 2}` and every `Λ > 0` there is `K(Λ)` such
that if the coefficients of `P` are continuous on the unit disc `B₁` with `|B_j|, |C| ≤ Λ` there,
and `u ∈ C²(B₁)` satisfies `P u = f` on `B₁`, then
`|∇u(0)| ≤ K(Λ) (sup_{B₁} |u| + sup_{B₁} |f|)`.

The suprema are expressed through arbitrary upper bounds `U` and `F`; the estimate is trivial
when either supremum is infinite. `|∇u(0)|` is the operator norm of the derivative of `u` at `0`. -/
def InteriorGradientEstimate : Prop :=
  ∀ m : ℕ, (m = 1 ∨ m = 2) → ∀ Λ : ℝ, 0 < Λ → ∃ K : ℝ,
    ∀ (B : Fin 2 → ℝ² → (ℝ^m →L[ℝ] ℝ^m)) (C : ℝ² → (ℝ^m →L[ℝ] ℝ^m)) (u f : ℝ² → ℝ^m),
      (∀ j, ContinuousOn (B j) (ball 0 1)) → ContinuousOn C (ball 0 1) →
      (∀ j, ∀ x ∈ ball (0 : ℝ²) 1, ‖B j x‖ ≤ Λ) → (∀ x ∈ ball (0 : ℝ²) 1, ‖C x‖ ≤ Λ) →
      ContDiffOn ℝ 2 u (ball 0 1) → (∀ x ∈ ball (0 : ℝ²) 1, ellipticOp B C u x = f x) →
      ∀ U F : ℝ, (∀ x ∈ ball (0 : ℝ²) 1, ‖u x‖ ≤ U) → (∀ x ∈ ball (0 : ℝ²) 1, ‖f x‖ ≤ F) →
        ‖fderiv ℝ u 0‖ ≤ K * (U + F)

/-- (A4), regularity of distributional solutions: for `m ∈ {1, 2}` and an open set `Ω ⊆ ℝ²`, let
the coefficients of `P` and `f : Ω → ℝ^m` be locally Hölder continuous, and let `u : Ω → ℝ^m` be
locally Lipschitz and a distributional solution of `P u = f`, that is
`∫_Ω (u · Δη + ∑_j (B_j ∂_{x_j} u) · η + (C u) · η) dx = ∫_Ω f · η dx`
for every `C^∞` function `η : Ω → ℝ^m` with compact support. Then `u ∈ C²(Ω)` and `P u = f`
holds pointwise on `Ω`.

The derivatives `∂_{x_j} u` in the integral are `partialDeriv j u`, which agree with the true
partial derivatives wherever `u` is differentiable, hence almost everywhere on `Ω` by
Rademacher's theorem. A test function `η` is a smooth function on `ℝ²` whose support is compact
and contained in `Ω`. -/
def DistributionalRegularity : Prop :=
  ∀ m : ℕ, (m = 1 ∨ m = 2) → ∀ Ω : Set ℝ², IsOpen Ω →
    ∀ (B : Fin 2 → ℝ² → (ℝ^m →L[ℝ] ℝ^m)) (C : ℝ² → (ℝ^m →L[ℝ] ℝ^m)) (u f : ℝ² → ℝ^m),
      (∀ j, LocallyHolderOn (B j) Ω) → LocallyHolderOn C Ω → LocallyHolderOn f Ω →
      LocallyLipschitzOn Ω u →
      (∀ η : ℝ² → ℝ^m, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ω →
        ∫ x in Ω, (⟪u x, laplacian η x⟫ + (∑ j : Fin 2, ⟪B j x (partialDeriv j u x), η x⟫)
          + ⟪C x (u x), η x⟫) = ∫ x in Ω, ⟪f x, η x⟫) →
      ContDiffOn ℝ 2 u Ω ∧ ∀ x ∈ Ω, ellipticOp B C u x = f x

/-! ## Section 4: Norms and orthogonality -/

/-- The quotient `ψ = φ / (iW)` (Definition "Components" in Section 4 of the note). For
`φ` it gives `ψ₁ = Re ψ` and `ψ₂ = Im ψ`; for `h` it gives `h₁ + i h₂ = h / (iW)`. It is only
evaluated at `x ≠ 0`, where `W(x) ≠ 0` by (P2). -/
noncomputable def psi (w : ℝ → ℝ) (φ : ℝ² → ℂ) (x : ℝ²) : ℂ :=
  φ x / (Complex.I * vortex w x)

/-- The norm `‖φ‖_*` of (1.15), with values in `[0, ∞]`:
`sup_{0 < |x| ≤ 2} |ψ(x)| + sup_{|x| ≥ 2} (log |x|)⁻² |ψ₁(x)| + sup_{|x| ≥ 2} |ψ₂(x)|`. -/
noncomputable def normStar (w : ℝ → ℝ) (φ : ℝ² → ℂ) : ℝ≥0∞ :=
  (⨆ (x : ℝ²) (_ : 0 < ‖x‖ ∧ ‖x‖ ≤ 2), ENNReal.ofReal ‖psi w φ x‖)
    + (⨆ (x : ℝ²) (_ : 2 ≤ ‖x‖), ENNReal.ofReal (|(psi w φ x).re| / Real.log ‖x‖ ^ 2))
    + (⨆ (x : ℝ²) (_ : 2 ≤ ‖x‖), ENNReal.ofReal |(psi w φ x).im|)

/-- The norm `‖h‖_**` of (1.16), with values in `[0, ∞]`:
`sup_{|x| ≤ 2} |h(x)| + sup_{|x| ≥ 2} |x|² |h₁(x)| + sup_{|x| ≥ 2} |h₂(x)|`. -/
noncomputable def normStarStar (w : ℝ → ℝ) (h : ℝ² → ℂ) : ℝ≥0∞ :=
  (⨆ (x : ℝ²) (_ : ‖x‖ ≤ 2), ENNReal.ofReal ‖h x‖)
    + (⨆ (x : ℝ²) (_ : 2 ≤ ‖x‖), ENNReal.ofReal (‖x‖ ^ 2 * |(psi w h x).re|))
    + (⨆ (x : ℝ²) (_ : 2 ≤ ‖x‖), ENNReal.ofReal |(psi w h x).im|)

/-- The orthogonality conditions (1.12): for `j = 1, 2` the function `Re(h ∂_{x_j}W̄)` is
integrable on `ℝ²` and `⟨h, ∂_{x_j} W⟩ = ∫_{ℝ²} Re(h ∂_{x_j}W̄) dx = 0`. Integrability of
`h ∂_{x_j}W̄` itself is not required: when `‖h‖_** < ∞` its imaginary part is in general only
`O(|x|⁻¹)` at infinity. No condition `⟨h, iW⟩ = 0` is imposed. -/
def SatisfiesOrthogonality (w : ℝ → ℝ) (h : ℝ² → ℂ) : Prop :=
  ∀ j : Fin 2, Integrable (fun x ↦ (h x * conj (partialDeriv j (vortex w) x)).re) ∧
    pairing h (partialDeriv j (vortex w)) = 0

/-! ## Section 5: The theorems -/

/-- **Theorem A** of the note (Theorem 1.1 of the paper). Assume (P) and (A1)–(A4). There is a
constant `C > 0` such that for every locally Hölder continuous `h : ℝ² → ℂ` with `‖h‖_** < ∞`
that satisfies the orthogonality conditions, there exists `φ ∈ C²(ℝ²)` with `L[φ] = h` on `ℝ²`
and `‖φ‖_* ≤ C ‖h‖_**`. -/
theorem exists_solution_of_orthogonal (w : ℝ → ℝ) (hP : ProfileAssumptions w)
    (hA1 : Nondegeneracy w) (hA2 : DirichletSolvability) (hA3 : InteriorGradientEstimate)
    (hA4 : DistributionalRegularity) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ² → ℂ, LocallyHolderOn h univ → normStarStar w h < ⊤ →
      SatisfiesOrthogonality w h →
      ∃ φ : ℝ² → ℂ, ContDiff ℝ 2 φ ∧ (∀ x, linearizedOp w φ x = h x) ∧
        normStar w φ ≤ ENNReal.ofReal C * normStarStar w h := by
  sorry

/-- **Theorem B** of the note (Remark 1.2 of the paper). Assume (P) and (A1)–(A4). There is a
constant `C > 0` such that for every locally Hölder continuous `h : ℝ² → ℂ` with `‖h‖_** < ∞`
there exists `φ ∈ C²(ℝ²)` with `L[φ] = h` on `ℝ²`, `sup_{0 < |x| ≤ 2} |ψ(x)| ≤ C ‖h‖_**`, and
`|ψ₁(x)| ≤ C |x| ‖h‖_**`, `|ψ₂(x)| ≤ C ‖h‖_**` for `|x| ≥ 2`. -/
theorem exists_solution (w : ℝ → ℝ) (hP : ProfileAssumptions w)
    (hA1 : Nondegeneracy w) (hA2 : DirichletSolvability) (hA3 : InteriorGradientEstimate)
    (hA4 : DistributionalRegularity) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ² → ℂ, LocallyHolderOn h univ → normStarStar w h < ⊤ →
      ∃ φ : ℝ² → ℂ, ContDiff ℝ 2 φ ∧ (∀ x, linearizedOp w φ x = h x) ∧
        (⨆ (x : ℝ²) (_ : 0 < ‖x‖ ∧ ‖x‖ ≤ 2), ENNReal.ofReal ‖psi w φ x‖)
          ≤ ENNReal.ofReal C * normStarStar w h ∧
        ∀ x : ℝ², 2 ≤ ‖x‖ →
          ENNReal.ofReal |(psi w φ x).re| ≤ ENNReal.ofReal (C * ‖x‖) * normStarStar w h ∧
          ENNReal.ofReal |(psi w φ x).im| ≤ ENNReal.ofReal C * normStarStar w h := by
  sorry

end GLChallenge
