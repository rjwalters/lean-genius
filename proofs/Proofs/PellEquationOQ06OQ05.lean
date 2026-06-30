/-
Pell's Equation OQ-06-OQ-05: The Determinant (Cassini) Structure of the
Negative-Pell Chain

The parent entry (`pell-equation-oq-06`) builds the explicit chain `negPellSeq`
of solutions of `x² − 2y² = −1`, starting from `(1, 1)` and iterating the form
automorphism `(x, y) ↦ (3x + 4y, 2x + 3y)`. Sibling entries describe that chain
in three different ways:

  • `oq-06-oq-01` — *which* pairs occur (classification by descent);
  • `oq-06-oq-02` — its *algebraic* nature (the odd powers `ζ^(2n+1)` of the
    fundamental unit `ζ = 1 + √2` of `ℤ[√2]`);
  • `oq-06-oq-03` — its *recurrence* (`uₙ₊₂ = 6uₙ₊₁ − uₙ`);
  • `oq-06-oq-04` — its *analytic* meaning (best rational approximations of √2).

This entry adds the **determinant / lattice** view, which none of the others
record. Writing `(xₙ, yₙ) = negPellSeq n`, the 2×2 determinant of two
*consecutive* solution vectors is a constant, independent of `n`:

    D(n) := xₙ · yₙ₊₁ − xₙ₊₁ · yₙ = −2          (negPellSeq_det)

This is the Cassini-type identity for the chain: the solution vectors
`(xₙ, yₙ)` march along a fixed-determinant path, each consecutive pair spanning
a sublattice of `ℤ²` of index `2`. There is a companion "inner product" identity

    xₙ₊₁ · xₙ − 2 · yₙ₊₁ · yₙ = −3              (negPellSeq_inner)

and together they package the conceptual one-line source of both: in `ℤ[√2]`,

    aₙ₊₁ · conj(aₙ) = ⟨−3, −2⟩ = −ζ²            (negPellSeq_mul_conj)

where `aₙ = ⟨xₙ, yₙ⟩ = ζ^(2n+1)` (the `oq-06-oq-02` representation) and `conj`
is the quadratic conjugation `⟨x, y⟩ ↦ ⟨x, −y⟩`. Indeed
`aₙ₊₁·conj(aₙ) = ζ^(2n+3)·conj(ζ)^(2n+1) = ζ²·(ζ·conj ζ)^(2n+1)
= ζ²·N(ζ)^(2n+1) = −ζ²`, whose real/imaginary parts are exactly the two scalar
identities. As an immediate consequence, every solution of the chain is
**primitive**: `gcd(xₙ, yₙ) = 1` (`negPellSeq_isCoprime`), since any common
divisor divides `x² − 2y² = −1`.

Main results:
  • `negPellSeq_det`        — D(n) = xₙ·yₙ₊₁ − xₙ₊₁·yₙ = −2 (constant determinant).
  • `negPellSeq_inner`      — xₙ₊₁·xₙ − 2·yₙ₊₁·yₙ = −3 (companion identity).
  • `negPellSeq_det_matrix` — the Mathlib `Matrix` form: `det !![xₙ, xₙ₊₁; yₙ, yₙ₊₁] = −2`.
  • `negPellSeq_mul_conj`   — the conceptual source `aₙ₊₁ · conj(aₙ) = −ζ²` in ℤ[√2].
  • `negPellSeq_isCoprime`  — every chain solution `(xₙ, yₙ)` is primitive.

All proofs are `sorry`-free and axiom-free (no `native_decide`). The two scalar
identities are pure `linear_combination` consequences of the parent's norm
relation `negPellSeq_norm` together with the step map `negPellSeq_succ` — no
induction is needed, because the determinant of consecutive vectors collapses to
a fixed multiple of the (constant) norm.

References:
- Parent entry: `pell-equation-oq-06` (the chain; `negPellSeq`, `negPellSeq_norm`).
- Sibling: `pell-equation-oq-06-oq-02` (`ζ`, `ζ_sq`, `negPellSeq_eq_pow`).
- Mathlib `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (`Zsqrtd`, `Zsqrtd.re_mul`,
  `Zsqrtd.im_mul`), `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
  (`Matrix.det_fin_two_of`), `Mathlib/RingTheory/Coprime/Basic.lean` (`IsCoprime`).
-/

import Mathlib
import Proofs.PellEquationOQ06
import Proofs.PellEquationOQ06OQ02

namespace PellEquationOQ06OQ05

open PellEquationOQ06
open PellEquationOQ06OQ02

/-
## The constant-determinant (Cassini) identity
-/

/-- **The determinant of two consecutive solution vectors is the constant −2.**
    With `(xₙ, yₙ) = negPellSeq n`,
    `xₙ·yₙ₊₁ − xₙ₊₁·yₙ = 2·(xₙ² − 2yₙ²) = 2·(−1) = −2`. No induction is needed:
    the step map `negPellSeq_succ` turns the determinant into a fixed multiple of
    the (constant) negative-Pell norm `negPellSeq_norm`. -/
theorem negPellSeq_det (n : ℕ) :
    (negPellSeq n).1 * (negPellSeq (n + 1)).2
      - (negPellSeq (n + 1)).1 * (negPellSeq n).2 = -2 := by
  rw [negPellSeq_succ]
  dsimp
  linear_combination 2 * negPellSeq_norm n

/-- **The companion "inner product" identity.** With `(xₙ, yₙ) = negPellSeq n`,
    `xₙ₊₁·xₙ − 2·yₙ₊₁·yₙ = 3·(xₙ² − 2yₙ²) = 3·(−1) = −3`. -/
theorem negPellSeq_inner (n : ℕ) :
    (negPellSeq (n + 1)).1 * (negPellSeq n).1
      - 2 * ((negPellSeq (n + 1)).2 * (negPellSeq n).2) = -3 := by
  rw [negPellSeq_succ]
  dsimp
  linear_combination 3 * negPellSeq_norm n

/-
## The Mathlib `Matrix` form
-/

open Matrix in
/-- **Matrix form of the Cassini identity.** The `2×2` integer matrix whose
    columns are the consecutive solution vectors `(xₙ, yₙ)` and `(xₙ₊₁, yₙ₊₁)`
    has determinant `−2`, for every `n`. -/
theorem negPellSeq_det_matrix (n : ℕ) :
    Matrix.det !![(negPellSeq n).1, (negPellSeq (n + 1)).1;
                  (negPellSeq n).2, (negPellSeq (n + 1)).2] = -2 := by
  rw [Matrix.det_fin_two_of]
  linear_combination negPellSeq_det n

/-
## The conceptual source in ℤ[√2]
-/

/-- **The single algebraic identity behind both scalar identities.** With
    `aₙ = ⟨xₙ, yₙ⟩ = ζ^(2n+1)` (entry `oq-06-oq-02`) and the quadratic
    conjugate `conj⟨x, y⟩ = ⟨x, −y⟩`, one has

        aₙ₊₁ · conj(aₙ) = ⟨−3, −2⟩ = −ζ².

    Its real part is `negPellSeq_inner` and its imaginary part is
    `negPellSeq_det`. Conceptually:
    `aₙ₊₁·conj(aₙ) = ζ²·(ζ·conj ζ)^(2n+1) = ζ²·N(ζ)^(2n+1) = −ζ²`. -/
theorem negPellSeq_mul_conj (n : ℕ) :
    (⟨(negPellSeq (n + 1)).1, (negPellSeq (n + 1)).2⟩ : ℤ√2)
        * ⟨(negPellSeq n).1, -(negPellSeq n).2⟩ = -ζ ^ 2 := by
  have hdet := negPellSeq_det n
  have hin := negPellSeq_inner n
  rw [ζ_sq]
  refine Zsqrtd.ext ?_ ?_
  · simp only [Zsqrtd.re_mul, Zsqrtd.re_neg]
    linear_combination hin
  · simp only [Zsqrtd.im_mul, Zsqrtd.im_neg]
    linear_combination hdet

/-
## Primitivity of the chain solutions
-/

/-- **Every chain solution is primitive:** `gcd(xₙ, yₙ) = 1`. Any common divisor
    of `xₙ` and `yₙ` divides `xₙ² − 2yₙ² = −1`, hence is a unit. Concretely,
    `(−xₙ)·xₙ + (2yₙ)·yₙ = −(xₙ² − 2yₙ²) = 1` exhibits a Bézout identity. -/
theorem negPellSeq_isCoprime (n : ℕ) :
    IsCoprime (negPellSeq n).1 (negPellSeq n).2 :=
  ⟨-(negPellSeq n).1, 2 * (negPellSeq n).2, by linear_combination -negPellSeq_norm n⟩

/-
## Explicit small values (sanity checks)
-/

-- `(x₀, y₀) = (1, 1)`, `(x₁, y₁) = (7, 5)`: `1·5 − 7·1 = −2`, `7·1 − 2·5·1 = −3`.
example : (negPellSeq 0).1 * (negPellSeq 1).2 - (negPellSeq 1).1 * (negPellSeq 0).2 = -2 :=
  negPellSeq_det 0
example : (negPellSeq 1).1 * (negPellSeq 0).1 - 2 * ((negPellSeq 1).2 * (negPellSeq 0).2) = -3 :=
  negPellSeq_inner 0

#check @negPellSeq_det
#check @negPellSeq_inner
#check @negPellSeq_det_matrix
#check @negPellSeq_mul_conj
#check @negPellSeq_isCoprime

end PellEquationOQ06OQ05
