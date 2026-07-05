/-
# RH ⟹ M(x) = O(x^{1/2+ε}):  the honest Perron axiom boundary

This file formalizes the **forward** direction of Littlewood's theorem:

  Assuming the Riemann Hypothesis, the Mertens function
  `M(x) = Σ_{n ≤ x} μ(n)` satisfies `M(x) = O(x^{1/2+ε})` for every `ε > 0`.

**Status: axiomatized** (conditional on RH, which is open).

## Why this file exists alongside the sibling `rh-consequences-oq-03`

The sibling `RiemannHypothesisConsequencesOQ03.lean` also proves the forward
direction, but it derives it from the **`√x` bound** `|M(n)| ≤ C·√n` taken as an
axiom.  That `√x` bound is *strictly stronger* than what RH actually gives, and
is in fact **believed false**: the Mertens conjecture `|M(x)| < √x` was disproved
(Odlyzko–te Riele 1985), and more sharply `limsup M(x)/√x = +∞` is expected, so
no bound of the form `|M(x)| ≤ C·√x` can hold.  Deriving the (true) ε-bound from
a (believed-false) `√x` axiom is logically valid but rests on a false premise.

**This file uses the correct axiom boundary.**  The genuine RH consequence
(Littlewood 1912) factors through Perron's formula *without* ever asserting the
`√x` bound:

* **(P)** — *RH-free.*  Truncated Perron inversion writes `M(n)` as a contour
  integral of `x^s / (s · ζ(s))` along `Re s = 1/2 + ε`, plus a truncation error
  that is unconditionally `O(n^{1/2+ε})`.  We abstract the contour-integral value
  as an opaque function `perronIntegral ε n` and axiomatize the error bound.

* **(Z)** — *carries RH.*  Under RH, `ζ` has no zeros with `Re s > 1/2`, and the
  conditional critical-strip estimate `|1/ζ(1/2+ε+it)| ≪_ε |t|^ε`
  (Titchmarsh, *Theory of the Riemann Zeta-Function*, Thm 14.2) bounds the
  shifted-contour integral itself by `O(n^{1/2+ε})`.

* **Assembly** — *machine-checked here.*  The triangle inequality combines (P)
  and (Z) into `|M(n)| ≤ (C₁+C₂) · n^{1/2+ε}`.  This is the only content beyond
  the two analytic axioms, and it is genuinely verified — see
  `rh_implies_mertens_eps_bound`.

Both analytic inputs (a truncated Perron formula for `L`-series summatory
functions, and a conditional `1/ζ` growth bound) are absent from Mathlib
(each is hundreds of lines and needs Borel–Carathéodory + Hadamard three-circles
machinery), which is why they are stated as axioms rather than proved.

## Correctness note against the parent

The parent `RiemannHypothesisConsequences.lean` states
`axiom rh_implies_mertens_bound : RH → ∃ C, C>0 ∧ ∀ n≥1, |M n| ≤ C·√n`.
By the argument above this **overclaims** — the `√x` form is believed false.
The genuine consequence is the ε-form proved here as `rh_implies_mertens_eps_bound`.
The parent axiom should be softened to the ε-form.  (The ε-form is genuinely
weaker: `√n = n^{1/2} ≤ n^{1/2+ε}` for `n ≥ 1`; this monotonicity step is already
machine-checked in the sibling `oq-03`, so we do not repeat it here.)

Mathlib already provides `RiemannHypothesis`
(`Mathlib/NumberTheory/LSeries/RiemannZeta.lean`) and the Möbius function
`ArithmeticFunction.moebius`.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace RHConsequencesOQ01

open ArithmeticFunction

/-! ## The Mertens function -/

/-- The Mertens function `M(n) = Σ_{k ≤ n} μ(k)` (matching the parent's
definition: `Finset.range (n+1)` sums `k = 0, …, n`, and `μ 0 = 0`). -/
def mertens (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.moebius k

@[simp] theorem mertens_zero : mertens 0 = 0 := by simp [mertens]

theorem mertens_one : mertens 1 = 1 := by
  simp [mertens, Finset.sum_range_succ]

/-- Recurrence: `M(n+1) = M(n) + μ(n+1)`. -/
theorem mertens_step (n : ℕ) :
    mertens (n + 1) = mertens n + ArithmeticFunction.moebius (n + 1) := by
  simp [mertens, Finset.sum_range_succ]

/-! ## The abstract truncated Perron integral

`perronIntegral ε n` stands for the truncated contour integral
`(1 / 2πi) ∫_{1/2+ε-iT}^{1/2+ε+iT} n^s / (s · ζ(s)) ds` with truncation height
`T = n`.  Its analytic construction is the Mathlib gap; we keep it opaque so that
neither axiom below is derivable from the other — the Perron *factorization*
`M(n) ≈ perronIntegral ε n` is genuine, not a relabelling of the conclusion. -/
noncomputable opaque perronIntegral (ε : ℝ) (n : ℕ) : ℝ

/-! ## The two classical analytic inputs (axioms) -/

/-- **(P) Truncated Perron inversion — RH-free.**  `M(n)` equals the shifted-
contour integral `perronIntegral ε n` up to a truncation error that is
unconditionally `O(n^{1/2+ε})`.  This is the elementary Perron estimate (Mellin
inversion + truncation of the vertical integral); it does **not** use RH. -/
axiom perron_approx_error :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        |(mertens n : ℝ) - perronIntegral ε n| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)

/-- **(Z) Conditional `1/ζ` bound on the shifted contour — carries RH.**  Under
the Riemann Hypothesis the critical-strip estimate `|1/ζ(1/2+ε+it)| ≪_ε |t|^ε`
holds, and integrating `|n^s| = n^{1/2+ε}` against it over the contour of height
`T = n` bounds the Perron integral itself by `O(n^{1/2+ε})`.  This is where RH
enters. -/
axiom perron_integral_bound_of_rh :
    RiemannHypothesis →
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          |perronIntegral ε n| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)

/-! ## The Littlewood growth condition -/

/-- The Littlewood bound: for every `ε > 0` there is `C > 0` with
`|M(n)| ≤ C · n^{1/2+ε}` for all `n ≥ 1`. -/
def LittlewoodBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)

/-! ## The Assembly (machine-checked)

The only content beyond the two analytic axioms: the triangle inequality
`|M(n)| ≤ |M(n) − I(n)| + |I(n)|` turns the RH-free Perron error (P) and the
RH-conditional contour bound (Z) into the ε-bound, with combined constant
`C₁ + C₂`.  No `√x` bound is used anywhere. -/

/-- **RH ⟹ Littlewood ε-bound (proved from the Perron axiom boundary).**  For a
fixed `ε > 0`: `|M(n)| ≤ |M(n) − perronIntegral ε n| + |perronIntegral ε n|`,
and each summand is `≤ C · n^{1/2+ε}` by (P) and (Z) respectively. -/
theorem rh_implies_mertens_eps_bound (h : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  intro ε hε
  obtain ⟨C₁, hC₁, hP⟩ := perron_approx_error ε hε
  obtain ⟨C₂, hC₂, hZ⟩ := perron_integral_bound_of_rh h ε hε
  refine ⟨C₁ + C₂, by positivity, fun n hn => ?_⟩
  have htri :
      |(mertens n : ℝ)|
        ≤ |(mertens n : ℝ) - perronIntegral ε n| + |perronIntegral ε n| := by
    calc |(mertens n : ℝ)|
        = |((mertens n : ℝ) - perronIntegral ε n) + perronIntegral ε n| := by
          ring_nf
      _ ≤ |(mertens n : ℝ) - perronIntegral ε n| + |perronIntegral ε n| :=
          abs_add_le _ _
  calc |(mertens n : ℝ)|
      ≤ |(mertens n : ℝ) - perronIntegral ε n| + |perronIntegral ε n| := htri
    _ ≤ C₁ * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) + C₂ * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
        add_le_add (hP n hn) (hZ n hn)
    _ = (C₁ + C₂) * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by ring

/-- Packaged as the `LittlewoodBound` predicate. -/
theorem rh_implies_littlewoodBound (h : RiemannHypothesis) : LittlewoodBound :=
  rh_implies_mertens_eps_bound h

/-- Immediate corollary: under RH, for every `ε > 0` there is an explicit growth
constant for the Mertens function (no `√x` bound assumed anywhere). -/
theorem rh_gives_explicit_constant (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
  rh_implies_mertens_eps_bound h ε hε

end RHConsequencesOQ01
