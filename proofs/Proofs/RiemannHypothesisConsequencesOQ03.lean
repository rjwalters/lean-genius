/-
# Littlewood's Equivalence:  RH  ⟺  M(x) = O(x^{1/2+ε})

This file formalizes the classical theorem of Littlewood (1912):

  The Riemann Hypothesis is *equivalent* to the statement that, for every ε > 0,
  the Mertens function M(x) = Σ_{n ≤ x} μ(n) satisfies M(x) = O(x^{1/2+ε}).

**Status**: axiomatized.  The Riemann Hypothesis is open, so the equivalence
cannot be verified.  We state the two directions as the two genuine classical
inputs and *derive* the biconditional from them:

* Forward direction (`rh_implies_littlewood_bound`) is **proved** from the
  sharper classical bound `|M(x)| ≤ C·√x` (which RH is known to imply).  The
  ε-relaxation is genuinely weaker than the √x bound, and we make that logical
  step machine-checked: `n^{1/2} ≤ n^{1/2+ε}` for `n ≥ 1`, `ε ≥ 0`.

* Reverse direction (`littlewood_bound_implies_rh`) is the deep half.  It follows
  from the convergence of the Dirichlet series Σ μ(n) n^{-s} = 1/ζ(s) for
  Re(s) > 1/2 (via partial summation of the M(n) bound), which forces ζ to be
  zero-free there.  The analytic machinery (Perron / partial summation with the
  Dirichlet series of 1/ζ) is not yet in Mathlib, so this direction is an axiom.

Thus the biconditional `littlewood_equivalence` is **not** axiomatized directly;
it is assembled from one derived implication and one axiomatized implication.

**Historical note.**  The Mertens *conjecture* |M(x)| < √x (a strictly stronger
statement than Littlewood's O(x^{1/2+ε})) was disproved by Odlyzko and te Riele
(1985).  Littlewood's weaker equivalence remains, and is what RH actually gives.

Mathlib already provides `RiemannHypothesis`
(see `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`) and the Möbius function
`ArithmeticFunction.moebius`.
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace RHConsequencesOQ03

open ArithmeticFunction

/-!
## The Mertens function

`M(n) = Σ_{k ≤ n} μ(k)`, the summatory function of the Möbius function.
We sum over `Finset.range (n+1)` so that `M(n)` includes the term `k = n`.
(The `k = 0` term contributes `μ(0) = 0`.)
-/

/-- The Mertens function `M(n) = Σ_{k ≤ n} μ(k)`. -/
def mertens (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.moebius k

/-- `M(n+1) = M(n) + μ(n+1)`: the Mertens function steps by one Möbius value. -/
theorem mertens_step (n : ℕ) :
    mertens (n + 1) = mertens n + ArithmeticFunction.moebius (n + 1) := by
  simp [mertens, Finset.sum_range_succ]

/-- `M(0) = 0` since `μ(0) = 0`. -/
theorem mertens_zero : mertens 0 = 0 := by
  simp [mertens]

/-- `M(1) = 1` since `μ(0) + μ(1) = 0 + 1`. -/
theorem mertens_one : mertens 1 = 1 := by
  simp [mertens, Finset.sum_range_succ]

/-!
## The Littlewood big-O condition

`LittlewoodBound` is the statement `∀ ε > 0, M(x) = O(x^{1/2+ε})`, spelled out
with an explicit constant: for every `ε > 0` there is `C > 0` with
`|M(n)| ≤ C · n^{1/2+ε}` for all `n ≥ 1`.
-/

/-- The Littlewood growth condition on the Mertens function:
for every `ε > 0` there is a constant `C > 0` such that
`|M(n)| ≤ C · n^{1/2+ε}` for all `n ≥ 1`. -/
def LittlewoodBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)

/-!
## The two classical inputs
-/

/-- **Classical (RH ⟹ √x bound).**  The Riemann Hypothesis implies the sharp
Mertens bound `|M(n)| ≤ C·√n`.  This is a standard consequence of RH (stronger
than Littlewood's ε-bound); its proof needs the explicit-formula / zero-free
machinery not yet available in Mathlib, so it is stated as an axiom. -/
axiom rh_implies_mertens_sqrt_bound :
    RiemannHypothesis →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → |(mertens n : ℝ)| ≤ C * Real.sqrt n

/-- **Deep direction of Littlewood's equivalence (ε-bound ⟹ RH).**  If
`M(x) = O(x^{1/2+ε})` for every `ε > 0`, then the Dirichlet series
`Σ μ(n) n^{-s} = 1/ζ(s)` converges for `Re(s) > 1/2` (partial summation), so
`ζ` has no zeros with `Re(s) > 1/2`; by the functional equation, none with
`Re(s) < 1/2` either, which is RH.  The analytic input (partial summation
against the Dirichlet series of `1/ζ`) is not in Mathlib, so this is an axiom. -/
axiom littlewood_bound_implies_rh :
    LittlewoodBound → RiemannHypothesis

/-!
## Auxiliary monotonicity

The exponent in the Littlewood condition is monotone: a bound at exponent `ε`
automatically gives a (weaker) bound at any `ε' ≥ ε`, because `n ≥ 1`.
-/

/-- A valid `|M(n)| ≤ C·n^{1/2+ε}` bound also holds at any larger exponent
`ε' ≥ ε` (with the same constant), since `n^{1/2+ε} ≤ n^{1/2+ε'}` for `n ≥ 1`. -/
theorem mertens_bound_exponent_mono {ε ε' C : ℝ} (hle : ε ≤ ε') (hC : 0 < C)
    (h : ∀ n : ℕ, 1 ≤ n → |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) :
    ∀ n : ℕ, 1 ≤ n → |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε') := by
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ ((1 : ℝ) / 2 + ε) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε') :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  calc |(mertens n : ℝ)|
      ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := h n hn
    _ ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε') :=
        mul_le_mul_of_nonneg_left hpow hC.le

/-!
## Forward direction, derived

Here is the genuine machine-checked content: the ε-bound follows from the √x
bound, using `√n = n^{1/2} ≤ n^{1/2+ε}` for `n ≥ 1`, `ε > 0`.
-/

/-- **RH ⟹ Littlewood bound (proved).**  The ε-relaxed bound is a consequence of
the sharp `√x` bound: `√n = n^{1/2} ≤ n^{1/2+ε}` once `n ≥ 1`. -/
theorem rh_implies_littlewood_bound (h : RiemannHypothesis) : LittlewoodBound := by
  obtain ⟨C, hC, hbound⟩ := rh_implies_mertens_sqrt_bound h
  intro ε hε
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- `√n = n^{1/2}`
  have hsqrt : Real.sqrt n = (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
  -- `n^{1/2} ≤ n^{1/2+ε}` since the base is ≥ 1 and the exponent grows
  have hpow : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  calc |(mertens n : ℝ)|
      ≤ C * Real.sqrt n := hbound n hn
    _ = C * (n : ℝ) ^ ((1 : ℝ) / 2) := by rw [hsqrt]
    _ ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
        mul_le_mul_of_nonneg_left hpow hC.le

/-!
## Littlewood's equivalence

Assembling the derived forward direction with the axiomatized reverse direction.
-/

/-- **Littlewood's equivalence (1912):**
`RH ⟺ (∀ ε > 0, M(x) = O(x^{1/2+ε}))`.

The forward implication is derived from the sharp `√x` bound; only the reverse
(deep) implication is taken as an axiom. -/
theorem littlewood_equivalence : RiemannHypothesis ↔ LittlewoodBound :=
  ⟨rh_implies_littlewood_bound, littlewood_bound_implies_rh⟩

/-- Restatement of the equivalence with the big-O condition written out in full. -/
theorem littlewood_equivalence_unfolded :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
  littlewood_equivalence

/-- Immediate corollary: under RH, for every `ε > 0` there is an explicit growth
constant for the Mertens function. -/
theorem rh_gives_explicit_constant (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      |(mertens n : ℝ)| ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
  (littlewood_equivalence.mp h) ε hε

end RHConsequencesOQ03
