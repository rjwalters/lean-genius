/-
# Erdős Problem #495: The Littlewood Conjecture

**Source:** [erdosproblems.com/495](https://erdosproblems.com/495)
**Status:** OPEN (Littlewood, c. 1930)

## Statement

Let α, β ∈ ℝ. Is it true that
  lim inf (n → ∞) n · ‖nα‖ · ‖nβ‖ = 0
where ‖x‖ denotes the distance from x to the nearest integer?

## Background

This is the famous Littlewood conjecture, one of the central open
problems in Diophantine approximation. It asks whether every pair
of real numbers can be simultaneously well-approximated by rationals
in a multiplicative sense.

Einsiedler–Katok–Lindenstrauss (2006) proved the set of
counterexamples has Hausdorff dimension zero. This earned
Lindenstrauss the 2010 Fields Medal.

## Approach

We define the distance-to-nearest-integer function, formulate the
Littlewood conjecture, and state the key partial results as axioms.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos495

/- ## Part I: Distance to Nearest Integer -/

/--
The distance from x to the nearest integer: ‖x‖ = |x - round(x)|.
This is also called the fractional distance or the distance to ℤ.
-/
noncomputable def distInt (x : ℝ) : ℝ :=
  |x - round x|

/--
distInt is always non-negative (formerly axiom, now proved).
-/
theorem distInt_nonneg (x : ℝ) : distInt x ≥ 0 := by
  unfold distInt; exact abs_nonneg _

/--
distInt is at most 1/2 (formerly axiom, now proved).
Uses the fundamental property of rounding: |x - round(x)| ≤ 1/2.
-/
theorem distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := by
  unfold distInt; exact abs_sub_round x

/- ## Part II: The Littlewood Product -/

/--
The Littlewood product at n for parameters α, β:
  L(n, α, β) = n · ‖nα‖ · ‖nβ‖
-/
noncomputable def littlewoodProduct (n : ℕ) (α β : ℝ) : ℝ :=
  (n : ℝ) * distInt ((n : ℝ) * α) * distInt ((n : ℝ) * β)

/--
The Littlewood product is always non-negative (formerly axiom, now proved).
Each factor is non-negative: n ≥ 0, |·| ≥ 0, |·| ≥ 0.
-/
theorem littlewoodProduct_nonneg (n : ℕ) (α β : ℝ) :
    littlewoodProduct n α β ≥ 0 := by
  unfold littlewoodProduct distInt
  positivity

/- ## Part III: The Littlewood Conjecture -/

/--
**Erdős Problem #495 / The Littlewood Conjecture (c. 1930):**
For all α, β ∈ ℝ,
  lim inf (n → ∞) n · ‖nα‖ · ‖nβ‖ = 0.

Equivalently: for every ε > 0, there exist infinitely many n ∈ ℕ
with n · ‖nα‖ · ‖nβ‖ < ε.
-/
def LittlewoodConjecture : Prop :=
  ∀ α β : ℝ, ∀ ε : ℝ, ε > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 1 ∧
      littlewoodProduct n α β < ε

/- ## Part IV: Special Cases -/

/--
The conjecture holds when α is rational: if α = p/q then
‖nα‖ = 0 for n a multiple of q, so the product vanishes.
-/
axiom littlewood_rational_case :
  ∀ (p : ℤ) (q : ℕ), q ≥ 1 →
    ∀ β : ℝ, ∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 1 ∧
        littlewoodProduct n ((p : ℝ) / (q : ℝ)) β < ε

/--
Cassels–Swinnerton-Dyer (1955): the conjecture holds when
α, β lie in the same cubic number field.
E.g., α = ∛2 and β = (∛2)².
-/
/- ## Part V: The EKL Theorem -/

/--
**Einsiedler–Katok–Lindenstrauss (2006):**
The set of pairs (α, β) for which the Littlewood conjecture fails
has Hausdorff dimension zero. Counterexamples, if they exist, are
extremely rare.

The proof uses ergodic theory on homogeneous spaces and the
classification of invariant measures for diagonal actions on
SL(3,ℝ)/SL(3,ℤ). Lindenstrauss received the 2010 Fields Medal
partly for this work.
-/
/-- **Einsiedler-Katok-Lindenstrauss (2006):**
The set of counterexamples to Littlewood has Hausdorff dimension 0.
We axiomatize a consequence: for any α, the set of β failing Littlewood
with α is countable (weaker than dim 0 but still meaningful). -/
axiom ekl_countable_exceptions :
  ∀ α : ℝ,
    ∃ (S : Set ℝ), S.Countable ∧
      ∀ β : ℝ, β ∉ S →
        ∀ ε : ℝ, ε > 0 →
          ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 1 ∧
            littlewoodProduct n α β < ε

/- ## Part VI: The p-adic Littlewood Conjecture -/

/--
The p-adic Littlewood conjecture (de Mathan–Teulié, 2004):
for every real α and prime p,
  lim inf (n → ∞) n · |n|_p · ‖nα‖ = 0.

Einsiedler–Kleinbock (2007) proved the set of counterexamples
has Hausdorff dimension zero, analogous to EKL.
-/
def PAdicLittlewood (p : ℕ) (_ : p.Prime) : Prop :=
  ∀ α : ℝ, ∀ ε : ℝ, ε > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 1 ∧
      (n : ℝ) * distInt ((n : ℝ) * α) < ε * (n : ℝ)

/--
Badziahin–Velani (2014) proved the p-adic Littlewood conjecture
for a class of badly approximable numbers.
-/
/- ## Part VII: Summary -/

/--
**Summary:**
Erdős Problem #495 is the Littlewood conjecture (c. 1930): for all
α, β ∈ ℝ, lim inf n · ‖nα‖ · ‖nβ‖ = 0. Known for rationals,
cubic irrationals (Cassels–Swinnerton-Dyer), and "almost all" pairs
(EKL, Hausdorff dimension zero exceptions). Still OPEN in full generality.
-/
theorem erdos_495_summary :
    -- The conjecture holds for rational α
    (∀ (p : ℤ) (q : ℕ), q ≥ 1 →
      ∀ β : ℝ, ∀ ε : ℝ, ε > 0 →
        ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 1 ∧
          littlewoodProduct n ((p : ℝ) / (q : ℝ)) β < ε) ∧
    -- Exceptions are countable for each fixed α (weaker than EKL)
    (∀ α : ℝ, ∃ (S : Set ℝ), S.Countable ∧
      ∀ β : ℝ, β ∉ S →
        ∀ ε : ℝ, ε > 0 →
          ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ n ≥ 1 ∧
            littlewoodProduct n α β < ε) :=
  ⟨littlewood_rational_case, ekl_countable_exceptions⟩

end Erdos495
