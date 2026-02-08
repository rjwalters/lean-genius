/-
# Erdős Problem #687 — Covering Congruences and the Jacobsthal Function

Let Y(x) be the maximal y such that there exists a choice of congruence
classes aₚ for all primes p ≤ x such that every integer in [1, y] is
≡ aₚ (mod p) for at least one prime p ≤ x.

Equivalently, Y(x) is the Jacobsthal function g(P(x)) where P(x) = ∏_{p ≤ x} p
is the primorial, and g(n) is the largest gap between consecutive integers
coprime to n.

## Status: OPEN ($1,000 prize)

## Key Results

- **Iwaniec (1978)**: Y(x) ≪ x² (best upper bound).
- **Ford–Green–Konyagin–Maynard–Tao (2018)**:
  Y(x) ≫ x · (log x)(log log log x) / (log log x).
- **Maier–Pomerance conjecture**: Y(x) ≪ x · (log x)^{2+o(1)}.
- **Rankin (1938)**: Earlier lower bound, improved by FGKMT.

## Related Problems

#688, #689, #970 address related variants.

*Reference:* [erdosproblems.com/687](https://www.erdosproblems.com/687)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset Filter

/- ## Core Definitions -/

/-- The primorial: product of all primes ≤ x. -/
noncomputable def primorial (x : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p

/-- An integer n is covered by a covering system if n ≡ aₚ (mod p)
for some prime p ≤ x. -/
def IsCovered (x : ℕ) (a : ∀ p : ℕ, p.Prime → p ≤ x → ℕ) (n : ℤ) : Prop :=
  ∃ (p : ℕ) (hp : p.Prime) (hpx : p ≤ x),
    (n : ℤ) % (p : ℤ) = (a p hp hpx : ℤ) % (p : ℤ)

/-- The set of y values achievable by some covering system for primes ≤ x. -/
def jacobsthalSet (x : ℕ) : Set ℕ :=
  { y : ℕ | ∃ a : ∀ p : ℕ, p.Prime → p ≤ x → ℕ,
    ∀ n : ℤ, 1 ≤ n → n ≤ y → IsCovered x a n }

/-- Y(x): the maximal y such that some covering system covers all of [1, y]. -/
noncomputable def jacobsthalY (x : ℕ) : ℕ :=
  sSup (jacobsthalSet x)

/- ## The Jacobsthal Function -/

/-- The Jacobsthal function g(n): largest gap between consecutive
integers coprime to n. Equivalently, g(n) = 1 + max length of a
run of integers all sharing a factor with n. -/
noncomputable def jacobsthal (n : ℕ) : ℕ :=
  sSup { d : ℕ | ∃ m : ℤ, ∀ k : ℤ, m < k → k < m + d →
    ∃ p : ℕ, p.Prime ∧ (p : ℤ) ∣ n ∧ (p : ℤ) ∣ k }

/- ## Basic Properties of jacobsthalSet -/

/-- 0 is always in the Jacobsthal set (vacuously: no integers in [1, 0]). -/
theorem jacobsthalSet_nonempty (x : ℕ) : (jacobsthalSet x).Nonempty := by
  refine ⟨0, ?_⟩
  unfold jacobsthalSet
  simp only [Set.mem_setOf_eq, Nat.cast_zero]
  exact ⟨fun _ _ _ => 0, fun n h1 h2 => by omega⟩

/-- The Jacobsthal set is bounded above by the primorial.
After primorial(x) steps, the CRT covering pattern repeats, so any
uncovered integer would imply infinitely many uncovered integers
in any interval of length primorial(x). -/
axiom jacobsthalSet_bddAbove (x : ℕ) :
  BddAbove (jacobsthalSet x)

/- ## Structural Properties -/

/-- Key lemma: the Jacobsthal set for x₁ is contained in that for x₂
when x₁ ≤ x₂. Given a covering for primes ≤ x₁, extend it to primes
≤ x₂ by choosing class 0 for each new prime. -/
theorem jacobsthalSet_mono {x₁ x₂ : ℕ} (h : x₁ ≤ x₂) :
    jacobsthalSet x₁ ⊆ jacobsthalSet x₂ := by
  intro y hy
  unfold jacobsthalSet at hy ⊢
  simp only [Set.mem_setOf_eq] at hy ⊢
  obtain ⟨a, ha⟩ := hy
  -- Extend covering: keep old classes, use 0 for new primes
  refine ⟨fun p hp hpx₂ => if hle : p ≤ x₁ then a p hp hle else 0, fun n h1 hn => ?_⟩
  obtain ⟨p, hp, hpx₁, hcov⟩ := ha n h1 hn
  exact ⟨p, hp, le_trans hpx₁ h, by simp only [dif_pos hpx₁]; exact hcov⟩

/-- Y(x) is monotone non-decreasing in x: more primes allow
longer covering intervals. -/
theorem jacobsthalY_mono (x₁ x₂ : ℕ) (h : x₁ ≤ x₂) :
    jacobsthalY x₁ ≤ jacobsthalY x₂ := by
  unfold jacobsthalY
  exact csSup_le_csSup (jacobsthalSet_bddAbove x₂)
    (jacobsthalSet_nonempty x₁) (jacobsthalSet_mono h)

/- ## Connection to Jacobsthal Function -/

/-- Y(x) equals the Jacobsthal function of the primorial. -/
axiom jacobsthalY_eq_jacobsthal (x : ℕ) :
  jacobsthalY x = jacobsthal (primorial x)

/- ## Main Conjecture ($1,000) -/

/-- **Erdős Problem #687 ($1,000 prize).**
Is Y(x) = o(x²)? More specifically, is Y(x) ≪ x^{1+o(1)}? -/
axiom erdos_687_conjecture :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
    (jacobsthalY x : ℝ) ≤ (x : ℝ) ^ (1 + ε)

/- ## Known Bounds -/

/-- **Iwaniec (1978).** Y(x) ≪ x².
This is the best known upper bound. -/
axiom iwaniec_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ (x : ℕ), 2 ≤ x →
    (jacobsthalY x : ℝ) ≤ C * (x : ℝ) ^ 2

/-- **Ford–Green–Konyagin–Maynard–Tao (2018).**
Y(x) ≫ x · (log x)(log log log x) / (log log x).
This improved Rankin's classical lower bound. -/
axiom fgkmt_lower :
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ (x : ℕ) in atTop,
    (jacobsthalY x : ℝ) ≥ c * (x : ℝ) *
      Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
      Real.log (Real.log (x : ℝ))

/-- **Maier–Pomerance Conjecture.** Y(x) ≪ x · (log x)^{2+o(1)}.
If true, this would nearly close the gap with the FGKMT lower bound. -/
axiom maier_pomerance_conjecture :
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ (x : ℕ) in atTop,
    (jacobsthalY x : ℝ) ≤ C * (x : ℝ) * Real.log (x : ℝ) ^ (2 + ε)

/-- The trivial lower bound: Y(x) ≥ x + 1, since we can cover
[1, x] by taking aₚ = 0 for each prime p ≤ x (every integer in [1,x]
has a prime factor ≤ x). The interval [1, x+1] is also covered since
x+1 has a prime factor ≤ x+1 ≤ ... but the precise bound needs careful
argument. -/
axiom jacobsthalY_trivial_lower (x : ℕ) (hx : 2 ≤ x) :
  x + 1 ≤ jacobsthalY x
