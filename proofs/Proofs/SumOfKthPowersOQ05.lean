import Mathlib

/-
# Power Sums over a Finite Field (Sum of k-th Powers, OQ-05)

The "sum of k-th powers" family in the gallery collects integer closed forms and
asymptotics for `∑_{i<n} i^k` (Faulhaber / Bernoulli / Nicomachus / Euler–Maclaurin).
This entry develops the orthogonal **modular** face of power sums: the value of the
complete power sum

  `∑_{x ∈ 𝔽_q} x^k`

over an entire finite field of cardinality `q`.  The answer is a clean dichotomy:

  `∑_{x : K} x^k = -1`  if `k ≠ 0` and `(q-1) ∣ k`,   and `0` otherwise.

Mathlib provides `FiniteField.sum_pow_units`, the sum over the *units* `Kˣ`.  The
headline result here extends that to the **whole** field, which requires handling the
`x = 0` term and — crucially — the `k = 0` edge case, where every summand is `1` and the
sum collapses to `q · 1 = 0` in characteristic `p`.  This is exactly the mechanism behind
Fermat's little theorem and the von Staudt–Clausen congruences (the residues `0,1,…,p-1`
sum to `0`, and more generally `∑ i^k ≡ -1 (mod p)` precisely when `(p-1) ∣ k`).

All results are `0`-axiom; the concrete examples use kernel `decide` (not the
compiler-trusting variant), so no `Lean.ofReduceBool` dependency is incurred.
-/

namespace SumOfKthPowersOQ05

open Finset
open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **Complete power sum over a finite field.**
For a finite field `K` of cardinality `q = Fintype.card K`,
`∑_{x : K} x^k = -1` when `k ≠ 0` and `(q-1) ∣ k`, and `0` otherwise.

This extends `FiniteField.sum_pow_units` (the sum over the units `Kˣ`) to the full field:
the `x = 0` term vanishes when `k ≠ 0`, and when `k = 0` every term equals `1`, so the
sum is `q · 1 = 0` in characteristic `p`. -/
theorem sum_pow_eq (k : ℕ) :
    (∑ x : K, x ^ k) = if k ≠ 0 ∧ (Fintype.card K - 1) ∣ k then -1 else 0 := by
  rcases eq_or_ne k 0 with hk | hk
  · -- k = 0 : every summand is 1, so the sum is `(card K) · 1 = 0` in char p.
    subst hk
    simp only [pow_zero, sum_const, card_univ, nsmul_eq_mul, mul_one]
    rw [FiniteField.cast_card_eq_zero, if_neg]
    rintro ⟨h, -⟩
    exact h rfl
  · -- k ≠ 0 : drop the zero term and reduce to the sum over units.
    have key : (∑ x : K, x ^ k) = ∑ x : Kˣ, (x ^ k : K) := by
      let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
      have himg : univ.map φ = univ \ {0} := by
        ext x
        simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
          mem_singleton, φ] using isUnit_iff_ne_zero
      calc
        (∑ x : K, x ^ k) = ∑ x ∈ univ \ {(0 : K)}, x ^ k := by
            rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hk, add_zero]
        _ = ∑ x : Kˣ, (x ^ k : K) := by simp [φ, ← himg, univ.sum_map φ]
    rw [key, FiniteField.sum_pow_units]
    simp only [hk, ne_eq, not_false_eq_true, true_and]

/-- **Power sum over `ZMod p`.** For a prime `p`,
`∑_{x : ZMod p} x^k = -1` when `k ≠ 0` and `(p-1) ∣ k`, and `0` otherwise. -/
theorem sum_pow_zmod (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (∑ x : ZMod p, x ^ k) = if k ≠ 0 ∧ (p - 1) ∣ k then -1 else 0 := by
  have h := sum_pow_eq (K := ZMod p) k
  rwa [ZMod.card] at h

/-- The complete power sum equals `-1` exactly when `k ≠ 0` and `(p-1) ∣ k`. -/
theorem sum_pow_zmod_eq_neg_one_iff (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (∑ x : ZMod p, x ^ k) = -1 ↔ k ≠ 0 ∧ (p - 1) ∣ k := by
  rw [sum_pow_zmod]
  constructor
  · intro h
    by_contra hcon
    rw [if_neg hcon] at h
    -- `0 = -1` forces `1 = 0`, impossible in the field `ZMod p`.
    exact one_ne_zero (by linear_combination h)
  · intro h
    rw [if_pos h]

/-- **Sum of all residues.** For an odd prime `p`, the residues `0, 1, …, p-1`
sum to `0` in `ZMod p` (the `k = 1` case: `(p-1) ∤ 1` once `p > 2`). -/
theorem sum_residues_eq_zero (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (∑ x : ZMod p, x) = 0 := by
  have h := sum_pow_zmod p 1
  simp only [pow_one] at h
  rw [h, if_neg]
  rintro ⟨-, hdvd⟩
  have : p - 1 ≤ 1 := Nat.le_of_dvd one_pos hdvd
  omega

/-! ### Concrete instances (verified by `decide`, hence `0`-axiom) -/

/-- `∑_{x : ZMod 5} x^4 = -1 = 4`, since `(5-1) ∣ 4`. -/
example : (∑ x : ZMod 5, x ^ 4) = 4 := by decide

/-- `∑_{x : ZMod 5} x^2 = 0`, since `(5-1) ∤ 2`. -/
example : (∑ x : ZMod 5, x ^ 2) = 0 := by decide

/-- `∑_{x : ZMod 7} x^6 = -1 = 6`, since `(7-1) ∣ 6`. -/
example : (∑ x : ZMod 7, x ^ 6) = 6 := by decide

/-- Sum of residues of `ZMod 5` is `0` (instance of `sum_residues_eq_zero`). -/
example : (∑ x : ZMod 5, x) = 0 := by decide

end SumOfKthPowersOQ05
