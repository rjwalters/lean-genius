/-
  Maclaurin's Inequality: The Equality Case (Sufficiency Direction)
  Research: amgm-inequality-oq-02-oq-02-oq-02

  The parent formalization `amgm-inequality-oq-02-oq-02`
  (`Proofs.AmgmInequalityOQ02`) proves Newton's log-concavity and the
  Maclaurin step Mₖ(x) ≥ Mₖ₊₁(x), where

      Mⱼ(x) = (eⱼ(x) / C(n,j))^(1/j)

  and eⱼ is the j-th elementary symmetric polynomial.  Its list of open
  questions asks (OQ-02) for the **equality case**:

      Mₖ(x) = Mₖ₊₁(x)   ⟺   all non-zero inputs are equal.

  This file settles the *sufficiency* (⟸) direction in full generality:
  when every coordinate equals a common constant c ≥ 0, every Maclaurin
  mean collapses to c, so the whole chain M₁ = M₂ = ⋯ = Mₙ = c consists of
  equalities.  The necessity (⟹) direction — that equality forces the
  inputs to be equal up to a zero block — requires tracking when the
  discriminant in the cleared-denominator induction is exactly zero and is
  left open (spawns a further child problem).

  Main results (0 axioms, 0 sorries):
  1. `elemSymm_const`        — eₖ(c,…,c) = C(n,k)·cᵏ
  2. `maclaurinMean_const`   — Mₖ(c,…,c) = c  (for c ≥ 0, 1 ≤ k ≤ n)
  3. `maclaurin_eq_of_const` — consecutive means agree on a constant input
  4. `maclaurin_all_eq_of_const` — every two means agree on a constant input
  5. `not_const_of_maclaurin_ne` — contrapositive: differing means ⟹ the
     input is not constant

  References:
  - Hardy–Littlewood–Pólya "Inequalities" (1934) §2.22
  - Maclaurin (1729)
  - AmgmInequalityOQ02.lean (parent formalization; source of eₖ, Mₖ)
-/

import Proofs.AmgmInequalityOQ02

open Finset Real

namespace MaclaurinEquality

/-!
## Elementary symmetric polynomials on a constant input

If every coordinate equals `c`, then each product over a `k`-element subset
is `cᵏ`, and there are exactly `C(n,k)` such subsets.  Hence
`eₖ(c,…,c) = C(n,k)·cᵏ`.
-/

/-- The `k`-th elementary symmetric polynomial of the constant vector
    `(c, …, c)` on `n` coordinates equals `C(n,k)·cᵏ`. -/
theorem elemSymm_const {n : ℕ} (k : ℕ) (c : ℝ) :
    elemSymm k (fun _ : Fin n => c) = (Nat.choose n k : ℝ) * c ^ k := by
  unfold elemSymm
  -- Every product over a `k`-subset is `c^k`.
  have hprod : ∀ s ∈ (univ : Finset (Fin n)).powersetCard k,
      (∏ _i ∈ s, c) = c ^ k := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [Finset.prod_const, hs.2]
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-!
## Maclaurin means on a constant input

For `1 ≤ k ≤ n` and `c ≥ 0`, the normalization cancels `C(n,k)` and the
outer `(·)^(1/k)` inverts the inner `cᵏ`, giving `Mₖ(c,…,c) = c`.
-/

/-- Each Maclaurin mean of a non-negative constant vector equals that
    constant: `Mₖ(c, …, c) = c`. -/
theorem maclaurinMean_const {n : ℕ} (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    maclaurinMean k (fun _ : Fin n => c) = c := by
  have hchoose : (0 : ℝ) < (Nat.choose n k : ℝ) := by
    have : 0 < Nat.choose n k := Nat.choose_pos hkn
    exact_mod_cast this
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold maclaurinMean
  rw [elemSymm_const]
  -- (C(n,k)·cᵏ)/C(n,k) = cᵏ
  rw [mul_comm, mul_div_assoc, div_self hchoose.ne', mul_one]
  -- (cᵏ)^(1/k) = c
  rw [← Real.rpow_natCast c k, ← Real.rpow_mul hc, mul_one_div, div_self hkne,
      Real.rpow_one]

/-- **Sufficiency, consecutive form.**  On a non-negative constant input the
    Maclaurin step is an equality: `Mₖ(c,…,c) = Mₖ₊₁(c,…,c)`. -/
theorem maclaurin_eq_of_const {n : ℕ} (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    maclaurinMean k (fun _ : Fin n => c) = maclaurinMean (k + 1) (fun _ : Fin n => c) := by
  rw [maclaurinMean_const k c hc hk (by omega),
      maclaurinMean_const (k + 1) c hc (by omega) hkn]

/-- **Sufficiency, full chain.**  On a non-negative constant input *every*
    pair of Maclaurin means (with indices in `1..n`) agrees; the whole
    chain `M₁ = M₂ = ⋯ = Mₙ = c` collapses to a single value. -/
theorem maclaurin_all_eq_of_const {n : ℕ} (j k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hj : 1 ≤ j) (hjn : j ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    maclaurinMean j (fun _ : Fin n => c) = maclaurinMean k (fun _ : Fin n => c) := by
  rw [maclaurinMean_const j c hc hj hjn, maclaurinMean_const k c hc hk hkn]

/-!
## Contrapositive

If two Maclaurin means of `x` disagree, then `x` cannot be a non-negative
constant vector.  This is the logically-equivalent statement of the
sufficiency direction and is the shape used when Maclaurin's inequality is
applied to detect non-constant data.
-/

/-- **Contrapositive of sufficiency.**  If some consecutive Maclaurin means
    of `x` differ, then `x` is not a non-negative constant vector. -/
theorem not_const_of_maclaurin_ne {n : ℕ} (k : ℕ) (x : Fin n → ℝ)
    (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (h : maclaurinMean k x ≠ maclaurinMean (k + 1) x) :
    ¬ ∃ c : ℝ, 0 ≤ c ∧ x = fun _ => c := by
  rintro ⟨c, hc, rfl⟩
  exact h (maclaurin_eq_of_const k c hc hk hkn)

end MaclaurinEquality
