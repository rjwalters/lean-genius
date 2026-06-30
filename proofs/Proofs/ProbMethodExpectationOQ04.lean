/-
  First Moment Method — OQ-04: non-strict averaging (some outcome meets the mean)

  The gallery entry `ProbMethodExpectation` proves the *strict* first moment
  principle: `E[X] > t ⟹ ∃ ω, X(ω) > t` (`first_moment_principle`) and its dual.
  The strict form cannot conclude anything at the threshold `E[X] = t`, yet the
  most common use of the probabilistic method is exactly the non-strict statement
  *"some outcome is at least the average"* — used to extract a witness meeting the
  expectation.  This file supplies the non-strict averaging lemmas.

  * `exists_ge_of_card_mul_le` / `exists_le_of_card_mul_ge` — the division-free
    practical forms: `t·|s| ≤ ∑ f ⟹ ∃ a, t ≤ f a` (and dual).  This is the shape
    actually used in lower-bound arguments (avoids dividing by `|s|`).
  * `exists_ge_average` / `exists_le_average` — *some element is at least / at most
    the mean*: `∃ a ∈ s, (∑ f)/|s| ≤ f a` and the dual.  The pigeonhole core of the
    first moment method.
  * `first_moment_ge` / `first_moment_le` — the non-strict threshold forms,
    `E[X] ≥ t ⟹ ∃ a, f a ≥ t`, completing the strict `first_moment_principle` at
    the boundary.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Spencer, *The Probabilistic Method*, Ch. 2 (first moment).
-/

import Mathlib

namespace ProbMethod.ExpectationOQ04

open Finset BigOperators

variable {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℚ} {t : ℚ}

/-- **Division-free first moment (≥).**  If `t·|s| ≤ ∑ f` over a nonempty set, then
    some element is at least `t`.  This is the practical lower-bound shape of the
    first moment method (no division by `|s|`). -/
theorem exists_ge_of_card_mul_le (hs : s.Nonempty) (h : t * s.card ≤ s.sum f) :
    ∃ a ∈ s, t ≤ f a := by
  by_contra hc
  push_neg at hc
  have hlt : s.sum f < s.sum (fun _ => t) := Finset.sum_lt_sum_of_nonempty hs hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hlt
  linarith

/-- **Division-free first moment (≤).**  If `∑ f ≤ t·|s|`, some element is at most
    `t`. -/
theorem exists_le_of_card_mul_ge (hs : s.Nonempty) (h : s.sum f ≤ t * s.card) :
    ∃ a ∈ s, f a ≤ t := by
  by_contra hc
  push_neg at hc
  have hlt : s.sum (fun _ => t) < s.sum f := Finset.sum_lt_sum_of_nonempty hs hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hlt
  linarith

/-- **Some element is at least the mean.**  `∃ a ∈ s, (∑ f)/|s| ≤ f a`. -/
theorem exists_ge_average (hs : s.Nonempty) :
    ∃ a ∈ s, (s.sum f) / s.card ≤ f a := by
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  refine exists_ge_of_card_mul_le hs (le_of_eq ?_)
  field_simp

/-- **Some element is at most the mean.**  `∃ a ∈ s, f a ≤ (∑ f)/|s|`. -/
theorem exists_le_average (hs : s.Nonempty) :
    ∃ a ∈ s, f a ≤ (s.sum f) / s.card := by
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  refine exists_le_of_card_mul_ge hs (le_of_eq ?_)
  field_simp

/-- **Non-strict first moment principle (≥).**  If the average is at least `t`,
    some element is at least `t` — the boundary case the strict
    `first_moment_principle` cannot reach. -/
theorem first_moment_ge (hs : s.Nonempty) (havg : t ≤ (s.sum f) / s.card) :
    ∃ a ∈ s, t ≤ f a := by
  obtain ⟨a, ha, hfa⟩ := exists_ge_average hs
  exact ⟨a, ha, le_trans havg hfa⟩

/-- **Non-strict first moment principle (≤).**  Dual of `first_moment_ge`. -/
theorem first_moment_le (hs : s.Nonempty) (havg : (s.sum f) / s.card ≤ t) :
    ∃ a ∈ s, f a ≤ t := by
  obtain ⟨a, ha, hfa⟩ := exists_le_average hs
  exact ⟨a, ha, le_trans hfa havg⟩

/-! ## Application: strengthening `expected_mono_cliques` toward Erdős 1947

The parent gallery lemma `expected_mono_cliques` only records that the expected
number of monochromatic `k`-cliques in a uniformly random 2-colouring of the edges
of `Kₙ`, namely `E(n,k) = C(n,k)·2^{1−C(k,2)}`, is `≥ 0`.  The open question OQ-04
asks to strengthen this to `E(n,k) < 1` — which, by the (strict) first moment
principle, exhibits a 2-colouring with **no** monochromatic `k`-clique, i.e. the
Erdős 1947 lower bound `R(k,k) > n`.

This section makes two verified reductions toward that goal: it removes the integer
`zpow` by reducing `E < 1` to a clean `ℕ`-power inequality, and it records the
first-moment upper bound `E ≤ (nᵏ/k!)·2^{1−C(k,2)}` (via `Nat.choose_le_pow_div`),
the quantity Erdős's counting argument actually bounds below `1`. -/

/-- The expected number of monochromatic `k`-cliques in a uniformly random
2-colouring of `Kₙ`'s edges: `C(n,k) · 2^{1 − C(k,2)}` (matching the parent
`expected_mono_cliques`). -/
noncomputable def expectedMonoCliques (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * (2 : ℚ) ^ (1 - (k.choose 2 : ℤ))

/-- **Reduction of the Erdős strict bound to a pure power inequality.**  The
expected count is `< 1` *exactly* when `C(n,k)·2 < 2^{C(k,2)}` — a statement
entirely in `ℕ`-powers, with the integer `zpow` eliminated.  This is the clean
target a later session (or `Aristotle`) must discharge to answer OQ-04. -/
theorem expectedMonoCliques_lt_one_iff (n k : ℕ) :
    expectedMonoCliques n k < 1 ↔ (n.choose k : ℚ) * 2 < 2 ^ (k.choose 2) := by
  unfold expectedMonoCliques
  have hpow_pos : (0 : ℚ) < (2 : ℚ) ^ (k.choose 2) := by positivity
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_one, zpow_neg,
    zpow_natCast,
    show (n.choose k : ℚ) * (2 * ((2 : ℚ) ^ (k.choose 2))⁻¹)
        = ((n.choose k : ℚ) * 2) / (2 : ℚ) ^ (k.choose 2) from by rw [div_eq_mul_inv]; ring,
    div_lt_one hpow_pos]

/-- **First-moment upper bound on the expected count.**  Since `C(n,k) ≤ nᵏ/k!`
(`Nat.choose_le_pow_div`), the expected number of monochromatic `k`-cliques is at
most `(nᵏ/k!) · 2^{1 − C(k,2)}`.  Isolating this quantity reduces OQ-04 to the
elementary estimate `nᵏ · 2 < k! · 2^{C(k,2)}`. -/
theorem expectedMonoCliques_le (n k : ℕ) :
    expectedMonoCliques n k
      ≤ ((n : ℚ) ^ k / (k.factorial : ℚ)) * (2 : ℚ) ^ (1 - (k.choose 2 : ℤ)) := by
  unfold expectedMonoCliques
  apply mul_le_mul_of_nonneg_right _ (zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)
  have h := Nat.choose_le_pow_div k n (α := ℚ)
  simpa using h

end ProbMethod.ExpectationOQ04
