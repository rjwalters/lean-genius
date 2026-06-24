import Mathlib

/-
# Degree-`k` binomial truncation lower bound for `(1 + a)ⁿ`

**Open question (bernoulli-inequality-oq-01-oq-02-oq-01).** The parent entry
`BernoulliInequalityOQ01OQ02` proves the *second-order* Bernoulli inequality
`1 + n·a + C(n,2)·a² ≤ (1+a)ⁿ` (for `a ≥ 0`) together with its sharp equality
characterization (equality iff `a = 0 ∨ n ≤ 2`).  The natural next question is
the **arbitrary-degree** refinement: for each truncation order `k`,

  `∑_{i=0}^{k} C(n,i) · aⁱ  ≤  (1 + a)ⁿ`   for `a ≥ 0`,

with its own sharp equality boundary.  This entry settles it.

The mechanism is uniform and elementary: by the binomial theorem
`(1+a)ⁿ = ∑_{i=0}^{n} C(n,i) aⁱ`, the truncated sum `∑_{i≤k}` is, after padding
to a common range, a sub-sum of the full expansion whose discarded tail terms
`C(n,i) aⁱ` are all nonnegative.  The bound therefore holds for **every** `k`
(no relation between `k` and `n` is needed), and it is an *equality* exactly when
nothing positive is discarded:

* `binom_trunc_le`       : `0 ≤ a → ∑_{i≤k} C(n,i) aⁱ ≤ (1+a)ⁿ`.
* `binom_trunc_strict`   : `0 < a → k < n → ∑_{i≤k} C(n,i) aⁱ < (1+a)ⁿ`.
* `binom_trunc_eq_iff`   : for `0 ≤ a`, equality holds **iff** `a = 0 ∨ n ≤ k`.

The threshold `n ≤ k` says the truncation is exact precisely once it captures the
whole expansion; for `a > 0` the bound becomes strict as soon as a genuine tail
term `C(n,k+1) a^{k+1} > 0` is dropped, i.e. `k < n`.

This single family subsumes the earlier entries as the special cases `k = 1`
(first-order Bernoulli `1 + n·a ≤ (1+a)ⁿ`) and `k = 2` (the parent's second-order
bound), recorded below as `bernoulli_first_order` and `bernoulli_second_order`.

**Relation to Mathlib.** Mathlib has the first-order weak Bernoulli inequality
`one_add_mul_le_pow` and the full binomial theorem `add_pow`, but no
general-degree truncation bound with an equality characterization.
-/

namespace BernoulliInequalityOQ01OQ02OQ01

open Finset

variable {a : ℝ}

/-- The `i`-th term of the binomial expansion of `(1+a)ⁿ`, `C(n,i)·aⁱ`. -/
private def term (n i : ℕ) (a : ℝ) : ℝ := (n.choose i : ℝ) * a ^ i

private theorem term_nonneg (ha : 0 ≤ a) (n i : ℕ) : 0 ≤ term n i a :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha i)

/-- The binomial theorem in the orientation we need:
`(1 + a)ⁿ = ∑_{i=0}^{n} C(n,i) · aⁱ`. -/
private theorem full_expansion (n : ℕ) :
    (1 + a) ^ n = ∑ i ∈ range (n + 1), term n i a := by
  rw [add_comm, add_pow]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [term, one_pow, mul_comm]

/-- **Degree-`k` binomial truncation lower bound.**  For `a ≥ 0` and any `n, k`,
the partial sum of the first `k+1` binomial terms is dominated by the full power:
`∑_{i=0}^{k} C(n,i) aⁱ ≤ (1+a)ⁿ`.  No relation between `k` and `n` is assumed. -/
theorem binom_trunc_le (ha : 0 ≤ a) (n k : ℕ) :
    ∑ i ∈ range (k + 1), (n.choose i : ℝ) * a ^ i ≤ (1 + a) ^ n := by
  -- Pad both sides to the common range `range (N+1)` with `N = max k n`.
  set N := max k n with hN
  have hkN : k + 1 ≤ N + 1 := by omega
  have hnN : n + 1 ≤ N + 1 := by omega
  have hsub_k : range (k + 1) ⊆ range (N + 1) := Finset.range_subset_range.mpr hkN
  have hsub_n : range (n + 1) ⊆ range (N + 1) := Finset.range_subset_range.mpr hnN
  -- The padded full expansion still equals `(1+a)ⁿ` (extra terms vanish: `C(n,i)=0`).
  have hpad : (1 + a) ^ n = ∑ i ∈ range (N + 1), term n i a := by
    rw [full_expansion n]
    refine Finset.sum_subset hsub_n ?_
    intro i _ hi
    have : n < i := by simpa [Nat.lt_iff_add_one_le] using (Finset.mem_range.not.mp hi)
    simp [term, Nat.choose_eq_zero_of_lt this]
  calc
    ∑ i ∈ range (k + 1), (n.choose i : ℝ) * a ^ i
        = ∑ i ∈ range (k + 1), term n i a := rfl
    _ ≤ ∑ i ∈ range (N + 1), term n i a :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_k
            (fun i _ _ => term_nonneg ha n i)
    _ = (1 + a) ^ n := hpad.symm

/-- **Strict truncation bound.**  For `a > 0` and `k < n` a genuine positive tail
term is discarded, so the inequality is strict. -/
theorem binom_trunc_strict (ha : 0 < a) {n k : ℕ} (hkn : k < n) :
    ∑ i ∈ range (k + 1), (n.choose i : ℝ) * a ^ i < (1 + a) ^ n := by
  have hsub : range (k + 1) ⊆ range (n + 1) := Finset.range_subset_range.mpr (by omega)
  have hmem : k + 1 ∈ range (n + 1) := Finset.mem_range.mpr (by omega)
  have hnotmem : k + 1 ∉ range (k + 1) := by simp
  have hpos : 0 < term n (k + 1) a :=
    mul_pos (by exact_mod_cast Nat.choose_pos (by omega : k + 1 ≤ n)) (pow_pos ha (k + 1))
  have hlt :
      ∑ i ∈ range (k + 1), term n i a < ∑ i ∈ range (n + 1), term n i a :=
    Finset.sum_lt_sum_of_subset hsub hmem hnotmem hpos
      (fun i _ _ => term_nonneg ha.le n i)
  calc
    ∑ i ∈ range (k + 1), (n.choose i : ℝ) * a ^ i
        = ∑ i ∈ range (k + 1), term n i a := rfl
    _ < ∑ i ∈ range (n + 1), term n i a := hlt
    _ = (1 + a) ^ n := (full_expansion n).symm

/-- **Sharp equality characterization.**  For `a ≥ 0`, the degree-`k` truncation is
*exact* — `∑_{i=0}^{k} C(n,i) aⁱ = (1+a)ⁿ` — if and only if `a = 0` (only the
constant term survives on both sides) or `n ≤ k` (the truncation already captures
the entire expansion). -/
theorem binom_trunc_eq_iff (ha : 0 ≤ a) (n k : ℕ) :
    (∑ i ∈ range (k + 1), (n.choose i : ℝ) * a ^ i = (1 + a) ^ n) ↔ a = 0 ∨ n ≤ k := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨ha0, hk⟩ := hc
    have hapos : 0 < a := ha.lt_of_ne (Ne.symm ha0)
    have hkn : k < n := by omega
    exact (binom_trunc_strict hapos hkn).ne h
  · rintro (rfl | hnk)
    · -- `a = 0`: every term with `i ≥ 1` vanishes, leaving the constant `C(n,0)=1`.
      have hzero : ∑ i ∈ range (k + 1), (n.choose i : ℝ) * (0 : ℝ) ^ i = 1 := by
        rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
        · simp
        · intro i _ hi
          simp [zero_pow hi]
      simpa using hzero
    · -- `n ≤ k`: range `n+1 ⊆ k+1` and the extra terms vanish, so the sums agree.
      rw [full_expansion n]
      refine (Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_).symm
      intro i _ hi
      have : n < i := by simpa [Nat.lt_iff_add_one_le] using (Finset.mem_range.not.mp hi)
      simp [Nat.choose_eq_zero_of_lt this]

/-- **First-order Bernoulli** as the `k = 1` instance: `1 + n·a ≤ (1+a)ⁿ` for `a ≥ 0`. -/
theorem bernoulli_first_order (ha : 0 ≤ a) (n : ℕ) :
    1 + (n : ℝ) * a ≤ (1 + a) ^ n := by
  have h := binom_trunc_le ha n 1
  simpa [Finset.sum_range_succ, Nat.choose_one_right] using h

/-- **Second-order Bernoulli** (the parent entry's bound) as the `k = 2` instance:
`1 + n·a + C(n,2)·a² ≤ (1+a)ⁿ` for `a ≥ 0`. -/
theorem bernoulli_second_order (ha : 0 ≤ a) (n : ℕ) :
    1 + (n : ℝ) * a + (n.choose 2 : ℝ) * a ^ 2 ≤ (1 + a) ^ n := by
  have h := binom_trunc_le ha n 2
  simpa [Finset.sum_range_succ, Nat.choose_one_right] using h

end BernoulliInequalityOQ01OQ02OQ01
