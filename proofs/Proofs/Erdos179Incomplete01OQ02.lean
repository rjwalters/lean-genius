/-
  Erdős Problem #179 — Open Question OQ-02:
  Quantitative lower bounds on countAPs for structured sets (intervals)

  The parent entry Erdos179Incomplete01.lean proves the trivial UPPER bound
  `countAPs A k ≤ C(|A|, k)` and the exact 2-AP count `countAPs A 2 = C(|A|,2)`.
  This file answers the open question "can a quantitative lower bound on
  countAPs for structured sets (e.g. intervals) be formalized as a
  counterpoint to the upper bound?" affirmatively, with 0 axioms / 0 sorries:

  Main results:
    • `arithmeticProgression_inj`    : rigidity — for k ≥ 2 and positive
        differences, a k-AP determines its first term and common difference
        (via the endpoint lemmas `le_of_mem_arithmeticProgression` /
        `mem_arithmeticProgression_le`).
    • `countAPs_range_eq_sum`        : EXACT count for intervals —
        countAPs {0,…,N−1} k = Σ_{d=1}^{⌊(N−1)/(k−1)⌋} (N − (k−1)d).
    • `countAPs_range_lower_bound`   : the quantitative LOWER bound
        ⌊N/(2(k−1))⌋ · ⌊N/2⌋ ≤ countAPs {0,…,N−1} k — order N²/(4(k−1)),
        so intervals achieve the quadratic supersaturation order that the
        parent's F_k(N,ℓ) = N^{2−o(1)} results concern.
    • `countAPs_range_upper_bound`   : the matching upper bound ≤ N², so the
        interval count is Θ(N²) for each fixed k ≥ 2.
    • `containsAP_range_iff`         : {0,…,N−1} contains a k-AP iff k ≤ N.
    • `countAPs_range_two` / `countAPs_range_sum_two` : consistency with the
        parent's exact 2-AP count (the formula collapses to C(N,2) at k = 2).

  Reference: https://erdosproblems.com/179
-/

import Proofs.Erdos179Incomplete01

namespace Erdos179Combinatorics

open Finset
open scoped Classical

/- ## Part I: Endpoint lemmas — every AP element lies between the first
      and last terms, and both endpoints belong to the AP. -/

/-- Every element of a k-term AP is at least the first term. -/
theorem le_of_mem_arithmeticProgression {x a d k : ℕ}
    (hx : x ∈ arithmeticProgression a d k) : a ≤ x := by
  simp only [arithmeticProgression, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  omega

/-- Every element of a k-term AP is at most the last term `a + (k−1)d`. -/
theorem mem_arithmeticProgression_le {x a d k : ℕ}
    (hx : x ∈ arithmeticProgression a d k) : x ≤ a + (k - 1) * d := by
  simp only [arithmeticProgression, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have h : i * d ≤ (k - 1) * d := Nat.mul_le_mul_right d (by omega)
  omega

/-- The first term belongs to any nonempty AP. -/
theorem first_mem_arithmeticProgression (a d : ℕ) {k : ℕ} (hk : 0 < k) :
    a ∈ arithmeticProgression a d k := by
  simp only [arithmeticProgression, Finset.mem_image, Finset.mem_range]
  exact ⟨0, hk, by ring⟩

/-- The last term `a + (k−1)d` belongs to any nonempty AP. -/
theorem last_mem_arithmeticProgression (a d : ℕ) {k : ℕ} (hk : 0 < k) :
    a + (k - 1) * d ∈ arithmeticProgression a d k := by
  simp only [arithmeticProgression, Finset.mem_image, Finset.mem_range]
  exact ⟨k - 1, by omega, rfl⟩

/- ## Part II: Rigidity — an AP of length ≥ 2 with positive difference
      determines its parameters. This is what makes counting APs by
      parameter pairs (a, d) legitimate. -/

/-- **Rigidity.** For k ≥ 2 and positive common differences, equal k-term APs
    have equal first terms and equal differences: the first term is the
    minimum and the last term is the maximum, so both parameters are
    recoverable from the underlying set. -/
theorem arithmeticProgression_inj {a a' d d' : ℕ} {k : ℕ} (hk : 2 ≤ k)
    (hd : 0 < d) (hd' : 0 < d')
    (h : arithmeticProgression a d k = arithmeticProgression a' d' k) :
    a = a' ∧ d = d' := by
  have hk0 : 0 < k := by omega
  have h1 : a ∈ arithmeticProgression a' d' k := by
    rw [← h]; exact first_mem_arithmeticProgression a d hk0
  have h2 : a' ∈ arithmeticProgression a d k := by
    rw [h]; exact first_mem_arithmeticProgression a' d' hk0
  have ha : a = a' :=
    le_antisymm (le_of_mem_arithmeticProgression h2) (le_of_mem_arithmeticProgression h1)
  subst ha
  have h3 : a + (k - 1) * d ∈ arithmeticProgression a d' k := by
    rw [← h]; exact last_mem_arithmeticProgression a d hk0
  have h4 : a + (k - 1) * d' ∈ arithmeticProgression a d k := by
    rw [h]; exact last_mem_arithmeticProgression a d' hk0
  have h5 : a + (k - 1) * d ≤ a + (k - 1) * d' := mem_arithmeticProgression_le h3
  have h6 : a + (k - 1) * d' ≤ a + (k - 1) * d := mem_arithmeticProgression_le h4
  have h7 : (k - 1) * d = (k - 1) * d' := by omega
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) h7⟩

/-- A nonempty AP fits inside `range N` iff its last term does. -/
theorem arithmeticProgression_subset_range {a d N : ℕ} {k : ℕ} (hk : 0 < k) :
    arithmeticProgression a d k ⊆ Finset.range N ↔ a + (k - 1) * d < N := by
  constructor
  · intro h
    have hlast := h (last_mem_arithmeticProgression a d hk)
    simpa using hlast
  · intro h x hx
    rw [Finset.mem_range]
    exact lt_of_le_of_lt (mem_arithmeticProgression_le hx) h

/- ## Part III: The exact AP count for intervals.
      The k-APs inside {0,…,N−1} are exactly parameterized by pairs (d, a)
      with 1 ≤ d ≤ ⌊(N−1)/(k−1)⌋ and a < N − (k−1)d, so the count is the
      sum of fiber sizes. -/

/-- **Exact formula.** For k ≥ 2, the number of k-term APs contained in the
    interval {0, …, N−1} is `Σ_{d=1}^{⌊(N−1)/(k−1)⌋} (N − (k−1)d)`. -/
theorem countAPs_range_eq_sum (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    countAPs (Finset.range N) k =
      ∑ d ∈ Finset.Icc 1 ((N - 1) / (k - 1)), (N - (k - 1) * d) := by
  classical
  have hk1 : 0 < k - 1 := by omega
  have hk0 : 0 < k := by omega
  -- The AP finsets are the image of the parameter set under (d, a) ↦ AP a d k.
  have key : countAPs (Finset.range N) k =
      (((Finset.Icc 1 ((N - 1) / (k - 1))).sigma
        (fun d => Finset.range (N - (k - 1) * d))).image
          (fun p => arithmeticProgression p.2 p.1 k)).card := by
    unfold countAPs
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Finset.mem_sigma,
      Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨hsub, a, d, hd, rfl⟩
      rw [arithmeticProgression_subset_range hk0] at hsub
      refine ⟨⟨d, a⟩, ⟨⟨hd, ?_⟩, ?_⟩, rfl⟩
      · rw [Nat.le_div_iff_mul_le hk1, mul_comm]
        omega
      · omega
    · rintro ⟨⟨d, a⟩, ⟨⟨hd1, _⟩, ha⟩, rfl⟩
      refine ⟨?_, a, d, by omega, rfl⟩
      rw [arithmeticProgression_subset_range hk0]
      omega
  -- Rigidity makes the parameterization injective, so counting APs is
  -- counting parameter pairs, fiber by fiber.
  have hinj : Set.InjOn (fun p : (_ : ℕ) × ℕ => arithmeticProgression p.2 p.1 k)
      (((Finset.Icc 1 ((N - 1) / (k - 1))).sigma
        (fun d => Finset.range (N - (k - 1) * d))) : Finset ((_ : ℕ) × ℕ)) := by
    rintro ⟨d, a⟩ hp ⟨d', a'⟩ hq h
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hp hq
    dsimp only at h
    obtain ⟨ha, hd⟩ := arithmeticProgression_inj hk (by omega) (by omega) h
    subst ha
    subst hd
    rfl
  rw [key, Finset.card_image_of_injOn hinj, Finset.card_sigma]
  simp only [Finset.card_range]

/- ## Part IV: The quantitative lower bound (the open question),
      and the matching quadratic upper bound. -/

/-- **Quantitative lower bound (the open question).** The interval {0,…,N−1}
    contains at least `⌊N/(2(k−1))⌋ · ⌊N/2⌋` k-term APs — order N²/(4(k−1)).
    Proof: every difference d ≤ N/(2(k−1)) leaves at least N − ⌊N/2⌋ ≥ ⌊N/2⌋
    admissible first terms. This is the counterpoint to the parent's
    `countAPs_le_choose`: structured sets have QUADRATICALLY many k-APs,
    the supersaturation order that F_k(N,ℓ) = N^{2−o(1)} concerns. -/
theorem countAPs_range_lower_bound (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    N / (2 * (k - 1)) * (N / 2) ≤ countAPs (Finset.range N) k := by
  have hk1 : 0 < k - 1 := by omega
  rw [countAPs_range_eq_sum N hk]
  -- The small differences d ≤ N/(2(k−1)) form a sub-range of the full index set.
  have hDD : N / (2 * (k - 1)) ≤ (N - 1) / (k - 1) := by
    rw [← Nat.div_div_eq_div_mul]
    exact Nat.div_le_div_right (by omega)
  -- Each small difference admits at least ⌊N/2⌋ first terms.
  have hstep : ∀ d ∈ Finset.Icc 1 (N / (2 * (k - 1))), N / 2 ≤ N - (k - 1) * d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have h1 : (k - 1) * d ≤ (k - 1) * (N / (2 * (k - 1))) :=
      Nat.mul_le_mul le_rfl hd.2
    have h2 : (k - 1) * (N / (2 * (k - 1))) ≤ N / 2 := by
      rw [← Nat.div_div_eq_div_mul, mul_comm (k - 1) (N / 2 / (k - 1))]
      exact Nat.div_mul_le_self _ _
    omega
  calc N / (2 * (k - 1)) * (N / 2)
      = ∑ _d ∈ Finset.Icc 1 (N / (2 * (k - 1))), (N / 2) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
        congr 1
        omega
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / (2 * (k - 1))), (N - (k - 1) * d) :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ d ∈ Finset.Icc 1 ((N - 1) / (k - 1)), (N - (k - 1) * d) :=
        Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right hDD)

/-- **Matching upper bound.** The interval count is at most N², so together
    with the lower bound, countAPs {0,…,N−1} k = Θ(N²) for fixed k ≥ 2. -/
theorem countAPs_range_upper_bound (N : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    countAPs (Finset.range N) k ≤ N * N := by
  rw [countAPs_range_eq_sum N hk]
  calc ∑ d ∈ Finset.Icc 1 ((N - 1) / (k - 1)), (N - (k - 1) * d)
      ≤ ∑ _d ∈ Finset.Icc 1 ((N - 1) / (k - 1)), N :=
        Finset.sum_le_sum (fun d _ => Nat.sub_le _ _)
    _ = (N - 1) / (k - 1) * N := by
        rw [Finset.sum_const, smul_eq_mul, Nat.card_Icc]
        congr 1
        omega
    _ ≤ N * N :=
        Nat.mul_le_mul (le_trans (Nat.div_le_self _ _) (by omega)) le_rfl

/- ## Part V: Existence complement and consistency checks. -/

/-- The AP with first term 0 and difference 1 is the interval itself. -/
theorem arithmeticProgression_zero_one (k : ℕ) :
    arithmeticProgression 0 1 k = Finset.range k := by
  unfold arithmeticProgression
  ext x
  simp

/-- The interval {0,…,N−1} contains a k-term AP iff k ≤ N — existence version
    of the counting bounds. -/
theorem containsAP_range_iff {N k : ℕ} : ContainsAP (Finset.range N) k ↔ k ≤ N := by
  constructor
  · rintro ⟨a, d, hd, hsub⟩
    have hcard := Finset.card_le_card hsub
    rwa [arithmeticProgression_card a d k hd, Finset.card_range] at hcard
  · intro h
    exact ⟨0, 1, one_pos, by
      rw [arithmeticProgression_zero_one]
      exact Finset.range_subset.mpr h⟩

/-- Consistency with the parent's exact 2-AP count: intervals have C(N,2)
    two-term APs. -/
theorem countAPs_range_two (N : ℕ) : countAPs (Finset.range N) 2 = N.choose 2 := by
  rw [countAPs_two, Finset.card_range]

/-- Consistency check: at k = 2 the exact interval formula collapses to the
    triangular number Σ_{d=1}^{N−1} (N − d) = C(N,2). -/
theorem countAPs_range_sum_two (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 (N - 1), (N - d) = N.choose 2 := by
  have h := countAPs_range_eq_sum N (k := 2) le_rfl
  rw [countAPs_range_two] at h
  rw [← h]
  apply Finset.sum_congr
  · norm_num
  · intro d _
    norm_num

end Erdos179Combinatorics
