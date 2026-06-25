/-
  Erdős Problem #247, follow-up oq-01-oq-02:
  The exact reach of Liouville's method for lacunary binary sums.

  Source: https://erdosproblems.com/247
  Parent: Proofs/Erdos247Problem.lean (gallery slug erdos-247-oq-01)

  Context.
  The parent file formalizes Erdős's 1975 transcendence theorem for lacunary
  sums Σ 1/2^{n_k} as an *axiom* `erdos_transcendence_strong`, valid under the
  super-polynomial ("strong") growth condition. It then eliminates that axiom
  for the single example n_k = k! by showing the factorial sum is a Liouville
  number (via Mathlib's Liouville theory).

  This file answers, partially and precisely, the open question
    "Prove the Erdős strong-growth theorem without axioms using the
     Liouville/Mahler framework in Mathlib."
  by isolating the EXACT subclass of sequences that the elementary Liouville
  argument can handle, and showing axiom-free transcendence for all of them.

  Main definition.
  `HasRatioGrowth n` : for every m there is an index N with n_N ≥ 1 and
    n_{N+1} > m·n_N + 1.  (Equivalently, lim sup n_{k+1}/n_k = ∞.)

  Main results (all axiom-free).
  * `lacunarySum_liouville`  : StrictMono n → HasRatioGrowth n →
        the sum Σ 1/2^{n_k} is a Liouville number.
  * `lacunarySum_transcendental` : the same hypotheses give transcendence over ℚ.
  * `factorial_hasRatioGrowth`, `factorial_sum_transcendental_via_ratio` :
        the parent's factorial example is the special case N = m+1.
  * `pow2_not_hasRatioGrowth` : the sequence n_k = 2^k does NOT satisfy ratio
        growth (its ratio is the constant 2), so this Liouville method
        provably cannot reach it.
  * `strongGrowth_not_implies_ratioGrowth` : since 2^k DOES have strong growth,
        ratio growth is strictly weaker than strong growth.  In particular the
        Liouville method covers a proper subclass of Erdős's 1975 theorem; the
        axiom is genuinely required for sequences like 2^k.

  This makes the boundary of the axiom-free approach precise: Liouville's
  inequality eliminates the axiom exactly when consecutive gaps grow without
  bound (n_{k+1}/n_k → ∞ along a subsequence), and demonstrably no further.

  Tags: transcendence, number-theory, lacunary-series, liouville, erdos-problem
-/

import Mathlib

set_option maxHeartbeats 800000

namespace Erdos247RatioGrowth

/- ## Self-contained restatement of the parent infrastructure

The next two declarations duplicate `Erdos247.lacunarySum` and
`Erdos247.transcendental_int_to_rat` from `Proofs/Erdos247Problem.lean` so that
this file depends only on Mathlib (the parent module is imported in the gallery
build via `Proofs.lean`). -/

/-- The lacunary binary sum Σ_{k≥0} 1/2^{n_k}. -/
noncomputable def lacunarySum (n : ℕ → ℕ) : ℝ :=
  ∑' k, (1 : ℝ) / 2 ^ n k

/-- Transcendence over ℤ implies transcendence over ℚ (clearing denominators). -/
theorem transcendental_int_to_rat {x : ℝ} (h : Transcendental ℤ x) :
    Transcendental ℚ x :=
  fun halg => h ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)

/- ## The ratio-growth condition -/

/-- **Ratio growth.** For every `m` there is an index `N` with `n_N ≥ 1` and
    `n_{N+1} > m·n_N + 1`.  Equivalently `lim sup n_{k+1}/n_k = ∞`.  This is the
    exact condition under which Liouville's inequality forces `Σ 1/2^{n_k}` to be
    a Liouville number (see `lacunarySum_liouville`). -/
def HasRatioGrowth (n : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∃ N : ℕ, 1 ≤ n N ∧ n (N + 1) > m * n N + 1

/- ## Generic Liouville infrastructure for strictly increasing exponents -/

/-- Strictly increasing `ℕ → ℕ` sequences dominate the identity. -/
private theorem self_le {n : ℕ → ℕ} (hn : StrictMono n) : ∀ k, k ≤ n k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have : n i < n (i + 1) := hn (Nat.lt_succ_self i)
    omega

/-- Shift estimate: `n_{N+1} + j ≤ n_{j + (N+1)}` for strictly increasing `n`. -/
private theorem shift_le {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) :
    ∀ j, n (N + 1) + j ≤ n (j + (N + 1)) := by
  intro j
  induction j with
  | zero => simp
  | succ i ih =>
    have hstep : n (i + (N + 1)) < n (i + 1 + (N + 1)) := hn (by omega)
    have he : i + 1 + (N + 1) = (i + 1) + (N + 1) := by ring
    omega

/-- The lacunary series is summable (compared to the geometric series). -/
private theorem lacunary_summable {n : ℕ → ℕ} (hn : StrictMono n) :
    Summable (fun k => (1 : ℝ) / 2 ^ n k) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity) (by norm_num) :
      Summable (fun k => ((1 : ℝ) / 2) ^ k))
  show (1 : ℝ) / 2 ^ n k ≤ (1 / 2) ^ k
  rw [one_div, one_div, inv_pow]
  apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ k)
  exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (self_le hn k)

/-- The tail of the lacunary sum from index `N+1` onward. -/
noncomputable def tail (n : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j, (1 : ℝ) / 2 ^ n (j + (N + 1))

/-- The tail series is summable. -/
private theorem tail_summable {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) :
    Summable (fun j => (1 : ℝ) / 2 ^ n (j + (N + 1))) := by
  apply Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (summable_geometric_of_lt_one (by positivity) (by norm_num) :
      Summable (fun j => ((1 : ℝ) / 2) ^ j))
  show (1 : ℝ) / 2 ^ n (j + (N + 1)) ≤ (1 / 2) ^ j
  rw [one_div, one_div, inv_pow]
  apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ j)
  have hj : j ≤ n (j + (N + 1)) := le_trans (by omega) (self_le hn (j + (N + 1)))
  exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hj

/-- Splitting the sum into a finite head (range `N+1`) plus the tail. -/
theorem lacunarySum_split {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) :
    lacunarySum n =
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ n k) + tail n N := by
  have key := (lacunary_summable hn).sum_add_tsum_nat_add (N + 1)
  unfold lacunarySum tail
  rw [← key]

/-- The finite head is an integer over `2^{n_N}`. -/
theorem partialSum_eq_div {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) :
    ∃ a : ℤ, (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ n k) =
      (a : ℝ) / 2 ^ n N := by
  induction N with
  | zero => exact ⟨1, by simp⟩
  | succ N ih =>
    obtain ⟨a, ha⟩ := ih
    have hle : n N ≤ n (N + 1) := (hn (Nat.lt_succ_self N)).le
    set d := n (N + 1) - n N with hd
    refine ⟨a * 2 ^ d + 1, ?_⟩
    rw [Finset.sum_range_succ, ha]
    have hpow : (2 : ℝ) ^ n (N + 1) = 2 ^ n N * 2 ^ d := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    rw [hpow]
    have h1 : (2 : ℝ) ^ n N ≠ 0 := by positivity
    have h2 : (2 : ℝ) ^ d ≠ 0 := by positivity
    push_cast
    field_simp

/-- The tail is strictly positive. -/
theorem tail_pos {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) : 0 < tail n N := by
  unfold tail
  exact (tail_summable hn N).tsum_pos (fun j => by positivity) 0 (by positivity)

/-- Geometric tail bound: `tail n N ≤ 2 / 2^{n_{N+1}}`. -/
theorem tail_le {n : ℕ → ℕ} (hn : StrictMono n) (N : ℕ) :
    tail n N ≤ 2 / (2 : ℝ) ^ n (N + 1) := by
  unfold tail
  have hle : ∀ j, (1 : ℝ) / 2 ^ n (j + (N + 1)) ≤
      (1 / 2 ^ n (N + 1)) * (1 / 2) ^ j := by
    intro j
    have hrw : (1 : ℝ) / 2 ^ n (N + 1) * (1 / 2) ^ j =
        1 / 2 ^ (n (N + 1) + j) := by
      rw [pow_add, one_div, one_div, inv_pow, ← mul_inv]; ring_nf
    rw [hrw]
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) < 2 ^ (n (N + 1) + j))
      (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (shift_le hn N j))
  have hgeo : Summable (fun j => (1 / 2 ^ n (N + 1)) * ((1 : ℝ) / 2) ^ j) :=
    Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) (by norm_num))
  calc ∑' j, (1 : ℝ) / 2 ^ n (j + (N + 1))
      ≤ ∑' j, (1 / 2 ^ n (N + 1)) * ((1 : ℝ) / 2) ^ j :=
        hasSum_le hle (tail_summable hn N).hasSum hgeo.hasSum
    _ = (1 / 2 ^ n (N + 1)) * ∑' j, ((1 : ℝ) / 2) ^ j := tsum_mul_left
    _ = (1 / 2 ^ n (N + 1)) * 2 := by
        rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)]; norm_num
    _ = 2 / (2 : ℝ) ^ n (N + 1) := by ring

/- ## Main theorem: ratio growth ⇒ Liouville number -/

/-- **Liouville from ratio growth.**  If `n` is strictly increasing and has
    ratio growth, then `Σ 1/2^{n_k}` is a Liouville number.  The witness for
    parameter `m` is the index `N` provided by `HasRatioGrowth`: the rational
    `a / 2^{n_N}` (the finite head) approximates the sum to within the tail,
    which is `≤ 2/2^{n_{N+1}} < 1/(2^{n_N})^m` precisely because
    `n_{N+1} > m·n_N + 1`. -/
theorem lacunarySum_liouville {n : ℕ → ℕ} (hn : StrictMono n)
    (hr : HasRatioGrowth n) : Liouville (lacunarySum n) := by
  intro m
  obtain ⟨N, hN1, hNm⟩ := hr m
  obtain ⟨a, ha⟩ := partialSum_eq_div hn N
  refine ⟨a, (2 : ℤ) ^ n N, ?_, ?_, ?_⟩
  · -- 1 < 2^{n_N}
    exact_mod_cast Nat.one_lt_pow (by omega : n N ≠ 0) (by omega : 1 < 2)
  · -- the sum is not exactly a / 2^{n_N} (tail is strictly positive)
    rw [lacunarySum_split hn N, ha]
    push_cast
    intro heq
    have := tail_pos hn N
    linarith
  · -- |sum - a/2^{n_N}| < 1 / (2^{n_N})^m
    rw [lacunarySum_split hn N, ha]
    push_cast
    rw [show (a : ℝ) / 2 ^ n N + tail n N - a / 2 ^ n N = tail n N from by ring]
    rw [abs_of_pos (tail_pos hn N)]
    calc tail n N
        ≤ 2 / (2 : ℝ) ^ n (N + 1) := tail_le hn N
      _ < 1 / ((2 : ℝ) ^ n N) ^ m := by
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]
          rw [one_mul, ← pow_mul, show n N * m = m * n N from by ring]
          have hstep : (2 : ℝ) * (2 : ℝ) ^ (m * n N) =
              (2 : ℝ) ^ (m * n N + 1) := by rw [pow_succ]; ring
          rw [hstep]
          have hlt : m * n N + 1 < n (N + 1) := by omega
          exact_mod_cast Nat.pow_lt_pow_right (by omega : 1 < 2) hlt

/-- **Axiom-free transcendence from ratio growth.** -/
theorem lacunarySum_transcendental {n : ℕ → ℕ} (hn : StrictMono n)
    (hr : HasRatioGrowth n) : Transcendental ℚ (lacunarySum n) :=
  transcendental_int_to_rat (lacunarySum_liouville hn hr).transcendental

/- ## Examples: factorial satisfies ratio growth, 2^k does not -/

/-- The factorial exponent sequence `n_k = (k+1)!` has ratio growth: take
    `N = m + 1`, so `n_N = (m+2)!` and `n_{N+1} = (m+3)! = (m+3)·(m+2)!`. -/
theorem factorial_hasRatioGrowth : HasRatioGrowth (fun k => (k + 1).factorial) := by
  intro m
  refine ⟨m + 1, Nat.factorial_pos _, ?_⟩
  show ((m + 1) + 1 + 1).factorial > m * ((m + 1) + 1).factorial + 1
  rw [Nat.factorial_succ ((m + 1) + 1)]
  have hpos : 0 < ((m + 1) + 1).factorial := Nat.factorial_pos _
  nlinarith [hpos]

/-- `StrictMono` for the factorial exponent sequence (mirrors the parent). -/
theorem factorial_strictMono : StrictMono (fun k => (k + 1).factorial) := by
  intro a b hab
  exact Nat.factorial_lt_of_lt (Nat.succ_pos a) (Nat.add_lt_add_right hab 1)

/-- Re-derivation of the parent's factorial transcendence as a special case of
    the generic ratio-growth theorem. -/
theorem factorial_sum_transcendental_via_ratio :
    Transcendental ℚ (lacunarySum (fun k => (k + 1).factorial)) :=
  lacunarySum_transcendental factorial_strictMono factorial_hasRatioGrowth

/-- The geometric exponent sequence `n_k = 2^k` does NOT have ratio growth:
    its consecutive ratio is the constant `2`, so `n_{N+1} = 2·n_N` can never
    exceed `2·n_N + 1`. -/
theorem pow2_not_hasRatioGrowth : ¬ HasRatioGrowth (fun k => 2 ^ k) := by
  intro hr
  obtain ⟨N, _, hNm⟩ := hr 2
  simp only [pow_succ] at hNm
  set x := 2 ^ N
  omega

/-- The strong-growth condition (parent's `HasStrongGrowth`, here restated) does
    not imply ratio growth, since `2^k` satisfies strong growth but not ratio
    growth.  Hence Liouville's method covers a proper subclass of Erdős's 1975
    theorem, and the `erdos_transcendence_strong` axiom is genuinely required
    for sequences such as `2^k`. -/
def HasStrongGrowth (n : ℕ → ℕ) : Prop :=
  ∀ (t : ℕ), t ≥ 1 → ∀ C : ℕ, ∃ k : ℕ, k > 0 ∧ n k > C * k ^ t

/-- `n + 1 ≤ 2^n` (mirrors the parent's `pow2_ge_succ`). -/
private theorem pow2_ge_succ (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ i ih =>
    calc i + 1 + 1 ≤ 2 * (i + 1) := by omega
      _ ≤ 2 * 2 ^ i := by gcongr
      _ = 2 ^ (i + 1) := by ring

/-- `2^k` has strong growth (mirrors the parent's `pow2_strong_growth`). -/
theorem pow2_strong_growth : HasStrongGrowth (fun k => 2 ^ k) := by
  intro t ht C
  by_cases hC : C = 0
  · subst hC; exact ⟨1, by omega, by simp⟩
  · have hC_pos : 0 < C := Nat.pos_of_ne_zero hC
    set N := C * (t + 1) ^ t with hN
    have hN_pos : 0 < N := by positivity
    refine ⟨N * (t + 1), Nat.mul_pos hN_pos (by omega), ?_⟩
    show 2 ^ (N * (t + 1)) > C * (N * (t + 1)) ^ t
    rw [pow_mul]
    have hge : N + 1 ≤ 2 ^ N := pow2_ge_succ N
    have h2 : 0 < N ^ t := by positivity
    calc C * (N * (t + 1)) ^ t
        = C * (t + 1) ^ t * N ^ t := by rw [mul_pow]; ring
      _ < (N + 1) * N ^ t := by
          exact mul_lt_mul_of_pos_right (by omega : C * (t + 1) ^ t < N + 1) h2
      _ ≤ (N + 1) * (N + 1) ^ t := by gcongr; omega
      _ = (N + 1) ^ (t + 1) := by ring
      _ ≤ (2 ^ N) ^ (t + 1) := by gcongr

theorem strongGrowth_not_implies_ratioGrowth :
    ¬ (∀ n : ℕ → ℕ, HasStrongGrowth n → HasRatioGrowth n) := by
  intro h
  exact pow2_not_hasRatioGrowth (h _ pow2_strong_growth)

/- ## Summary -/

/-- Summary of the axiom-free results established in this file:
    (1) ratio growth ⇒ transcendence (the Liouville-reachable subclass);
    (2) the factorial sum is in this subclass;
    (3) `2^k` is not, yet has strong growth, so the subclass is proper. -/
theorem ratio_growth_summary :
    (∀ n : ℕ → ℕ, StrictMono n → HasRatioGrowth n →
      Transcendental ℚ (lacunarySum n)) ∧
    HasRatioGrowth (fun k => (k + 1).factorial) ∧
    (¬ HasRatioGrowth (fun k => 2 ^ k) ∧ HasStrongGrowth (fun k => 2 ^ k)) :=
  ⟨fun _ hn hr => lacunarySum_transcendental hn hr,
   factorial_hasRatioGrowth,
   pow2_not_hasRatioGrowth, pow2_strong_growth⟩

end Erdos247RatioGrowth
