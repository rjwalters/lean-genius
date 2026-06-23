import Mathlib

/-
# Erdos Problem #839: Sequences Avoiding Consecutive-Term Sums

Erdos Problem #839 considers sequences 1 <= a_1 < a_2 < ... where no term
equals a sum of consecutive earlier terms (i.e., a_m != a_i + a_{i+1} + ... + a_j
for any i <= j < m). Two questions are posed:

1. Is lim sup(a_n/n) = infinity?
2. Does (1/log x) * sum_{a_n < x} 1/a_n -> 0?

Known:
- lim inf(a_n/n) < infinity is achievable
- sum 1/a_n >= c * log log x is possible
- Upper density can reach 19/36 (Freud), disproving Erdos's conjecture of 1/2

Reference: https://erdosproblems.com/839
-/

-- ## Definitions

/-- The sum of consecutive terms a_i + a_{i+1} + ... + a_j. -/
def consecutiveSum (a : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ∑ k ∈ Finset.Icc i j, a k

/-- No term of the sequence equals a sum of consecutive earlier terms. -/
def AvoidConsecutiveSums (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∀ i j : ℕ, i ≤ j → j < m →
    a m ≠ consecutiveSum a i j

/-- The set of all valid sequences (strictly increasing, positive, avoiding
    consecutive-term sums). -/
def ValidSeq := { a : ℕ → ℕ //
  (∀ n, 0 < a n) ∧ (∀ i j, i < j → a i < a j) ∧ AvoidConsecutiveSums a }

-- ## Growth Rate Questions

/-- Question 1: Is lim sup(a_n/n) = infinity for every valid sequence? -/
def Question1 : Prop :=
  ∀ a : ValidSeq, ∀ C : ℝ, ∃ n : ℕ, C < (a.val n : ℝ) / (n + 1 : ℝ)

/-- Question 2: Does the logarithmic density vanish?
    (1/log x) * sum_{a_n < x} 1/a_n -> 0 as x -> infinity. -/
def Question2 : Prop :=
  ∀ a : ValidSeq, ∀ ε : ℝ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n ∈ (Finset.range X).filter (fun n => a.val n < X),
        (1 : ℝ) / (a.val n : ℝ)) ≤ ε * Real.log X

-- ## Structural Theorems

/-- A valid sequence satisfies a(n) >= n + 1, by strict monotonicity
    and positivity (a(0) >= 1). -/
theorem valid_seq_lower_bound (a : ValidSeq) (n : ℕ) :
    n + 1 ≤ a.val n := by
  induction n with
  | zero => exact a.property.1 0
  | succ k ih =>
    have hlt := a.property.2.1 k (k + 1) (Nat.lt_succ_of_le le_rfl)
    omega

/-- The consecutive sum of a single term a_i equals a_i. -/
theorem consecutiveSum_single (a : ℕ → ℕ) (i : ℕ) :
    consecutiveSum a i i = a i := by
  simp [consecutiveSum, Finset.Icc_self]

/-- In a valid sequence, no term equals any single earlier term
    (follows from strict monotonicity). -/
theorem valid_seq_no_repeat (a : ValidSeq) (m j : ℕ) (hjm : j < m) :
    a.val m ≠ a.val j := by
  have := a.property.2.1 j m hjm
  omega

/-- The avoid-consecutive-sums property implies no term equals any
    single earlier term (special case of the definition). -/
theorem avoid_implies_no_single_match (a : ValidSeq) (m j : ℕ) (hjm : j < m) :
    a.val m ≠ consecutiveSum a.val j j := by
  exact a.property.2.2 m j j le_rfl hjm

/-- Consecutive sum over an interval [i, j] with i > j is zero (empty sum). -/
theorem consecutiveSum_empty (a : ℕ → ℕ) (i j : ℕ) (h : j < i) :
    consecutiveSum a i j = 0 := by
  simp [consecutiveSum, Finset.Icc_eq_empty (by omega : ¬ i ≤ j)]

/-- For a sequence with positive terms, the consecutive sum over [i, j] is
    at least a(i). -/
theorem consecutiveSum_ge_first (a : ℕ → ℕ) (i j : ℕ) (h : i ≤ j)
    (_hpos : ∀ n, 0 < a n) :
    a i ≤ consecutiveSum a i j := by
  unfold consecutiveSum
  calc a i = ∑ t ∈ {i}, a t := by simp
    _ ≤ ∑ t ∈ Finset.Icc i j, a t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx; simp at hx; subst hx; simp [Finset.mem_Icc, h]
        · intro _ _ _; omega

/-- For a strictly increasing positive sequence, the consecutive sum over [i, j]
    with i < j is strictly greater than a(i). -/
theorem consecutiveSum_gt_first (a : ValidSeq) (i j : ℕ) (h : i < j) :
    a.val i < consecutiveSum a.val i j := by
  unfold consecutiveSum
  have hij : i ≠ j := by omega
  have hpos_j : 0 < a.val j := a.property.1 j
  calc a.val i < a.val i + a.val j := by omega
    _ = ∑ t ∈ ({i, j} : Finset ℕ), a.val t := by
        rw [Finset.sum_pair hij]
    _ ≤ ∑ t ∈ Finset.Icc i j, a.val t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp [Finset.mem_Icc] at hx ⊢
          rcases hx with rfl | rfl <;> omega
        · intro _ _ _; omega

/-- For a valid sequence, a(n) grows at least linearly: a(n) >= n + 1. -/
theorem valid_seq_linear_growth (a : ValidSeq) :
    ∀ n : ℕ, (n : ℝ) + 1 ≤ (a.val n : ℝ) := by
  intro n
  have := valid_seq_lower_bound a n
  exact_mod_cast this

-- ## Known Results (axioms for deep constructions)

/-- The reciprocal sum can grow at least as fast as c * log log x. -/
/-- The upper density of a valid sequence. -/
noncomputable def upperDensity (a : ValidSeq) : ℝ :=
  Filter.limsup (fun N : ℕ =>
    ((Finset.range N).filter (fun n => a.val n ≤ N)).card / (N : ℝ))
    Filter.atTop

/-- The Freud construction achieves upper density 19/36. -/
axiom freud_density :
  ∃ a : ValidSeq, upperDensity a = 19 / 36

/-- Erdos conjectured the upper density is at most 1/2, but
    Freud disproved this by constructing a sequence with density 19/36.
    This follows from freud_density since 19/36 > 1/2. -/
theorem freud_counterexample :
    ∃ a : ValidSeq, (1 : ℝ) / 2 < upperDensity a := by
  obtain ⟨a, ha⟩ := freud_density
  exact ⟨a, by rw [ha]; norm_num⟩

-- ## Deriving liminf_finite from freud_density
--
-- Key insight: positive upper density forces liminf(a_n/n) < ∞.
-- If upperDensity = 19/36, then frequently count(N)/N > 1/4,
-- so frequently the N/4-th term is ≤ N, giving a(n)/(n+1) < 4.

section LiminfFinite

private noncomputable def countRatio (a : ValidSeq) (N : ℕ) : ℝ :=
  ((Finset.range N).filter (fun n => a.val n ≤ N)).card / (N : ℝ)

private lemma countRatio_nonneg (a : ValidSeq) (N : ℕ) : 0 ≤ countRatio a N :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The counting ratio is cobounded under ≤ (any eventual upper bound is ≥ 0,
    since the ratio is always ≥ 0). Follows the Erdos929 pattern. -/
private lemma countRatio_isCoboundedUnder (a : ValidSeq) :
    Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop (countRatio a) := by
  refine ⟨0, fun c hc => ?_⟩
  by_contra hlt; push_neg at hlt
  simp only [Filter.eventually_map] at hc
  obtain ⟨N, hN⟩ := hc.exists
  linarith [countRatio_nonneg a N]

/-- If c < limsup f, then frequently c < f. Proved by contrapositive:
    if eventually f ≤ c, then limsup ≤ c. -/
private lemma frequently_lt_of_lt_limsup (a : ValidSeq) (c : ℝ)
    (hlt : c < Filter.limsup (countRatio a) Filter.atTop) :
    ∃ᶠ N in Filter.atTop, c < countRatio a N := by
  by_contra h
  rw [Filter.not_frequently] at h
  have h_ev : ∀ᶠ N in Filter.atTop, countRatio a N ≤ c :=
    h.mono fun _ hn => le_of_not_lt hn
  linarith [Filter.limsup_le_of_le (countRatio_isCoboundedUnder a) h_ev]

/-- For a strictly increasing sequence, if the counting function at N
    has card ≥ k+1, then a(k) ≤ N.
    Proof: by contradiction. If a(k) > N, then all filter elements are < k
    (by monotonicity), so card ≤ k, contradicting card ≥ k+1. -/
lemma term_le_of_count_gt (a : ValidSeq) (N k : ℕ)
    (hcard : k + 1 ≤ ((Finset.range N).filter (fun n => a.val n ≤ N)).card) :
    a.val k ≤ N := by
  by_contra h
  push_neg at h
  have h_bound : ∀ m ∈ (Finset.range N).filter (fun n => a.val n ≤ N), m < k := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    by_contra h_not
    push_neg at h_not
    rcases eq_or_lt_of_le h_not with rfl | hlt
    · omega
    · have := a.property.2.1 k m hlt; omega
  have h_sub : (Finset.range N).filter (fun n => a.val n ≤ N) ⊆ Finset.range k :=
    fun m hm => Finset.mem_range.mpr (h_bound m hm)
  have : ((Finset.range N).filter (fun n => a.val n ≤ N)).card ≤ k :=
    (Finset.card_le_card h_sub).trans (Finset.card_range k).le
  omega

/-- lim inf(a_n/n) can be finite: proved from freud_density.
    Since Freud's sequence has upper density 19/36 > 0, the counting
    function is frequently large, forcing a(n)/(n+1) < 4 infinitely often. -/
theorem liminf_finite :
    ∃ a : ValidSeq, ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (a.val n : ℝ) / (n + 1 : ℝ) ≤ C := by
  obtain ⟨a, ha⟩ := freud_density
  refine ⟨a, 4, by norm_num, fun M => ?_⟩
  -- upperDensity a = 19/36, and countRatio is the same function
  have h_eq : Filter.limsup (countRatio a) Filter.atTop = upperDensity a := rfl
  -- 1/4 < 19/36 = upperDensity a
  have hlt : (1 : ℝ) / 4 < Filter.limsup (countRatio a) Filter.atTop := by
    rw [h_eq, ha]; norm_num
  -- Frequently countRatio > 1/4
  have hfreq := frequently_lt_of_lt_limsup a (1 / 4) hlt
  rw [Filter.frequently_atTop] at hfreq
  -- Get N ≥ 4*(M+1) with countRatio > 1/4
  obtain ⟨N, hNM, hcount_ratio⟩ := hfreq (4 * (M + 1))
  -- N ≥ 4*(M+1) ≥ 4 > 0
  have hN_pos : 0 < N := by omega
  -- Extract N < 4 * count from 1/4 < count/N
  set cnt := ((Finset.range N).filter (fun n => a.val n ≤ N)).card with hcnt_def
  have h_Nlt4cnt : (N : ℝ) < 4 * (cnt : ℝ) := by
    unfold countRatio at hcount_ratio
    rw [div_lt_div_iff (by norm_num : (0 : ℝ) < 4)
        (by exact_mod_cast hN_pos : (0 : ℝ) < (N : ℝ))] at hcount_ratio
    linarith
  -- cnt ≥ M + 2 (so cnt - 1 ≥ M + 1 > M)
  have h_cnt_large : M + 2 ≤ cnt := by
    have h1 : (N : ℝ) ≥ 4 * ((M : ℝ) + 1) := by exact_mod_cast hNM
    have h2 : (M + 1 : ℝ) < (cnt : ℝ) := by linarith
    have h3 : M + 1 < cnt := by exact_mod_cast h2
    omega
  -- Set n = cnt - 1
  refine ⟨cnt - 1, by omega, ?_⟩
  -- a(cnt-1) ≤ N from the counting argument
  have h_bound : a.val (cnt - 1) ≤ N :=
    term_le_of_count_gt a N (cnt - 1) (by omega)
  -- cnt - 1 + 1 = cnt (since cnt ≥ 2)
  have h_cast_eq : ((cnt - 1 : ℕ) : ℝ) + 1 = (cnt : ℝ) := by
    have := Nat.sub_add_cancel (show 1 ≤ cnt by omega)
    exact_mod_cast this
  -- a(cnt-1)/(cnt-1+1) = a(cnt-1)/cnt ≤ N/cnt < 4
  rw [h_cast_eq]
  have h_cnt_pos : (0 : ℝ) < (cnt : ℝ) := by exact_mod_cast (show 0 < cnt by omega)
  rw [div_le_iff h_cnt_pos]
  calc (a.val (cnt - 1) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h_bound
    _ ≤ 4 * (cnt : ℝ) := by linarith

end LiminfFinite

-- ## Main Open Questions

/-- Erdos Problem #839, Question 1: Is lim sup(a_n/n) = infinity? -/
/-- Erdos Problem #839, Question 2: Does the logarithmic density vanish? -/
