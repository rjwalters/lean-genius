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

/-- lim inf(a_n/n) can be finite: there exist valid sequences where
    a_n/n stays bounded infinitely often. -/
axiom liminf_finite :
  ∃ a : ValidSeq, ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (a.val n : ℝ) / (n + 1 : ℝ) ≤ C

/-- The reciprocal sum can grow at least as fast as c * log log x. -/
axiom reciprocal_sum_lower :
  ∃ a : ValidSeq, ∃ c : ℝ, 0 < c ∧
    ∀ X : ℕ, 3 ≤ X →
      c * Real.log (Real.log X) ≤
        ∑ n ∈ (Finset.range X).filter (fun n => a.val n < X),
          (1 : ℝ) / (a.val n : ℝ)

-- ## Upper Density

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

-- ## Main Open Questions

/-- Erdos Problem #839, Question 1: Is lim sup(a_n/n) = infinity? -/
axiom erdos_839_question1 : Question1

/-- Erdos Problem #839, Question 2: Does the logarithmic density vanish? -/
axiom erdos_839_question2 : Question2
