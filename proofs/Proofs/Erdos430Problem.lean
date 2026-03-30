/-
# Erdős Problem #430: Composite Numbers in Greedy Large-Factor Sequences

Erdős Problem #430 considers a greedy decreasing sequence in [1,n) defined by:
- a₁ = n - 1
- aₖ is the greatest integer in [1, aₖ₋₁) whose prime factors all exceed n - aₖ

The question asks: for sufficiently large n, must this sequence contain at
least one composite number?

Selfridge's preliminary calculations suggest yes, but no proof is known.
The problem is equivalent to the first part of Erdős Problem #385 (observed
by Sarosh Adenwalla).

Reference: https://erdosproblems.com/430
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic

/- ## Definitions -/

/-- The smallest prime factor of n, or n itself if n ≤ 1. -/
def minPrimeFactor (n : ℕ) : ℕ :=
  if 2 ≤ n then Nat.minFac n else n

/-- All prime factors of m exceed a given bound k. -/
def allPrimeFactorsExceed (m k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ m → k < p

/-- Decidability of allPrimeFactorsExceed via bounded quantification.
    For m > 0, any divisor p satisfies p ≤ m, so we check p ∈ [0, m].
    For m = 0, every prime divides 0, so the condition reduces to k < 2. -/
instance decidableAllPrimeFactorsExceed (m k : ℕ) :
    Decidable (allPrimeFactorsExceed m k) :=
  if hm : m = 0 then
    if hk : k < 2 then
      .isTrue (by subst hm; intro p hp _; exact lt_of_lt_of_le hk hp.two_le)
    else
      .isFalse (by subst hm; intro h; exact hk (h 2 Nat.prime_two (dvd_zero 2)))
  else
    decidable_of_iff
      (∀ p ∈ Finset.range (m + 1), p.Prime → p ∣ m → k < p)
      ⟨fun h p hp hd =>
         h p (Finset.mem_range.mpr
           (Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd))) hp hd,
       fun h p _ hp hd => h p hp hd⟩

/-- An integer m ∈ [1, n) is admissible at level n if all prime factors
    of m exceed n - m. -/
def IsAdmissible (n m : ℕ) : Prop :=
  1 ≤ m ∧ m < n ∧ allPrimeFactorsExceed m (n - m)

/-- Decidability of IsAdmissible, using the decidability of allPrimeFactorsExceed. -/
instance decidableIsAdmissible (n m : ℕ) : Decidable (IsAdmissible n m) :=
  inferInstanceAs (Decidable (1 ≤ m ∧ m < n ∧ allPrimeFactorsExceed m (n - m)))

/-- The greedy next element: the greatest integer in [1, prev) that is
    admissible at level n. Returns 0 if no such element exists. -/
def greedyNext (n prev : ℕ) : ℕ :=
  Finset.sup ((Finset.Icc 1 (prev - 1)).filter
    (fun m => decide (IsAdmissible n m) = true)) id

/- ## The Greedy Sequence -/

/-- The greedy large-factor sequence starting from n-1.
    greedySeq n 0 = n - 1, and greedySeq n (k+1) = greedyNext n (greedySeq n k). -/
def greedySeq (n : ℕ) : ℕ → ℕ
  | 0 => n - 1
  | k + 1 => greedyNext n (greedySeq n k)

/-- The sequence terminates at step k if greedySeq n k = 0. -/
def seqTerminates (n k : ℕ) : Prop :=
  greedySeq n k = 0

/-- The sequence contains a composite number. -/
def hasComposite (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < greedySeq n k ∧ ¬ (greedySeq n k).Prime ∧ 1 < greedySeq n k

/- ## Example: n = 8 -/

/-- For n = 8: a₁ = 7 (prime, all factors > 8-7=1),
    a₂ = 5 (prime, all factors > 8-5=3), then sequence terminates.
    No composite appears. Small n may not have composites.
    PROVED by native_decide (greedySeq is now computable). -/
theorem example_n8 : greedySeq 8 0 = 7 ∧ greedySeq 8 1 = 5 := by native_decide

/- ## Greedy Sequence Properties -/

/-- greedyNext returns an admissible element when positive.
    This follows from the Finset.sup/filter construction: if sup > 0,
    the filtered set is nonempty and the sup (= max) is in the set. -/
private lemma greedyNext_admissible (n prev : ℕ) (h : greedyNext n prev > 0) :
    IsAdmissible n (greedyNext n prev) := by
  unfold greedyNext at h ⊢
  set S := (Finset.Icc 1 (prev - 1)).filter
    (fun m => decide (IsAdmissible n m) = true)
  -- sup S id > 0 implies S is nonempty
  have hne : S.Nonempty := by
    by_contra hempty
    simp [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sup_empty] at h
  -- sup = max' for nonempty finsets of ℕ
  have hsup_eq : S.sup id = S.max' hne :=
    le_antisymm (Finset.sup_le fun b hb => Finset.le_max' S b hb)
      (Finset.le_sup (f := id) (Finset.max'_mem S hne))
  -- max' is in the set, so sup is in the set
  have hmem : S.sup id ∈ S := hsup_eq ▸ Finset.max'_mem S hne
  -- Extract IsAdmissible from filter membership
  exact of_decide_eq_true (Finset.mem_filter.mp hmem).2

/-- Every positive element of the greedy sequence is admissible. -/
private lemma greedySeq_admissible (n k : ℕ) (h : greedySeq n k > 0) (hn : n ≥ 2) :
    IsAdmissible n (greedySeq n k) := by
  induction k with
  | zero =>
    simp only [greedySeq] at h ⊢
    refine ⟨by omega, by omega, fun p hp _ => ?_⟩
    have : n - (n - 1) = 1 := by omega
    rw [this]
    exact hp.one_lt
  | succ k _ =>
    simp only [greedySeq] at h ⊢
    exact greedyNext_admissible n (greedySeq n k) h

/-- greedyNext is strictly less than the previous value, when positive.
    This follows because greedyNext selects from [1, prev-1]. -/
private lemma greedyNext_lt (n prev : ℕ) (h : 0 < greedyNext n prev) :
    greedyNext n prev < prev := by
  unfold greedyNext at h ⊢
  set S := (Finset.Icc 1 (prev - 1)).filter
    (fun m => decide (IsAdmissible n m) = true)
  have hne : S.Nonempty := by
    by_contra hempty
    simp [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sup_empty] at h
  have : S.sup id ≤ prev - 1 :=
    Finset.sup_le fun b hb => (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
  omega

/-- The greedy sequence is bounded: greedySeq n k ≤ n - 1 - k.
    When k ≥ n - 1, this implies the sequence has reached 0. -/
theorem greedySeq_le (n k : ℕ) : greedySeq n k ≤ n - 1 - k := by
  induction k with
  | zero => simp [greedySeq]
  | succ k ih =>
    simp only [greedySeq]
    by_cases h : 0 < greedyNext n (greedySeq n k)
    · have := greedyNext_lt n (greedySeq n k) h
      omega
    · omega

/-- The greedy sequence always terminates: by step n, the sequence is 0.
    Together with strict decrease while positive, the sequence has at most
    n - 1 nonzero terms. -/
theorem greedySeq_terminates (n : ℕ) : greedySeq n n = 0 := by
  have := greedySeq_le n n; omega

/- ## Connection to Problem #385 -/

/-- Erdős Problem #385 (first part): for large n, there exists a composite
    m < n such that all prime divisors of m exceed n - m.
    Adenwalla observed this is equivalent to Problem #430. -/
theorem erdos_385_equivalence :
  (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → hasComposite n) ↔
  (∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ m : ℕ, 1 < m ∧ m < n ∧ ¬ m.Prime ∧ allPrimeFactorsExceed m (n - m)) := by
  constructor
  · -- Forward: greedy composite → admissible composite
    intro ⟨N₀, hN₀⟩
    use max N₀ 2
    intro n hn
    have hn2 : n ≥ 2 := le_trans (le_max_right _ _) hn
    obtain ⟨k, hpos, hnprime, hgt1⟩ := hN₀ n (le_trans (le_max_left _ _) hn)
    have hadm := greedySeq_admissible n k hpos hn2
    exact ⟨greedySeq n k, hgt1, hadm.2.1, hnprime, hadm.2.2⟩
  · -- Backward: ∃ admissible composite → greedy hits some composite
    -- Key insight: if m is admissible and m < n-1, the greedy sequence
    -- (starting at n-1, strictly decreasing) is bounded below by m at
    -- each step (since m is always a valid candidate), so it must reach m.
    intro ⟨N₀, hN₀⟩
    use max N₀ 2
    intro n hn
    obtain ⟨m, hm_gt1, hm_lt_n, hm_not_prime, hm_factors⟩ :=
      hN₀ n (le_trans (le_max_left _ _) hn)
    have hn2 : n ≥ 2 := le_trans (le_max_right _ _) hn
    have hm_adm : IsAdmissible n m := ⟨by omega, hm_lt_n, hm_factors⟩
    -- Key lemma: greedyNext n prev ≥ m when prev > m (m is always a valid candidate)
    have greedyNext_ge_m : ∀ prev, m < prev → m ≤ greedyNext n prev := by
      intro prev hprev
      unfold greedyNext
      apply Finset.le_sup (f := id)
      simp only [Finset.mem_filter, Finset.mem_Icc, id]
      exact ⟨⟨by omega, by omega⟩, decide_eq_true hm_adm⟩
    -- Descent: the sequence reaches m by strong induction on the gap (current - m)
    suffices ∃ k, greedySeq n k = m by
      obtain ⟨k, hk⟩ := this
      exact ⟨k, by rw [hk]; omega, by rw [hk]; exact hm_not_prime, by rw [hk]; exact hm_gt1⟩
    -- By strong induction on (greedySeq n k - m): show if f(k) ≥ m, some k' has f(k') = m
    have h0_ge : m ≤ greedySeq n 0 := by simp [greedySeq]; omega
    suffices ∀ d, ∀ k₀, greedySeq n k₀ = m + d → ∃ k, greedySeq n k = m by
      exact this (greedySeq n 0 - m) 0 (by omega)
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro k₀ hk₀
      rcases d with _ | d
      · exact ⟨k₀, by omega⟩
      · -- greedySeq n k₀ = m + d + 1 > m, so greedyNext picks from ≥ m
        have h_next_ge : m ≤ greedySeq n (k₀ + 1) := by
          show m ≤ greedyNext n (greedySeq n k₀)
          exact greedyNext_ge_m (greedySeq n k₀) (by omega)
        have h_next_lt : greedySeq n (k₀ + 1) < greedySeq n k₀ := by
          show greedyNext n (greedySeq n k₀) < greedySeq n k₀
          apply greedyNext_lt
          have := greedyNext_ge_m (greedySeq n k₀) (by omega)
          omega
        -- The gap decreased: greedySeq n (k₀+1) - m < d + 1
        exact ih (greedySeq n (k₀ + 1) - m) (by omega) (k₀ + 1) (by omega)

/- ## Main Conjecture -/

/-- Erdős Problem #430: For sufficiently large n, the greedy large-factor
    sequence starting from n-1 must contain at least one composite number.
    Selfridge's calculations support this, but no proof is known. -/
axiom erdos_430_conjecture :
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → hasComposite n

/- ## Auxiliary: Prime Elements Dominate for Small n -/

/-- greedyNext applied to 0 returns 0: the candidate set Icc 1 (0-1) = Icc 1 0 is empty. -/
private lemma greedyNext_zero (n : ℕ) : greedyNext n 0 = 0 := by
  unfold greedyNext
  have : Finset.Icc 1 (0 - 1 : ℕ) = ∅ := Finset.Icc_eq_empty (by omega)
  simp [this]

/-- For n ≤ 1, the greedy sequence is identically 0. -/
private lemma greedySeq_zero_of_le_one {n : ℕ} (hn : n ≤ 1) (k : ℕ) :
    greedySeq n k = 0 := by
  induction k with
  | zero => simp [greedySeq]; omega
  | succ k ih => simp only [greedySeq]; rw [ih]; exact greedyNext_zero n

/-- For small n (specifically n ≤ 1), the sequence consists entirely of zeros,
    so every positive element is vacuously prime or 1. -/
theorem small_n_all_prime :
  ∃ n₀ : ℕ, ∀ n : ℕ, n ≤ n₀ →
    ∀ k : ℕ, 0 < greedySeq n k → (greedySeq n k).Prime ∨ greedySeq n k = 1 :=
  ⟨1, fun n hn k hpos => absurd (greedySeq_zero_of_le_one hn k) (by omega)⟩
