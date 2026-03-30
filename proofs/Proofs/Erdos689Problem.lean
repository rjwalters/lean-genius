-- Erdős Problem #689 — Double Covering by Prime Congruence Classes
--
-- For sufficiently large n, can we choose congruence classes a_p for all
-- primes 2 ≤ p ≤ n such that every integer in [1, n] satisfies at least
-- two of the congruences m ≡ a_p (mod p)?
--
-- This asks whether primes up to n provide enough "covering power" to
-- doubly cover [1, n] with chosen residue classes.
--
-- Generalizes to r-fold covering for any fixed r.
--
-- Status: OPEN
-- Reference: https://erdosproblems.com/689
-- Source: [Er79d]
-- Related: #687, #688

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

-- ## Definitions

/-- The set of primes up to n. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/-- An integer m is covered by prime p with residue class a if m ≡ a (mod p). -/
def IsCoveredBy (m p a : ℕ) : Prop :=
  m % p = a % p

/-- The covering count: how many primes p ≤ n cover m with the
    chosen congruence classes a. -/
noncomputable def coveringCount (n m : ℕ) (a : ℕ → ℕ) : ℕ :=
  ((primesUpTo n).filter (fun p => IsCoveredBy m p (a p))).card

/-- A congruence choice r-fold covers [1, n] if every m ∈ [1, n]
    is covered by at least r primes. -/
def IsRFoldCover (n r : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → r ≤ coveringCount n m a

-- ## Structural Properties

/-- Every m is covered by at least 0 primes (trivial). -/
theorem coveringCount_nonneg (n m : ℕ) (a : ℕ → ℕ) :
    0 ≤ coveringCount n m a :=
  Nat.zero_le _

/-- 0-fold covering is trivially achievable for any assignment. -/
theorem isRFoldCover_zero (n : ℕ) (a : ℕ → ℕ) :
    IsRFoldCover n 0 a := by
  intro m _ _
  exact Nat.zero_le _

/-- If r ≤ s and we have s-fold coverage, we have r-fold coverage. -/
theorem isRFoldCover_le {n r s : ℕ} {a : ℕ → ℕ}
    (hrs : r ≤ s) (h : IsRFoldCover n s a) : IsRFoldCover n r a := by
  intro m hm1 hmn
  exact le_trans hrs (h m hm1 hmn)

/-- Covering count is bounded by the number of primes up to n. -/
theorem coveringCount_le_card_primes (n m : ℕ) (a : ℕ → ℕ) :
    coveringCount n m a ≤ (primesUpTo n).card := by
  unfold coveringCount
  exact Finset.card_filter_le _ _

/-- If n₁ ≤ n₂, then primesUpTo n₁ ⊆ primesUpTo n₂. -/
theorem primesUpTo_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    primesUpTo n₁ ⊆ primesUpTo n₂ := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- The covering count increases with n (more primes available). -/
theorem coveringCount_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) (m : ℕ) (a : ℕ → ℕ) :
    coveringCount n₁ m a ≤ coveringCount n₂ m a := by
  unfold coveringCount
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact primesUpTo_mono h

/-- If r-fold covering holds for n₁ primes and n₁ ≤ n₂, it holds for n₂ primes
    on the same interval [1, n₁]. -/
theorem isRFoldCover_primes_mono {n₁ n₂ r : ℕ} {a : ℕ → ℕ}
    (h : n₁ ≤ n₂) (hcov : IsRFoldCover n₁ r a) :
    ∀ m : ℕ, 1 ≤ m → m ≤ n₁ → r ≤ coveringCount n₂ m a := by
  intro m hm1 hmn1
  exact le_trans (hcov m hm1 hmn1) (coveringCount_mono h m a)

-- ## Small Cases

/-- primesUpTo 1 is empty (no primes ≤ 1). -/
theorem primesUpTo_one : primesUpTo 1 = ∅ := by
  simp only [primesUpTo, Finset.filter_eq_empty_iff, Finset.mem_range]
  intro n hn
  interval_cases n <;> simp [Nat.Prime]

/-- Covering count is 0 when no primes available. -/
theorem coveringCount_one (m : ℕ) (a : ℕ → ℕ) :
    coveringCount 1 m a = 0 := by
  unfold coveringCount
  rw [primesUpTo_one]
  simp

-- ## Main Conjecture (OPEN)

/-- Erdős Problem #689 (OPEN): For sufficiently large n, does there
    exist a choice of congruence classes that 2-fold covers [1, n]?
    This is the r=2 case of the r-fold generalization. -/
theorem erdos_689_double_cover :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ a : ℕ → ℕ, IsRFoldCover n 2 a :=
  erdos_689_r_fold 2 (by norm_num)

/-- r-fold generalization (OPEN): For any fixed r and sufficiently
    large n (depending on r), does an r-fold covering exist? -/
axiom erdos_689_r_fold (r : ℕ) (hr : r ≥ 1) :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ a : ℕ → ℕ, IsRFoldCover n r a

-- ## Connections to Other Problems

/-- The sum Σ_{p ≤ n, p prime} 1/p diverges as log log n by Mertens' theorem.
    This means the "expected" covering count for a random assignment grows,
    suggesting r-fold covering should be achievable for large n.

    Proved from Mathlib's `not_summable_one_div_on_primes`: since the prime
    reciprocal indicator is not summable and nonneg, its partial sums tend to ∞.
    These partial sums are bounded by the `primesUpTo n` sums. -/
theorem mertens_sum_divergence :
  ∀ C : ℝ, 0 < C →
    ∃ N : ℕ, ∀ n ≥ N,
      C < ((primesUpTo n).sum (fun p => (1 : ℝ) / p)) := by
  intro C _
  -- Step 1: Prime reciprocal indicator is not summable (from Mathlib)
  have hns := not_summable_one_div_on_primes
  -- Step 2: The indicator is nonneg
  have hnn : ∀ i, 0 ≤ ({p : ℕ | p.Prime}.indicator fun n : ℕ => (1 : ℝ) / ↑n) i :=
    fun i => Set.indicator_apply_nonneg (fun _ => by positivity)
  -- Step 3: Not summable + nonneg ↔ partial sums → ∞
  rw [not_summable_iff_tendsto_nat_atTop_of_nonneg hnn] at hns
  rw [Filter.tendsto_atTop_atTop] at hns
  -- Step 4: For C + 1, get N such that C + 1 ≤ partial sum for all n ≥ N
  obtain ⟨N, hN⟩ := hns (C + 1)
  use N
  intro n hn
  have h_bound := hN n hn
  -- Step 5: Convert indicator sum to sum over filtered finset
  have h_ind_eq : ∀ x, ({p : ℕ | p.Prime}.indicator fun n : ℕ => (1 : ℝ) / ↑n) x =
      if x.Prime then (1 : ℝ) / ↑x else 0 := fun x => by
    simp [Set.indicator_apply]
  simp_rw [h_ind_eq, ← Finset.sum_filter] at h_bound
  -- Step 6: (Finset.range n).filter Nat.Prime ⊆ primesUpTo n
  have h_sub : (Finset.range n).filter Nat.Prime ⊆ primesUpTo n := by
    intro p hp
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  -- Step 7: Subset + nonneg terms → sum over subset ≤ sum over superset
  have h_le := Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)
  -- Step 8: C < C + 1 ≤ filter_sum ≤ primesUpTo_sum
  linarith

/-- Connection to Jacobsthal function (Problem #687): For large n,
    1-fold covering of [1,n] by primes up to n exists.
    This is the r=1 case of the r-fold generalization. -/
theorem jacobsthal_connection :
  ∀ᶠ (n : ℕ) in Filter.atTop,
    ∃ a : ℕ → ℕ, IsRFoldCover n 1 a := by
  rw [Filter.eventually_atTop]
  exact erdos_689_r_fold 1 (by norm_num)

/-- Ben Green's variant: Problem 45 on Green's list asks the same question
    with r = 10 instead of r = 2. Derived from the r-fold generalization. -/
theorem green_variant_r10 :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ a : ℕ → ℕ, IsRFoldCover n 10 a :=
  erdos_689_r_fold 10 (by norm_num)
