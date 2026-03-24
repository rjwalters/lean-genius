/-
# Erdős Problem 488: Divisibility Density in Multiples of Finite Sets

Let `A` be a finite set of positive integers and
`B = {n ≥ 1 : a | n for some a ∈ A}` (the set of multiples of
elements of `A`).

Is it true that for every `m > n ≥ max(A)`,
`|B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n`?

The constant 2 is optimal: `A = {a}`, `n = 2a-1`, `m = 2a`.

Originally posed in Erdős (1961). The 1961 version had `a ∤ n`
(likely a typo), corrected to `a | n` in 1966.

*Reference:* [erdosproblems.com/488](https://www.erdosproblems.com/488)
-/

import Mathlib

/- ## Multiples set -/

/-- `B(A)`: the set of positive integers divisible by some element
of `A`. -/
def multiplesSet (A : Finset ℕ) : Set ℕ :=
    { n : ℕ | 1 ≤ n ∧ ∃ a ∈ A, a ∣ n }

/- ## Counting function -/

/-- Count of elements of `B(A)` in `[1, N]`. -/
noncomputable def multiplesCount (A : Finset ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (fun n => ∃ a ∈ A, a ∣ n)).card

/-- The density ratio `|B ∩ [1,N]| / N`. -/
noncomputable def multiplesRatio (A : Finset ℕ) (N : ℕ) : ℚ :=
    (multiplesCount A N : ℚ) / (N : ℚ)

/- ## Main conjecture -/

/-- Erdős Problem 488: For every finite set `A` of integers ≥ 2, and
every `m > n ≥ max(A)`, we have
`|B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n`. -/
def ErdosProblem488 : Prop :=
    ∀ (A : Finset ℕ) (hA : A.Nonempty),
      (∀ a ∈ A, 2 ≤ a) →
        ∀ (n m : ℕ),
          A.max' hA ≤ n →
          n < m →
            multiplesRatio A m < 2 * multiplesRatio A n

/- ## Inclusion–exclusion for multiples -/

/-- For a singleton `A = {a}`, `|B ∩ [1,N]| = ⌊N/a⌋`.
Proved via a bijection between `Finset.range (N/a)` and the multiples of `a`
in `[1, N]`, sending `k ↦ (k+1)*a`. -/
theorem singleton_multiplesCount (a N : ℕ) (ha : 1 ≤ a) :
    multiplesCount ({a} : Finset ℕ) N = N / a := by
  unfold multiplesCount
  -- Simplify singleton existential to plain divisibility
  have hfilt : ((Finset.Icc 1 N).filter (fun n => ∃ a' ∈ ({a} : Finset ℕ), a' ∣ n)) =
               ((Finset.Icc 1 N).filter (fun n => a ∣ n)) := by
    apply Finset.filter_congr
    intro x _
    simp only [Finset.mem_singleton, exists_eq_left]
  rw [hfilt, ← Finset.card_range (N / a)]
  -- Bijection: range (N/a) → (Icc 1 N).filter (a ∣ ·) via k ↦ (k+1)*a
  symm
  apply Finset.card_bij (fun k _ => (k + 1) * a)
  · -- Forward: (k+1)*a ∈ filtered set
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_left a (k + 1)⟩
    · -- 1 ≤ (k + 1) * a
      exact le_trans ha (le_mul_of_one_le_left (Nat.zero_le a) (by omega))
    · -- (k + 1) * a ≤ N
      exact le_trans (Nat.mul_le_mul_right a (by omega : k + 1 ≤ N / a))
                     (Nat.div_mul_le_self N a)
  · -- Injectivity
    intro k₁ _ k₂ _ h
    have := mul_right_cancel₀ (show (a : ℕ) ≠ 0 by omega) h
    omega
  · -- Surjectivity: every multiple a*m in [1,N] has m-1 ∈ range (N/a)
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hdvd⟩ := hn
    obtain ⟨m, rfl⟩ := hdvd
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hn1
      · omega
    refine ⟨m - 1, Finset.mem_range.mpr ?_, ?_⟩
    · -- m - 1 < N / a
      have : m ≤ N / a := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < a)]
        rwa [mul_comm]
      omega
    · -- (m - 1 + 1) * a = a * m
      have : m - 1 + 1 = m := by omega
      rw [this, mul_comm]

/-- Monotonicity: `|B ∩ [1,M]| ≤ |B ∩ [1,N]|` when `M ≤ N`. -/
theorem multiplesCount_mono (A : Finset ℕ) (M N : ℕ) (h : M ≤ N) :
    multiplesCount A M ≤ multiplesCount A N := by
  unfold multiplesCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at *
  exact ⟨⟨hn.1.1, le_trans hn.1.2 h⟩, hn.2⟩

/-- Adding elements to `A` can only increase the multiples count. -/
theorem multiplesCount_subset (A B : Finset ℕ) (h : A ⊆ B) (N : ℕ) :
    multiplesCount A N ≤ multiplesCount B N := by
  unfold multiplesCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at *
  exact ⟨hn.1, let ⟨a, haA, hdvd⟩ := hn.2; ⟨a, h haA, hdvd⟩⟩

/- ## Optimality of constant 2 -/

/-- The constant 2 is optimal: for `A = {a}`, `n = 2a-1`, `m = 2a`,
the ratio approaches 2 as `a → ∞`.

For singleton `{a}`: `multiplesCount {a} (2a) = 2` and
`multiplesCount {a} (2a-1) = 1`, so the ratio is
`(2/(2a)) / (1/(2a-1)) = (2a-1)/a = 2 - 1/a → 2`. -/
theorem constant_2_optimal :
    ∀ (ε : ℚ), 0 < ε →
      ∃ a : ℕ, 2 ≤ a ∧
        let A := ({a} : Finset ℕ)
        let n := 2 * a - 1
        let m := 2 * a
        2 - ε < multiplesRatio A m / multiplesRatio A n := by
  intro ε hε
  -- Choose a > 1/ε with a ≥ 2
  obtain ⟨a₀, ha₀⟩ := exists_nat_gt (1 / ε)
  refine ⟨max a₀ 2, le_max_right _ _, ?_⟩
  set a := max a₀ 2
  have ha2 : 2 ≤ a := le_max_right _ _
  have ha_pos : (0 : ℚ) < ↑a := by exact_mod_cast (show 0 < a by omega)
  -- Compute multiplesCount values
  show 2 - ε < multiplesRatio ({a} : Finset ℕ) (2 * a) /
               multiplesRatio ({a} : Finset ℕ) (2 * a - 1)
  have ha1 : 1 ≤ a := by omega
  have ha0 : 0 < a := by omega
  simp only [multiplesRatio]
  rw [singleton_multiplesCount a (2 * a) ha1,
      singleton_multiplesCount a (2 * a - 1) ha1,
      show 2 * a / a = 2 from Nat.mul_div_cancel 2 ha0,
      show (2 * a - 1) / a = 1 from
        Nat.div_eq_of_lt_le (by omega) (by omega)]
  -- Goal: 2 - ε < ((2 : ℚ) / ↑(2 * a)) / ((1 : ℚ) / ↑(2 * a - 1))
  -- Suffices to show 2 - ε < (2*a-1)/a = 2 - 1/a
  suffices h : 2 - ε < (2 * (↑a : ℚ) - 1) / ↑a by
    have h2a_ne : (↑(2 * a) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2a1_ne : (↑(2 * a - 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have ha_ne : (↑a : ℚ) ≠ 0 := ne_of_gt ha_pos
    convert h using 1
    field_simp
    rw [Nat.cast_sub (show 1 ≤ 2 * a by omega), Nat.cast_mul, Nat.cast_ofNat]
    ring
  -- Prove: 2 - ε < (2*↑a - 1) / ↑a = 2 - 1/↑a
  have heq : (2 * (↑a : ℚ) - 1) / ↑a = 2 - 1 / ↑a := by field_simp
  rw [heq]
  -- Goal: 2 - ε < 2 - 1 / ↑a
  -- Key: 1/↑a < ε follows from 1/ε < a
  have h_inv : (1 : ℚ) / ↑a < ε := by
    have h : 1 / ε < ↑a := lt_of_lt_of_le ha₀ (Nat.cast_le.mpr (le_max_left _ _))
    have h1 : 1 < ↑a * ε := by rwa [div_lt_iff₀ hε] at h
    exact (div_lt_iff₀ ha_pos).mpr (by linarith [mul_comm (↑a : ℚ) ε])
  linarith

/- ## Davenport's density -/

/-- The asymptotic density of `B(A)` exists and can be computed by
inclusion–exclusion over the elements of `A`. -/
axiom multiplesSet_density_exists (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ ε : ℚ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          |multiplesRatio A N - δ| < ε
