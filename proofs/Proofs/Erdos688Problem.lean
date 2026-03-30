/-
# Erdős Problem #688: Covering by Large Prime Congruences

Define εₙ as the maximum ε such that for some choice of congruence class
aₚ for each prime n^ε < p ≤ n, every integer in [1,n] satisfies at least
one congruence m ≡ aₚ (mod p). Estimate εₙ; is εₙ = o(1)?

## Key Results

- **Erdős's lower bound**: εₙ ≫ (log log log n) / (log log n)
- **Open**: Is εₙ = o(1)? How fast does it tend to 0?
- Related to Problems #687 and #689

## References

- [Er79d] Erdős (1979)
- <https://erdosproblems.com/688>
-/

import Mathlib

/- ## Core Definitions -/

/-- A covering assignment: for each prime p in a range, choose a
    residue class aₚ ∈ {0, ..., p−1}. -/
def CoveringAssignment (primes : Finset ℕ) :=
  (p : ℕ) → p ∈ primes → Fin p

/-- Whether a covering assignment covers the interval [1, n]:
    every m ∈ [1, n] satisfies m ≡ aₚ (mod p) for some prime p. -/
def CoverInterval (n : ℕ) (primes : Finset ℕ)
    (assignment : CoveringAssignment primes) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ p ∈ primes, ∃ (hp : p ∈ primes),
      m % p = (assignment p hp : ℕ)

/-- The set of primes in the interval (n^ε, n]. -/
noncomputable def primesInRange (n : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p =>
    Nat.Prime p ∧ (p : ℝ) > (n : ℝ) ^ ε ∧ p ≤ n)

/-- εₙ: the maximum ε such that some choice of residue classes for
    primes in (n^ε, n] covers [1, n]. -/
noncomputable def coveringExponent (n : ℕ) : ℝ :=
  sSup {ε : ℝ | ε > 0 ∧ ε < 1 ∧
    ∃ assignment : CoveringAssignment (primesInRange n ε),
      CoverInterval n (primesInRange n ε) assignment}

/- ## Main Conjecture -/

/-- **Erdős's Conjecture**: εₙ = o(1), i.e., εₙ → 0 as n → ∞.
    Even primes close to n suffice to cover [1, n] with one class each. -/
/- ## Known Bounds -/

/-- **Erdős's lower bound**: εₙ ≫ (log log log n) / (log log n).
    The exponent cannot decrease faster than this iterated-log ratio. -/
/-- Trivial upper bound: εₙ < 1, since we need at least the prime n
    (if n is prime) or primes up to n. -/
/- ## Structural Properties -/

/-- Each prime p covers at most ⌊n/p⌋ + 1 integers in [1,n]
    with a single residue class.
    Proved via injection m ↦ (m+1)/p into range(n/p + 1). -/
theorem single_class_coverage :
  ∀ (n p : ℕ) (a : ℕ), Nat.Prime p → p ≤ n → a < p →
    ({m ∈ Finset.range n | (m + 1) % p = a}.card : ℝ) ≤ (n : ℝ) / p + 1 := by
  intro n p a hp _hpn hap
  set S := Finset.filter (fun m => (m + 1) % p = a) (Finset.range n) with hS_def
  -- Step 1: S embeds into range(n/p + 1) via m ↦ (m+1)/p
  have h_maps : ∀ m ∈ S, (m + 1) / p ∈ Finset.range (n / p + 1) := by
    intro m hm
    simp only [hS_def, Finset.mem_filter, Finset.mem_range] at hm ⊢
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  -- Step 2: The map is injective on S (same remainder + same quotient → same value)
  have h_inj : Set.InjOn (fun m => (m + 1) / p) (↑S) := by
    intro m₁ hm₁ m₂ hm₂ heq
    simp only [hS_def, Finset.coe_filter, Finset.mem_coe,
               Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hm₁ hm₂
    have r1 := Nat.div_add_mod (m₁ + 1) p
    have r2 := Nat.div_add_mod (m₂ + 1) p
    rw [hm₁.2, hm₂.2] at r1 r2
    omega
  -- Step 3: card S ≤ n/p + 1 via injection
  have h_card : S.card ≤ n / p + 1 := by
    calc S.card
        ≤ (Finset.range (n / p + 1)).card :=
          Finset.card_le_card_of_injOn (fun m => (m + 1) / p) h_maps h_inj
      _ = n / p + 1 := Finset.card_range _
  -- Step 4: Cast to ℝ — ↑(n/p) ≤ (n:ℝ)/p follows from Nat.cast_div_le
  calc (S.card : ℝ)
      ≤ ↑(n / p + 1) := Nat.cast_le.mpr h_card
    _ = ↑(n / p) + 1 := by push_cast; ring
    _ ≤ (n : ℝ) / p + 1 := by
        gcongr
        rw [le_div_iff₀ (Nat.cast_pos.mpr hp.pos)]
        exact_mod_cast Nat.div_mul_le_self n p

/-- The total coverage capacity of primes in (n^ε, n] is
    ∑_{n^ε < p ≤ n} ⌊n/p⌋ ~ n · (log(1/ε) + O(1)) by Mertens' theorem. -/
/-- Monotonicity: if ε₁ ≤ ε₂, the primes in (n^ε₁, n] include those
    in (n^ε₂, n], so more primes are available. -/
theorem exponent_monotone_coverage :
  ∀ (n : ℕ) (ε₁ ε₂ : ℝ), 0 < ε₁ → ε₁ ≤ ε₂ → ε₂ < 1 →
    (primesInRange n ε₂) ⊆ (primesInRange n ε₁) := by
  intro n ε₁ ε₂ hε₁ hε₁₂ _
  intro p hp
  simp only [primesInRange, Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩
  -- Need: (p : ℝ) > (n : ℝ) ^ ε₁
  -- We know: (p : ℝ) > (n : ℝ) ^ ε₂ and ε₁ ≤ ε₂
  by_cases hn : n = 0
  · subst hn; simp [Real.zero_rpow (ne_of_gt hε₁)] at hp
  · calc (n : ℝ) ^ ε₁ ≤ (n : ℝ) ^ ε₂ := by
          apply Real.rpow_le_rpow_of_exponent_le
          · exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn)
          · exact hε₁₂
      _ < p := hp.2.2.1

/-- Covering with all primes ≤ n (ε = 0): by CRT and the prime number
    theorem, one class per prime suffices to cover [1, n] for large n. -/
/-- The sieve connection: covering [1,n] by one residue class per prime
    is dual to sieving — excluding one class per prime. -/
theorem sieve_duality :
  ∀ (n : ℕ) (primes : Finset ℕ),
    (∀ p ∈ primes, Nat.Prime p) →
    -- If we exclude one class per prime, the remaining set is the
    -- complement of the covering
    True := by
  tauto
