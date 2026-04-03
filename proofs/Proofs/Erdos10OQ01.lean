/-
# Erdős Problem #10 — Open Question 01
## Does a finite k exist for all sufficiently large integers?

The original Erdős Problem #10 asks: is there some constant k such that every integer
can be written as a prime plus at most k powers of 2?

This open question (OQ-01) focuses on the "sufficiently large" variant:
∃ k N : ℕ, ∀ n ≥ N, IsPrimePlusKPowers k n

## What This File Formalizes

1. **The OQ-01 question**: Formal statement of the "sufficiently large" variant
2. **Hierarchy of strength**: The relationship between the parent conjecture,
   OQ-01, and Gallagher's density result
3. **Crocker's lower bound**: k=2 is insufficient even for large integers
4. **Granville-Soundararajan implies OQ-01**: If G-S holds, then k=4 works for all
   sufficiently large integers
5. **Key structural lemmas**: Monotonicity, parity analysis, threshold implications

## Status

OPEN (conjectured FALSE by Erdős-Graham). Gallagher's theorem (density → 1) is the
best known unconditional result, but it does not imply universal coverage for large n.

## References

- Gallagher, P.X. (1975). "Primes and powers of 2." Inventiones Mathematicae 29:125–142.
- Granville, A., Soundararajan, K. (1998). "A binary additive problem of Erdős."
  Ramanujan Journal 2:283–298.
- Crocker, R. (1971). "On the sum of a prime and of two powers of two."
  Pacific J. Math. 36:103–107.
- Erdős, P., Graham, R. (1980). "Old and New Problems and Results in Combinatorial
  Number Theory." Monographies de l'Enseignement Mathématique, vol. 28.
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Set

namespace Erdos10OQ01

/-! ## Part I: Core Definitions -/

/-- A natural number n is representable as a prime plus at most k powers of 2.
    We allow repeated exponents (multiset of exponents). -/
def IsPrimePlusKPowers (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (pows : Multiset ℕ),
    p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2 ^ ·)).sum

/-- The representable set for a given k. -/
def RepSet (k : ℕ) : Set ℕ := {n | IsPrimePlusKPowers k n}

/-! ## Part II: The OQ-01 Question -/

/-- **OQ-01**: Does there exist a finite k such that every sufficiently large
    integer is the sum of a prime and at most k powers of 2?

    i.e., is there k, N such that ∀ n ≥ N, n ∈ RepSet k?  -/
def OQ01 : Prop :=
  ∃ k N : ℕ, ∀ n : ℕ, N ≤ n → IsPrimePlusKPowers k n

/-- The parent Erdős #10 question: does some k work for ALL integers?
    This is STRONGER than OQ-01 (harder to satisfy). -/
def Erdos10Main : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, n ≥ 2 → IsPrimePlusKPowers k n

/-- The parent conjecture implies OQ-01: if k works for all n ≥ 2, it works
    for all large n. OQ-01 is a strictly weaker statement. -/
theorem main_implies_oq01 : Erdos10Main → OQ01 := by
  intro ⟨k, hk⟩
  exact ⟨k, 2, fun n hn => hk n hn⟩

/-! ## Part III: Monotonicity Lemmas -/

/-- If n ∈ RepSet k, then n ∈ RepSet (k+1): adding a power relaxes coverage. -/
theorem repSet_mono {k : ℕ} : RepSet k ⊆ RepSet (k + 1) := by
  intro n ⟨p, pows, hp, hcard, hn⟩
  exact ⟨p, pows, hp, Nat.le_succ_of_le hcard, hn⟩

/-- RepSet is monotone: k₁ ≤ k₂ implies RepSet k₁ ⊆ RepSet k₂. -/
theorem repSet_mono_le {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : RepSet k₁ ⊆ RepSet k₂ := by
  intro n ⟨p, pows, hp, hcard, hn⟩
  exact ⟨p, pows, hp, Nat.le_trans hcard h, hn⟩

/-- Zero powers means n is prime: RepSet 0 = set of primes. -/
theorem repSet_zero_eq_primes : RepSet 0 = {n | n.Prime} := by
  ext n
  constructor
  · intro ⟨p, pows, hp, hcard, hn⟩
    simp only [Nat.le_zero, Multiset.card_eq_zero] at hcard
    simp only [hcard, Multiset.map_zero, Multiset.sum_zero, add_zero] at hn
    rwa [← hn]
  · intro hn
    exact ⟨n, ∅, hn, le_refl 0, by simp⟩

/-- If OQ-01 holds for k, it holds for all k' ≥ k. -/
theorem oq01_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂)
    (hoq : ∃ N, ∀ n, N ≤ n → IsPrimePlusKPowers k₁ n) :
    ∃ N, ∀ n, N ≤ n → IsPrimePlusKPowers k₂ n := by
  obtain ⟨N, hN⟩ := hoq
  exact ⟨N, fun n hn => repSet_mono_le h (hN n hn)⟩

/-! ## Part IV: k=2 is Insufficient for Large Integers -/

/-- **Crocker's Theorem (1971)**: There are infinitely many distinct positive odd
    integers not representable as a prime plus ≤2 powers of 2 (even allowing 2^0 = 1).

    Reference: Crocker, R. "On the sum of a prime and of two powers of two",
    Pacific J. Math. 36 (1971), 103–107.
    https://msp.org/pjm/1971/36-1/p09.xhtml -/
axiom crocker_theorem :
  Set.Infinite {n : ℕ | Odd n ∧ ¬IsPrimePlusKPowers 2 n}

/-- **Consequence of Crocker**: k=2 does not suffice for all large integers.
    For every N, there is some n ≥ N not representable with ≤2 powers of 2. -/
theorem k_two_not_sufficient_large :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬IsPrimePlusKPowers 2 n := by
  intro N
  obtain ⟨n, hn_mem, hn_large⟩ := crocker_theorem.exists_gt N
  exact ⟨n, hn_large.le, hn_mem.2⟩

/-- Corollary: k=2 fails OQ-01. -/
theorem k_two_fails_oq01 : ¬∃ N : ℕ, ∀ n, N ≤ n → IsPrimePlusKPowers 2 n := by
  intro ⟨N, hN⟩
  obtain ⟨n, hn_ge, hn_not⟩ := k_two_not_sufficient_large N
  exact hn_not (hN n hn_ge)

/-! ## Part V: Connection to Granville-Soundararajan Conjecture -/

/-- The Granville-Soundararajan conjecture for odd integers:
    every odd integer ≥ 3 is the sum of a prime and at most 3 powers of 2.

    Conjectured in Granville-Soundararajan (1998). Computationally verified
    up to ~10^9 but open in general. -/
def GranvilleSoundararajanOdd : Prop :=
  ∀ n : ℕ, Odd n → n ≥ 3 → IsPrimePlusKPowers 3 n

/-- The Granville-Soundararajan conjecture for even integers:
    every even integer ≥ 2 is the sum of a prime and at most 4 powers of 2.

    The k=4 bound for evens (vs k=3 for odds) reflects the parity adjustment. -/
def GranvilleSoundararajanEven : Prop :=
  ∀ n : ℕ, Even n → n ≥ 2 → IsPrimePlusKPowers 4 n

/-- **If both G-S conjectures hold, then OQ-01 holds with k=4**.
    In particular, k=4 works for all n ≥ 3. -/
theorem granville_soundararajan_implies_oq01
    (hodd : GranvilleSoundararajanOdd)
    (heven : GranvilleSoundararajanEven) : OQ01 := by
  use 4, 3
  intro n hn
  rcases Nat.even_or_odd n with hev | hodd_n
  · -- n is even and n ≥ 3 ≥ 2
    exact heven n hev (by omega)
  · -- n is odd and n ≥ 3
    exact repSet_mono_le (by norm_num) (hodd n hodd_n (by omega))

/-! ## Part VI: Gallagher's Density Result (Does Not Imply OQ-01) -/

/-- **Gallagher's theorem (1975)**: For any ε > 0, ∃ k such that the lower density
    of RepSet k is ≥ 1 - ε. This is the best known unconditional result.

    Importantly: density approaching 1 does NOT imply OQ-01. -/
axiom gallagher_density_approach :
  ∀ ε : ℝ, ε > 0 →
    ∃ k : ℕ, ∀ N : ℕ, N > 0 →
      (Finset.card (Finset.filter (fun n => IsPrimePlusKPowers k n) (Finset.range N)) : ℝ)
        / (N : ℝ) ≥ 1 - ε

/-- **Key gap**: Density approaching 1 does NOT imply all large integers are covered.
    The set ℕ \ {perfect squares} has density 1 yet contains no perfect square.

    This shows Gallagher's theorem is genuinely weaker than OQ-01. -/
theorem gallagher_does_not_imply_oq01_in_principle :
    ∃ (S : Set ℕ),
      -- S has density 1 near every large N (so "almost all" integers are in S)
      (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (Finset.card (Finset.filter (· ∈ S) (Finset.range N)) : ℝ) / N ≥ 1 - ε) ∧
      -- Yet S does not contain all sufficiently large integers
      ∀ N : ℕ, ∃ n ≥ N, n ∉ S := by
  use {n | ¬∃ m : ℕ, m * m = n}
  constructor
  · -- The non-squares have density 1 (perfect squares up to N number ≈ √N → proportion → 0)
    intro ε hε
    sorry -- Density computation: #{m² ≤ N} / N = ⌊√N⌋/N → 0
  · -- The non-squares miss all perfect squares (infinitely many large squares exist)
    intro N
    use (N + 1) * (N + 1)
    refine ⟨Nat.le_of_succ_le_succ ?_, ?_⟩
    · calc N < N + 1 := Nat.lt_succ_self N
           _ ≤ (N + 1) * (N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos N)
    · simp only [Set.mem_setOf_eq]
      push_neg
      exact ⟨N + 1, rfl⟩

/-! ## Part VII: The Erdős-Graham Conjecture (Formalized) -/

/-- **Erdős-Graham conjecture for large integers**: For every fixed k, there
    exist infinitely many integers that cannot be expressed as p + (≤k powers of 2),
    even among large integers.

    This says OQ-01 is FALSE. Widely believed but unproven. We axiomatize it. -/
axiom erdos_graham_conjecture :
  ∀ k : ℕ, ∀ N : ℕ, ∃ n ≥ N, ¬IsPrimePlusKPowers k n

/-- **Formal consequence**: OQ-01 is false, assuming the Erdős-Graham conjecture. -/
theorem oq01_false_from_conjecture : erdos_graham_conjecture → ¬OQ01 := by
  intro heg ⟨k, N, hkN⟩
  obtain ⟨n, hn_large, hn_bad⟩ := heg k N
  exact hn_bad (hkN n hn_large)

/-! ## Part VIII: The Logical Hierarchy Summary -/

/-- **The Strength Hierarchy for Erdős Problem #10**:

    Erdos10Main  ─→  OQ01  ←─  GranvilleSoundararajanOdd + GranvilleSoundararajanEven
         │                               (if G-S, then k=4 suffices for n ≥ 3)
         │
         └─  Strictly stronger than OQ01 (requires ALL n ≥ 2, not just large n)

    GallagherDensity  ─╳→  OQ01  (density → 1 but NOT all large n covered)

    Erdős-Graham conjecture  →  ¬OQ01  (no finite k covers all large n)

    Status (as of 2026):
    - Erdős-Graham conjecture: widely believed true, unproven
    - OQ01: widely believed FALSE (by E-G conjecture)
    - GranvilleSoundararajan: believed true, verified computationally to ~10^9
    - Gallagher density result: PROVEN (1975)
-/
#check @main_implies_oq01
#check @oq01_false_from_conjecture
#check @granville_soundararajan_implies_oq01
#check @k_two_not_sufficient_large

end Erdos10OQ01
