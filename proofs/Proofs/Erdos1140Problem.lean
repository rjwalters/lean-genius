/-
Erdős Problem #1140: Primes of the Form n - 2x²

Source: https://erdosproblems.com/1140
Status: DISPROVED (Epure-Gica, 2010)

Statement:
Do there exist infinitely many n such that n - 2x² is prime
for all x with 2x² < n?

Answer: NO — Only finitely many n exist: {2, 5, 7, 13, 31, 61, 181, 199}
(with at most one additional exception).

History:
- Erdős: Posed the question
- Epure-Gica (2010): Proved only finitely many n exist
  - For n ≡ 1 (mod 4): only 5, 13, 61, 181
  - For n ≡ 3 (mod 4): only 7, 31, 199, and at most one exception
- Mollin-Williams (1989): Key supporting result for n ≡ 3 case

Tags: number-theory, primes, quadratic-forms, disproved
-/

import Mathlib

namespace Erdos1140

-- ## Part I: Basic Definitions

/-- The property that n - 2x² is prime for all valid x. -/
def AllShiftsArePrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/-- The known values satisfying the property. -/
def KnownValues : Finset ℕ := {2, 5, 7, 13, 31, 61, 181, 199}

-- ## Part II: Structural Properties

/-- The x = 0 case: if AllShiftsArePrime n and n > 0, then n is prime. -/
theorem allShiftsArePrime_implies_prime {n : ℕ} (h : AllShiftsArePrime n) (hn : n > 0) :
    Nat.Prime n := by
  have := h 0 (by omega)
  simpa using this

/-- For even n > 2, n is not prime, so AllShiftsArePrime fails at x = 0. -/
theorem even_case (n : ℕ) (hn : n > 2) (heven : 2 ∣ n) :
    ¬AllShiftsArePrime n := by
  intro h
  have h0 : Nat.Prime n := allShiftsArePrime_implies_prime h (by omega)
  rcases h0.eq_one_or_self_of_dvd 2 heven with h1 | h1 <;> omega

/-- AllShiftsArePrime n and n > 2 implies n is odd. -/
theorem allShiftsArePrime_odd {n : ℕ} (h : AllShiftsArePrime n) (hn : n > 2) :
    ¬(2 ∣ n) :=
  fun heven => even_case n hn heven h

-- ## Part III: Verified Small Cases (ALL Known Values)

/-- n = 2: x = 0, giving 2 (prime). -/
theorem n_eq_2 : AllShiftsArePrime 2 := by
  intro x hx; have : x ≤ 0 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> decide

/-- n = 5: x ∈ {0, 1}, giving 5, 3 (both prime). -/
theorem n_eq_5 : AllShiftsArePrime 5 := by
  intro x hx; have : x ≤ 1 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> decide

/-- n = 7: x ∈ {0, 1}, giving 7, 5 (both prime). -/
theorem n_eq_7 : AllShiftsArePrime 7 := by
  intro x hx; have : x ≤ 1 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> decide

/-- n = 13: x ∈ {0, 1, 2}, giving 13, 11, 5 (all prime). -/
theorem n_eq_13 : AllShiftsArePrime 13 := by
  intro x hx; have : x ≤ 2 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> decide

/-- n = 31: x ∈ {0, 1, 2, 3}, giving 31, 29, 23, 13 (all prime). -/
theorem n_eq_31 : AllShiftsArePrime 31 := by
  intro x hx; have : x ≤ 3 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> decide

/-- n = 61: x ∈ {0, ..., 5}, giving 61, 59, 53, 43, 29, 11 (all prime). -/
theorem n_eq_61 : AllShiftsArePrime 61 := by
  intro x hx; have : x ≤ 5 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> decide

/-- n = 181: x ∈ {0, ..., 9}, giving 181, 179, 173, 163, 149, 131, 109, 83, 53, 19
    (all prime). -/
theorem n_eq_181 : AllShiftsArePrime 181 := by
  intro x hx; have : x ≤ 9 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> norm_num

/-- n = 199: x ∈ {0, ..., 9}, giving 199, 197, 191, 181, 167, 149, 127, 101, 71, 37
    (all prime). -/
theorem n_eq_199 : AllShiftsArePrime 199 := by
  intro x hx; have : x ≤ 9 := by nlinarith [sq_nonneg x]
  interval_cases x <;> simp_all <;> norm_num

-- ## Part IV: Verified Failure Cases

/-- n = 1 fails: 1 is not prime. -/
theorem n_eq_1_fails : ¬AllShiftsArePrime 1 := by
  intro h; have := h 0 (by omega); norm_num at this

/-- n = 3 fails: 3 - 2·1² = 1 is not prime. -/
theorem n_eq_3_fails : ¬AllShiftsArePrime 3 := by
  intro h; have := h 1 (by omega); norm_num at this

/-- n = 4 fails: 4 is not prime. -/
theorem n_eq_4_fails : ¬AllShiftsArePrime 4 := by
  intro h; have := h 0 (by omega); norm_num at this

/-- n = 9 fails: 9 is not prime. -/
theorem n_eq_9_fails : ¬AllShiftsArePrime 9 := by
  intro h; have := h 0 (by omega); norm_num at this

/-- n = 15 fails: 15 is not prime. -/
theorem n_eq_15_fails : ¬AllShiftsArePrime 15 := by
  intro h; have := h 0 (by omega); norm_num at this

-- ## Part V: Epure-Gica Theorem

/-- **Epure-Gica (2010), case n ≡ 1 (mod 4):**
    The only values n ≡ 1 (mod 4) with AllShiftsArePrime are 5, 13, 61, 181. -/
axiom epure_gica_mod_1 (n : ℕ) :
    n % 4 = 1 → AllShiftsArePrime n → n ∈ ({5, 13, 61, 181} : Finset ℕ)

/-- **Epure-Gica (2010), case n ≡ 3 (mod 4):**
    The set of n ≡ 3 (mod 4) with AllShiftsArePrime is finite,
    consisting of {7, 31, 199} and at most one additional exception.
    (Relies on class number bounds for Q(√(-2n)) via Mollin-Williams 1989
    and Siegel's ineffective lower bound on h(-D).) -/
axiom epure_gica_mod_3 :
    ∃ T : Finset ℕ, ∀ n, n % 4 = 3 → AllShiftsArePrime n → n ∈ T

-- ## Part VI: Main Result (derived from Parts II + V)

/-- **Erdős Problem #1140: DISPROVED**

    There are only finitely many n such that n - 2x² is prime for all
    valid x. The known values are {2, 5, 7, 13, 31, 61, 181, 199}.

    Proof: For n > max(181, max(T)), where T is the finite set from
    epure_gica_mod_3: if AllShiftsArePrime n, then n > 2 so n is odd
    (Part II), hence n % 4 ∈ {1, 3}. The mod 1 case puts n in {5,13,61,181},
    contradicting n > 181. The mod 3 case puts n in T, contradicting
    n > max(T). -/
theorem erdos_1140_finite :
    ∃ B : ℕ, ∀ n > B, ¬AllShiftsArePrime n := by
  obtain ⟨T, hT⟩ := epure_gica_mod_3
  refine ⟨max 181 (T.sup id), fun n hn hAll => ?_⟩
  have h181 : 181 < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hTsup : T.sup id < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hodd : ¬(2 ∣ n) := allShiftsArePrime_odd hAll (by omega)
  have hmod : n % 4 = 1 ∨ n % 4 = 3 := by
    have : ¬(n % 2 = 0) := fun h => hodd ⟨n / 2, by omega⟩
    omega
  rcases hmod with h1 | h3
  · have hmem := epure_gica_mod_1 n h1 hAll
    simp at hmem; omega
  · have hmem := hT n h3 hAll
    have := Finset.le_sup (f := id) hmem
    simp at this; omega

/-- The answer to Erdős Problem #1140: NOT infinitely many. -/
theorem erdos_1140 : ¬(∀ N : ℕ, ∃ n > N, AllShiftsArePrime n) := by
  intro h
  obtain ⟨B, hB⟩ := erdos_1140_finite
  obtain ⟨n, hn, hn'⟩ := h B
  exact hB n (by omega) hn'

/-- All 8 known values are verified to satisfy the property. -/
theorem all_known_values_verified :
    ∀ n ∈ KnownValues, AllShiftsArePrime n := by
  intro n hn
  simp [KnownValues] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact n_eq_2
  · exact n_eq_5
  · exact n_eq_7
  · exact n_eq_13
  · exact n_eq_31
  · exact n_eq_61
  · exact n_eq_181
  · exact n_eq_199

/-
## Summary

**Problem Status: DISPROVED (Epure-Gica 2010)**

Erdős Problem #1140 asked whether infinitely many n exist such that
n - 2x² is prime for all x with 2x² < n.

**Answer: NO** — Only finitely many such n exist.

**Known values**: {2, 5, 7, 13, 31, 61, 181, 199} — all 8 verified in Lean.

**Proved Theorems (0 sorries)**:
- allShiftsArePrime_implies_prime: x=0 case gives Nat.Prime n
- even_case: Even n > 2 cannot satisfy the property
- allShiftsArePrime_odd: Solutions > 2 must be odd
- n_eq_2 through n_eq_199: All 8 known values verified
- n_eq_1_fails through n_eq_15_fails: 5 failure cases verified
- erdos_1140_finite: Finiteness (PROVED from mod_1 + mod_3 + parity)
- erdos_1140: The conjecture is FALSE (not infinitely many)
- all_known_values_verified: Unified theorem for all 8 known values

**Axioms (2)**:
- epure_gica_mod_1: n ≡ 1 (mod 4) → n ∈ {5, 13, 61, 181}
- epure_gica_mod_3: {n ≡ 3 (mod 4) | AllShiftsArePrime n} is finite

**Key improvements**:
1. Axiom elimination: 3 → 2 (erdos_1140_finite derived from classification)
2. Strengthened epure_gica_mod_3 to capture finiteness (was too weak)
3. All 8 known values verified, 5 failure cases, structural lemmas
4. Theorem count: 18 → 19 (erdos_1140_finite now proved)
5. Fixed Mathlib 4.26.0 compatibility (nlinarith bounds, norm_num)

References:
- Epure, R. & Gica, A. (2010). Number theory results.
- Mollin, R. & Williams, H. (1989). Supporting results.
-/

end Erdos1140
