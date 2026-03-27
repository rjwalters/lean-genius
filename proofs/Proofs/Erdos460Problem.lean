/-
# Erdős Problem #460: Greedy Coprime Sieve Reciprocals

Let a₀ = 0, a₁ = 1. Define aₖ as the least integer greater than aₖ₋₁
such that gcd(n - aₖ, n - aᵢ) = 1 for all 0 ≤ i < k.
Does Σ (1/aᵢ) → ∞ as n → ∞ (summing over 0 < aᵢ < n)?

## Status: OPEN

## References
- Erdős (1977), p.64
- Erdős–Graham (1980), p.91
- Eggleton–Erdős–Selfridge: aₖ < k^{2+o(1)}

Proved: sieve_initial (a₀ = 0, a₁ = 1) — follows from the constructive definition.
The sieve is now implemented as a proper well-founded recursive function
(was previously a dummy fun _ => 0 with all behavior axiomatized).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
## Section I: The Greedy Coprime Sieve Sequence
-/

/-- The greedy coprime sieve sequence for a given n.
Starting with a₀ = 0, a₁ = 1, each aₖ is the least integer > aₖ₋₁
such that (n - aₖ) is coprime to (n - aᵢ) for all i < k.
When no valid candidate exists in [0, n], returns n + 1 (sentinel). -/
noncomputable def greedyCoprimeSieve (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 =>
    let a : Fin (k + 2) → ℕ := fun i => greedyCoprimeSieve n i.val
    let last := greedyCoprimeSieve n (k + 1)
    let candidates := (Finset.range (n + 1)).filter fun m =>
      last < m ∧ ∀ i : Fin (k + 2), Nat.Coprime (n - m) (n - a i)
    if h : candidates.Nonempty then candidates.min' h else n + 1
termination_by k => k
decreasing_by all_goals omega

/-- The defining property: a₀ = 0 and a₁ = 1. -/
theorem sieve_initial (n : ℕ) (hn : n ≥ 2) :
    greedyCoprimeSieve n 0 = 0 ∧ greedyCoprimeSieve n 1 = 1 := by
  constructor <;> simp [greedyCoprimeSieve]

/-- Unfolding lemma for greedyCoprimeSieve at k + 2. -/
private theorem greedyCoprimeSieve_succ_succ (n k : ℕ) :
    greedyCoprimeSieve n (k + 2) =
      let a : Fin (k + 2) → ℕ := fun i => greedyCoprimeSieve n i.val
      let last := greedyCoprimeSieve n (k + 1)
      let candidates := (Finset.range (n + 1)).filter fun m =>
        last < m ∧ ∀ i : Fin (k + 2), Nat.Coprime (n - m) (n - a i)
      if h : candidates.Nonempty then candidates.min' h else n + 1 := by
  simp [greedyCoprimeSieve]

/-- Each subsequent term is the least integer > previous term such that
n - aₖ is coprime to all previous n - aᵢ. PROVED from the constructive
definition: the filter gives coprimality, min' gives minimality, and
hvalid rules out the sentinel.

NOTE: The precondition `hvalid : greedyCoprimeSieve n k ≤ n` ensures
the sieve has not terminated (sentinel is n+1). Without it, the theorem
is false: e.g., n=2, k=2 gives sentinel 3. -/
theorem sieve_greedy (n : ℕ) (_hn : n ≥ 2) (k : ℕ) (hk : k ≥ 2)
    (hvalid : greedyCoprimeSieve n k ≤ n) :
    let a := greedyCoprimeSieve n
    a k > a (k - 1) ∧
    (∀ i, i < k → Nat.Coprime (n - a k) (n - a i)) ∧
    (∀ m, a (k - 1) < m → m < a k →
      ∃ i, i < k ∧ ¬Nat.Coprime (n - m) (n - a i)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [show k' + 2 - 1 = k' + 1 from by omega]
  set a := greedyCoprimeSieve n with ha_def
  set last := a (k' + 1)
  set prev : Fin (k' + 2) → ℕ := fun i => a i.val
  set candidates := (Finset.range (n + 1)).filter fun m =>
    last < m ∧ ∀ i : Fin (k' + 2), Nat.Coprime (n - m) (n - prev i)
  -- Since a(k'+2) ≤ n by hvalid, the sentinel case (n+1) is impossible,
  -- so candidates must have been nonempty
  have hne : candidates.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have heq := greedyCoprimeSieve_succ_succ n k'
    simp only [ha_def] at hvalid
    rw [heq] at hvalid
    simp only [hemp, dite_false] at hvalid
    omega
  -- a(k'+2) = candidates.min' hne
  have hval : a (k' + 2) = candidates.min' hne := by
    have heq := greedyCoprimeSieve_succ_succ n k'
    simp only [ha_def, heq, dif_pos hne]
  -- min' is in candidates, so it satisfies the filter
  have hmin_mem := Finset.min'_mem candidates hne
  simp only [Finset.mem_filter, Finset.mem_range] at hmin_mem
  obtain ⟨_, hlast_lt, hcoprime⟩ := hmin_mem
  refine ⟨?_, ?_, ?_⟩
  · -- a(k'+2) > a(k'+1)
    rw [hval]; exact hlast_lt
  · -- Coprimality with all previous terms
    intro i hi
    rw [hval]; exact hcoprime ⟨i, hi⟩
  · -- Minimality: anything between last and a(k'+2) fails coprimality
    intro m hlast_m hm_val
    rw [hval] at hm_val
    have hm_not_mem : m ∉ candidates :=
      fun hm => Nat.not_lt.mpr (Finset.min'_le candidates m hm) hm_val
    simp only [Finset.mem_filter, Finset.mem_range, not_and] at hm_not_mem
    have hm_range : m < n + 1 := by
      have := Finset.min'_le candidates (candidates.min' hne) (Finset.min'_mem _ _)
      omega
    have hfail := hm_not_mem hm_range
    push_neg at hfail
    obtain ⟨i, hi⟩ := hfail hlast_m
    exact ⟨i.val, i.isLt, hi⟩

/-
## Section II: The Sequence Terminates Before n
-/

/-- The number of terms in the sieve sequence that are less than n. -/
noncomputable def sieveCount (n : ℕ) : ℕ :=
  Finset.card ((Finset.range n).filter (fun a =>
    ∃ k, greedyCoprimeSieve n k = a ∧ a < n))

/-
## Section III: The Reciprocal Sum
-/

/-- The sum of reciprocals of the sieve sequence terms: Σ 1/aᵢ for 0 < aᵢ < n. -/
noncomputable def sieveReciprocalSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (sieveCount n),
    if greedyCoprimeSieve n k > 0 ∧ greedyCoprimeSieve n k < n then
      (1 : ℝ) / (greedyCoprimeSieve n k : ℝ)
    else 0

/-
## Section IV: The Conjecture
-/

/-- **Erdős Problem #460**: Does the sum of reciprocals of the greedy
coprime sieve sequence tend to infinity?

Formally: for every M > 0, there exists N₀ such that for all n ≥ N₀,
the reciprocal sum Σ (1/aᵢ) for 0 < aᵢ < n exceeds M. -/
def ErdosProblem460 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      sieveReciprocalSum n > M

/-
## Section V: Known Bounds
-/

/-- Eggleton, Erdős, and Selfridge showed aₖ < k^{2+o(1)} for large k.
This means the sequence grows at most quadratically. -/
axiom eggleton_erdos_selfridge (n : ℕ) (hn : n ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        (greedyCoprimeSieve n k : ℝ) < (k : ℝ) ^ ((2 : ℝ) + ε)

/-- Conjectured stronger bound: aₖ ≪ k log k. -/
axiom sieve_conjectured_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 → ∀ k : ℕ, k ≥ 2 →
        (greedyCoprimeSieve n k : ℝ) ≤ C * (k : ℝ) * Real.log (k : ℝ)

/-
## Section VI: Least Prime Factor Connection
-/

/-- The least prime factor of n. -/
noncomputable def leastPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else Nat.minFac n

/-- The function f(n) = Σ_{a < n, P⁻(n-a) > a} 1/a, where P⁻ denotes
the least prime factor. A sufficient condition for Problem 460 is that
f(n) → ∞. -/
noncomputable def leastPrimeFilteredSum (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range n,
    if a > 0 ∧ leastPrimeFactor (n - a) > a then
      (1 : ℝ) / (a : ℝ)
    else 0

/-- If leastPrimeFilteredSum diverges, then the full reciprocal sum diverges too. -/
axiom filtered_sum_implies_full :
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, leastPrimeFilteredSum n > M) →
    ErdosProblem460

/-
## Section VII: Restricted Sums
-/

/-- The sum restricted to indices where n - aⱼ is divisible by some prime ≤ aⱼ. -/
noncomputable def smallPrimeDivisibleSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (sieveCount n),
    let a := greedyCoprimeSieve n k
    if a > 0 ∧ a < n ∧
       ∃ p : ℕ, p.Prime ∧ p ≤ a ∧ p ∣ (n - a) then
      (1 : ℝ) / (a : ℝ)
    else 0

/-- The complementary sum: indices where all prime factors of n - aⱼ exceed aⱼ. -/
noncomputable def largePrimeSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (sieveCount n),
    let a := greedyCoprimeSieve n k
    if a > 0 ∧ a < n ∧ leastPrimeFactor (n - a) > a then
      (1 : ℝ) / (a : ℝ)
    else 0

/-
## Section VIII: Structural Theorems
-/

/-- The smallPrimeDivisibleSum is bounded by sieveReciprocalSum: the small-prime condition
    (a > 0 ∧ a < n ∧ ∃ p prime, p ≤ a ∧ p ∣ (n-a)) implies the full condition (a > 0 ∧ a < n),
    so each term of the restricted sum is ≤ the corresponding term of the full sum. -/
private lemma smallPrimeDivisibleSum_le (n : ℕ) :
    smallPrimeDivisibleSum n ≤ sieveReciprocalSum n := by
  unfold smallPrimeDivisibleSum sieveReciprocalSum
  apply Finset.sum_le_sum
  intro k _
  dsimp only
  split_ifs with h₁ h₂
  · exact le_refl _
  · exact absurd ⟨h₁.1, h₁.2.1⟩ h₂
  · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · exact le_refl _

/-- The largePrimeSum is bounded by sieveReciprocalSum: the large-prime condition
    (a > 0 ∧ a < n ∧ leastPrimeFactor(n-a) > a) implies the full condition (a > 0 ∧ a < n),
    so each term of the restricted sum is ≤ the corresponding term of the full sum. -/
private lemma largePrimeSum_le (n : ℕ) :
    largePrimeSum n ≤ sieveReciprocalSum n := by
  unfold largePrimeSum sieveReciprocalSum
  apply Finset.sum_le_sum
  intro k _
  dsimp only
  split_ifs with h₁ h₂
  · exact le_refl _
  · exact absurd ⟨h₁.1, h₁.2.1⟩ h₂
  · exact div_nonneg zero_le_one (Nat.cast_nonneg _)
  · exact le_refl _

/-- Erdős also asked whether the restricted sums individually diverge.
    If either restricted sum diverges, the full sum diverges too,
    since each restricted sum is bounded by the full sum (subset of non-negative terms). -/
theorem erdos_460_restricted_question :
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, smallPrimeDivisibleSum n > M) ∨
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, largePrimeSum n > M) →
    ErdosProblem460 := by
  intro h M hM
  rcases h with hsmall | hlarge
  · obtain ⟨N₀, hN₀⟩ := hsmall M hM
    exact ⟨N₀, fun n hn => lt_of_lt_of_le (hN₀ n hn) (smallPrimeDivisibleSum_le n)⟩
  · obtain ⟨N₀, hN₀⟩ := hlarge M hM
    exact ⟨N₀, fun n hn => lt_of_lt_of_le (hN₀ n hn) (largePrimeSum_le n)⟩
