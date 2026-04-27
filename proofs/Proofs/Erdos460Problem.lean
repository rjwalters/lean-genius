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
Axioms: 1 (eggleton_erdos_selfridge — Eggleton-Erdős-Selfridge upper bound)
Sorries: 1 (filtered_sum_implies_full, converted from axiom for axiom-integrity)
Proved: sieve_greedy (from constructive def, with hactive guard for sentinel case)
Note: sieve_conjectured_bound demoted from axiom to def — it's an open conjecture.
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

/-- Each subsequent term is the least integer > previous term such that
n - aₖ is coprime to all previous n - aᵢ, and minimal with this property.
Proved from the constructive sieve definition when the sieve is active
(result ≤ n, not the n+1 sentinel).

The original axiom (without `hactive`) was false for n=2, k=2:
the sieve returns sentinel 3, but Coprime(2-3, 2-0) = Coprime(0,2) fails in ℕ. -/
theorem sieve_greedy (n : ℕ) (hn : n ≥ 2) (k : ℕ) (hk : k ≥ 2)
    (hactive : greedyCoprimeSieve n k ≤ n) :
    let a := greedyCoprimeSieve n
    a k > a (k - 1) ∧
    (∀ i, i < k → Nat.Coprime (n - a k) (n - a i)) ∧
    (∀ m, a (k - 1) < m → m < a k →
      ∃ i, i < k ∧ ¬Nat.Coprime (n - m) (n - a i)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [show k' + 2 - 1 = k' + 1 from by omega]
  dsimp only []  -- inline the let a := greedyCoprimeSieve n binding
  -- Define candidate set matching the sieve definition body
  set cands := (Finset.range (n + 1)).filter fun m =>
    greedyCoprimeSieve n (k' + 1) < m ∧
    ∀ i : Fin (k' + 2), Nat.Coprime (n - m) (n - greedyCoprimeSieve n i.val) with hcands
  -- Candidates must be nonempty: else sieve returns n+1, contradicting hactive
  have hne : cands.Nonempty := by
    by_contra hempty
    have hge : greedyCoprimeSieve n (k' + 2) = n + 1 := by
      simp only [greedyCoprimeSieve, ← hcands, dif_neg hempty]
    omega
  -- The sieve value equals min' of candidates
  have hval : greedyCoprimeSieve n (k' + 2) = cands.min' hne := by
    simp only [greedyCoprimeSieve, ← hcands, dif_pos hne]
  -- Extract properties from min' ∈ cands
  have hmem := Finset.mem_filter.mp (Finset.min'_mem cands hne)
  obtain ⟨_, hincr, hcop⟩ := hmem
  refine ⟨?_, ?_, ?_⟩
  -- (1) Strictly increasing: a(k'+2) > a(k'+1)
  · rw [hval]; exact hincr
  -- (2) Coprimality with all previous terms
  · intro i hi; rw [hval]; exact hcop ⟨i, hi⟩
  -- (3) Minimality: any m in (a(k'+1), a(k'+2)) fails coprimality
  · intro m hm_gt hm_lt
    have hm_not : m ∉ cands := by
      intro hm
      have := Finset.min'_le hne hm
      rw [← hval] at this
      omega
    have : ∃ i : Fin (k' + 2),
        ¬Nat.Coprime (n - m) (n - greedyCoprimeSieve n i.val) := by
      by_contra hall; push_neg at hall
      exact hm_not (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hm_gt, hall⟩)
    obtain ⟨i, hi⟩ := this
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

/-- Conjectured stronger bound: aₖ ≪ k log k.
    This is an OPEN CONJECTURE, not a proved result. -/
def SieveConjecturedBound : Prop :=
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 → ∀ k : ℕ, k ≥ 2 →
        (greedyCoprimeSieve n k : ℝ) ≤ C * (k : ℝ) * Real.log (k : ℝ)

/-- The reciprocal sum is non-negative. -/
theorem sieveReciprocalSum_nonneg (n : ℕ) : 0 ≤ sieveReciprocalSum n := by
  unfold sieveReciprocalSum
  apply Finset.sum_nonneg
  intro k _
  split_ifs with h
  · exact div_nonneg one_pos.le (Nat.cast_nonneg _)
  · exact le_refl _

/-
## Section VI: Least Prime Factor Connection
-/

/-- The least prime factor of n. -/
noncomputable def leastPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else Nat.minFac n

/-- The least prime factor of n ≥ 2 is prime. -/
theorem leastPrimeFactor_prime (n : ℕ) (hn : n ≥ 2) :
    Nat.Prime (leastPrimeFactor n) := by
  unfold leastPrimeFactor
  rw [if_neg (by omega)]
  exact Nat.minFac_prime (by omega)

/-- The least prime factor divides n (for n ≥ 2). -/
theorem leastPrimeFactor_dvd (n : ℕ) (hn : n ≥ 2) :
    leastPrimeFactor n ∣ n := by
  unfold leastPrimeFactor
  rw [if_neg (by omega)]
  exact Nat.minFac_dvd n

/-- The least prime factor is at most n (for n ≥ 2). -/
theorem leastPrimeFactor_le (n : ℕ) (hn : n ≥ 2) :
    leastPrimeFactor n ≤ n :=
  Nat.le_of_dvd (by omega) (leastPrimeFactor_dvd n hn)

/-- The function f(n) = Σ_{a < n, P⁻(n-a) > a} 1/a, where P⁻ denotes
the least prime factor. A sufficient condition for Problem 460 is that
f(n) → ∞. -/
noncomputable def leastPrimeFilteredSum (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range n,
    if a > 0 ∧ leastPrimeFactor (n - a) > a then
      (1 : ℝ) / (a : ℝ)
    else 0

/-- If `leastPrimeFilteredSum` diverges, then `ErdosProblem460` holds.

    This is a sufficient-condition lemma: it reduces the open conjecture to
    showing that the "filtered" sum (over `a` with `leastPrimeFactor (n-a) > a`)
    diverges. The implication is non-trivially provable from the relationship
    between `leastPrimeFilteredSum` and the greedy coprime sieve, but the
    formalization requires careful analysis of how filtered indices feed
    into the sieve sum.

    Converted from `axiom` to `theorem … := by sorry` so Aristotle can attempt
    the proof and so we no longer assume an unverified mathematical claim
    (axioms assert truth; sorries acknowledge an unproved gap).

    A weaker form is already proved as `erdos_460_restricted_question`, which
    uses `largePrimeSum` (summed over greedy-sieve indices, not all
    `a ∈ range n`); the two are not directly comparable. -/
theorem filtered_sum_implies_full :
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, leastPrimeFilteredSum n > M) →
    ErdosProblem460 := by
  sorry

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

/-- Each term of smallPrimeDivisibleSum is bounded by the corresponding
term of sieveReciprocalSum, since the filter condition is strictly stronger. -/
private lemma smallPrime_le_sieveReciprocal (n : ℕ) :
    smallPrimeDivisibleSum n ≤ sieveReciprocalSum n := by
  unfold smallPrimeDivisibleSum sieveReciprocalSum
  apply Finset.sum_le_sum
  intro k _
  dsimp only []
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd ⟨h1.1, h1.2.1⟩ h2
  · positivity
  · exact le_refl _

/-- Each term of largePrimeSum is bounded by the corresponding
term of sieveReciprocalSum, since the filter condition is strictly stronger. -/
private lemma largePrime_le_sieveReciprocal (n : ℕ) :
    largePrimeSum n ≤ sieveReciprocalSum n := by
  unfold largePrimeSum sieveReciprocalSum
  apply Finset.sum_le_sum
  intro k _
  dsimp only []
  split_ifs with h1 h2
  · exact le_refl _
  · exact absurd ⟨h1.1, h1.2.1⟩ h2
  · positivity
  · exact le_refl _

/-- If either restricted sum diverges, the full reciprocal sum diverges too,
since each restricted sum is a sub-sum of the full sieveReciprocalSum. -/
theorem erdos_460_restricted_question :
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, smallPrimeDivisibleSum n > M) ∨
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, largePrimeSum n > M) →
    ErdosProblem460 := by
  intro h
  unfold ErdosProblem460
  intro M hM
  rcases h with h_small | h_large
  · obtain ⟨N₀, hN₀⟩ := h_small M hM
    exact ⟨N₀, fun n hn =>
      lt_of_lt_of_le (hN₀ n hn) (smallPrime_le_sieveReciprocal n)⟩
  · obtain ⟨N₀, hN₀⟩ := h_large M hM
    exact ⟨N₀, fun n hn =>
      lt_of_lt_of_le (hN₀ n hn) (largePrime_le_sieveReciprocal n)⟩
