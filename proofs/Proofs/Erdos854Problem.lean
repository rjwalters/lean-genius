/-
# Erdős Problem #854 — Gaps Between Coprime Residues of Primorials

Let nₖ = p₁ · p₂ · ⋯ · pₖ be the k-th primorial. Consider the sequence
1 = a₁ < a₂ < ⋯ < a_{φ(nₖ)} = nₖ − 1 of integers coprime to nₖ.

Erdős asked:
(1) Estimate the smallest even integer not expressible as a gap aᵢ₊₁ − aᵢ.
(2) Is it true that ≫ max_i(aᵢ₊₁ − aᵢ) many even integers occur as gaps?

Erdős initially conjectured all even integers up to the maximal gap appear,
but computations by Lacampagne and Selfridge cast doubt on this for nₖ = 30030.

Reference: https://erdosproblems.com/854
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.OrderIsoNat
import Mathlib.Tactic

/- ## Primorial and Coprime Residues -/

/-- The k-th prime number (1-indexed: nthPrime 1 = 2, nthPrime 2 = 3, ...).
    Defined via Mathlib's Nat.nth which enumerates infinite sets in order. -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The k-th prime is prime (for k ≥ 1). -/
theorem nthPrime_prime (k : ℕ) (hk : 1 ≤ k) : Nat.Prime (nthPrime k) := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (k - 1)

/-- nthPrime is strictly monotone. -/
theorem nthPrime_mono : StrictMono nthPrime := by
  intro a b hab
  exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : a - 1 < b - 1)

/-- Concrete values: nthPrime 1 = 2, nthPrime 2 = 3, nthPrime 3 = 5. -/
theorem nthPrime_vals : nthPrime 1 = 2 ∧ nthPrime 2 = 3 ∧ nthPrime 3 = 5 := by
  simp only [nthPrime, show 1 - 1 = 0 from rfl, show 2 - 1 = 1 from rfl, show 3 - 1 = 2 from rfl]
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The k-th primorial: product of the first k primes -/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => primorial k * nthPrime (k + 1)

/-- The set of positive integers less than n that are coprime to n -/
def coprimeResidues (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => 0 < a ∧ Nat.Coprime a n)

/-- Sorted list of coprime residues (defined via Finset.sort). -/
noncomputable def sortedCoprimes (n : ℕ) : List ℕ := (coprimeResidues n).sort (· ≤ ·)

theorem sortedCoprimes_sorted (n : ℕ) : (sortedCoprimes n).Pairwise (· < ·) := by
  sorry -- Follows from Finset.sort properties

theorem sortedCoprimes_mem (n : ℕ) (a : ℕ) :
    a ∈ sortedCoprimes n ↔ a ∈ coprimeResidues n := by
  simp [sortedCoprimes, Finset.mem_sort]

/- ## Gap Structure -/

/-- The set of consecutive gaps between coprime residues of n.
    Computed from the sorted coprime residue list. -/
noncomputable def gapSet (n : ℕ) : Finset ℕ :=
  let l := sortedCoprimes n
  (List.zipWith (· - ·) l.tail l).toFinset

/-- Every gap is even for k ≥ 2 (since nₖ is even, all coprime residues are odd) -/
axiom gaps_even (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd : d ∈ gapSet (primorial k)) :
  2 ∣ d

/-- The maximal gap between consecutive coprime residues of n.
    Defined as the supremum of the gap set. -/
noncomputable def maxGap (n : ℕ) : ℕ := (gapSet n).sup id

theorem maxGap_mem (n : ℕ) (hn : 1 < n) : maxGap n ∈ gapSet n := by
  sorry -- Requires showing gapSet n is nonempty for n > 1

theorem maxGap_max (n : ℕ) (d : ℕ) (hd : d ∈ gapSet n) : d ≤ maxGap n :=
  Finset.le_sup hd

/-- Number of distinct gap values. -/
noncomputable def distinctGapCount (n : ℕ) : ℕ := (gapSet n).card

theorem distinctGapCount_def (n : ℕ) :
    distinctGapCount n = (gapSet n).card := rfl

/- ## Known Bounds -/

/-- Maximal gap for primorial(k) grows like 2pₖ (the Jacobsthal function bound) -/
axiom maxGap_bound (k : ℕ) (hk : 2 ≤ k) :
  maxGap (primorial k) ≤ 2 * nthPrime k

/-- The first missing gap: smallest positive even integer not in gapSet(n). -/
noncomputable def firstMissingGap (n : ℕ) : ℕ :=
  2 * Nat.find (⟨n, fun h => by omega⟩ : ∃ m, 2 * m ∉ gapSet n)

theorem firstMissingGap_even (_k : ℕ) (_hk : 2 ≤ _k) :
    2 ∣ firstMissingGap (primorial _k) :=
  dvd_mul_right 2 _

theorem firstMissingGap_missing (k : ℕ) (_hk : 2 ≤ k) :
    firstMissingGap (primorial k) ∉ gapSet (primorial k) :=
  Nat.find_spec (⟨primorial k, fun h => by omega⟩ : ∃ m, 2 * m ∉ gapSet (primorial k))

/-- Lacampagne–Selfridge computation: for nₖ = 30030 (k=6),
    not all even integers up to the maximal gap appear -/
axiom lacampagne_selfridge_counterexample :
  ∃ d : ℕ, 2 ∣ d ∧ d < maxGap (primorial 6) ∧ d ∉ gapSet (primorial 6)

/- ## The Erdős Conjectures -/

/-- Erdős Problem 854, Part 1: Estimate the smallest even integer
    not representable as a consecutive gap in coprime residues of primorials -/
axiom ErdosProblem854_missing_gap_growth :
  ∀ C : ℕ, ∃ k : ℕ, C ≤ firstMissingGap (primorial k)

/-- Erdős Problem 854, Part 2: The number of distinct even gaps
    is proportional to the maximal gap -/
axiom ErdosProblem854_many_gaps :
  ∃ c : ℚ, 0 < c ∧
    ∀ k : ℕ, 2 ≤ k →
      c * (maxGap (primorial k) : ℚ) ≤ (distinctGapCount (primorial k) : ℚ)
