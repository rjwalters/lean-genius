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

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos854

open Nat

/- ## Primorial and Coprime Residues -/

/-- The k-th prime number (0-indexed: nthPrime 0 = 2, nthPrime 1 = 3, ...) -/
noncomputable def nthPrime (k : ℕ) : ℕ := k.nth Prime

theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime := Nat.prime_nth_prime k

theorem nthPrime_mono : StrictMono nthPrime := Nat.nth_prime_strictMono

theorem nthPrime_zero : nthPrime 0 = 2 := by
  simp [nthPrime, Nat.nth_prime_zero]

theorem nthPrime_one : nthPrime 1 = 3 := by
  simp [nthPrime, Nat.nth_prime_one]

theorem nthPrime_two : nthPrime 2 = 5 := by
  simp [nthPrime]
  native_decide

/-- The k-th primorial: product of the first k primes (0-indexed).
    primorial 0 = 1, primorial 1 = 2, primorial 2 = 6, primorial 3 = 30 -/
noncomputable def primorial : ℕ → ℕ
  | 0 => 1
  | k + 1 => primorial k * nthPrime k

/-- The set of positive integers less than n that are coprime to n -/
def coprimeResidues (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun a => 0 < a ∧ Nat.Coprime a n)

/-- Sorted list of coprime residues (defined via Finset.sort). -/
noncomputable def sortedCoprimes (n : ℕ) : List ℕ := (coprimeResidues n).sort (· ≤ ·)

theorem sortedCoprimes_sorted (n : ℕ) : (sortedCoprimes n).Pairwise (· < ·) := by
  unfold sortedCoprimes
  have hle := Finset.pairwise_sort (coprimeResidues n) (· ≤ ·)
  have hnd := (coprimeResidues n).sort_nodup (· ≤ ·)
  rw [List.pairwise_iff_getElem] at hle ⊢
  intro i j hi hj hij
  have hle' := hle i j hi hj hij
  have hne := (List.pairwise_iff_getElem.mp hnd) i j hi hj hij
  omega

theorem sortedCoprimes_mem (n : ℕ) (a : ℕ) :
    a ∈ sortedCoprimes n ↔ a ∈ coprimeResidues n := by
  simp [sortedCoprimes, Finset.mem_sort]

/- ## Gap Structure -/

/-- The set of consecutive gaps between coprime residues of n.
    Computed from the sorted coprime residue list. -/
noncomputable def gapSet (n : ℕ) : Finset ℕ :=
  let l := sortedCoprimes n
  (List.zipWith (· - ·) l.tail l).toFinset

/-- The primorial of k is divisible by 2 for k ≥ 1. -/
private theorem two_dvd_primorial : ∀ k : ℕ, 1 ≤ k → 2 ∣ primorial k
  | 0, h => absurd h (by omega)
  | 1, _ => by simp [primorial, nthPrime_zero]
  | k + 2, _ => dvd_mul_of_dvd_left (two_dvd_primorial (k + 1) (by omega)) _

/-- Every coprime residue of an even number is odd. -/
private theorem coprimeResidues_odd (n : ℕ) (hn : 2 ∣ n)
    (a : ℕ) (ha : a ∈ coprimeResidues n) : ¬ 2 ∣ a := by
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨_, _, hcop⟩ := ha
  intro h2a
  have h2g : (2 : ℕ) ∣ Nat.gcd a n := Nat.dvd_gcd h2a hn
  rw [hcop] at h2g
  exact absurd h2g (by norm_num)

/-- Differences of elements where all elements satisfy ¬(2 ∣ ·) are even. -/
private theorem zipWith_sub_dvd_two :
    ∀ (l : List ℕ), (∀ x ∈ l, ¬ 2 ∣ x) →
    ∀ d ∈ List.zipWith (· - ·) l.tail l, 2 ∣ d := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro hodd d hd
    cases t with
    | nil => simp at hd
    | cons b rest =>
      simp only [List.tail_cons, List.zipWith_cons_cons] at hd
      rcases List.mem_cons.mp hd with rfl | hmem
      · -- d = b - a, both odd ⇒ difference is even
        have ha := hodd a (List.mem_cons_self _ _)
        have hb := hodd b (List.mem_cons_of_mem _ (List.mem_cons_self _ _))
        have ha' : a % 2 ≠ 0 := fun h => ha (Nat.dvd_of_mod_eq_zero h)
        have hb' : b % 2 ≠ 0 := fun h => hb (Nat.dvd_of_mod_eq_zero h)
        exact Nat.dvd_of_mod_eq_zero (by omega)
      · exact ih (fun x hx => hodd x (List.mem_cons_of_mem _ hx)) d hmem

/-- Every gap is even for k ≥ 2 (since nₖ is even, all coprime residues are odd) -/
theorem gaps_even (k : ℕ) (hk : 2 ≤ k) (d : ℕ) (hd : d ∈ gapSet (primorial k)) :
    2 ∣ d := by
  simp only [gapSet, List.mem_toFinset] at hd
  have hprim_even := two_dvd_primorial k (by omega)
  have hodd : ∀ x ∈ sortedCoprimes (primorial k), ¬ 2 ∣ x := by
    intro x hx
    rw [sortedCoprimes_mem] at hx
    exact coprimeResidues_odd (primorial k) hprim_even x hx
  exact zipWith_sub_dvd_two (sortedCoprimes (primorial k)) hodd d hd

/-- The maximal gap between consecutive coprime residues of n.
    Defined as the supremum of the gap set. -/
noncomputable def maxGap (n : ℕ) : ℕ := (gapSet n).sup id

theorem maxGap_mem (n : ℕ) (hne : (gapSet n).Nonempty) : maxGap n ∈ gapSet n := by
  simp only [maxGap]
  have hmem := Finset.max'_mem (gapSet n) hne
  suffices h : (gapSet n).sup id = (gapSet n).max' hne by
    rw [h]; exact hmem
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    exact Finset.le_max' _ b hb
  · exact Finset.le_sup (f := id) hmem

theorem maxGap_max (n : ℕ) (d : ℕ) (hd : d ∈ gapSet n) : d ≤ maxGap n := by
  simp only [maxGap]; exact Finset.le_sup hd

/-- Number of distinct gap values. -/
noncomputable def distinctGapCount (n : ℕ) : ℕ := (gapSet n).card

theorem distinctGapCount_def (n : ℕ) :
    distinctGapCount n = (gapSet n).card := rfl

/- ## Known Bounds -/

/-- Maximal gap for primorial(k) grows like 2pₖ₋₁ (the Jacobsthal function bound) -/
axiom maxGap_bound (k : ℕ) (hk : 2 ≤ k) :
  maxGap (primorial k) ≤ 2 * nthPrime (k - 1)

/-- The first missing gap: smallest positive even integer not in gapSet(n). -/
noncomputable def firstMissingGap (n : ℕ) : ℕ :=
  2 * Nat.find (⟨(gapSet n).sup id + 1, fun h => by
    have := Finset.le_sup (f := id) h
    simp at this
    omega⟩ : ∃ m, 2 * m ∉ gapSet n)

theorem firstMissingGap_even (_k : ℕ) (_hk : 2 ≤ _k) :
    2 ∣ firstMissingGap (primorial _k) :=
  dvd_mul_right 2 _

theorem firstMissingGap_missing (n : ℕ) :
    firstMissingGap n ∉ gapSet n := by
  simp only [firstMissingGap]
  exact Nat.find_spec _

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

/- ## Primorial Structure -/

/-- The primorial is always positive. -/
theorem primorial_pos : ∀ k : ℕ, 0 < primorial k
  | 0 => by simp [primorial]
  | k + 1 => Nat.mul_pos (primorial_pos k) (nthPrime_prime k).pos

/-- primorial k divides primorial (k+1). -/
theorem primorial_dvd_succ (k : ℕ) : primorial k ∣ primorial (k + 1) := by
  simp only [primorial]
  exact dvd_mul_right _ _

/-- The i-th prime divides primorial k for any i < k. -/
theorem nthPrime_dvd_primorial : ∀ (k i : ℕ), i < k → nthPrime i ∣ primorial k
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, i, h => by
    simp only [primorial]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with rfl | hi
    · exact dvd_mul_left _ _
    · exact dvd_mul_of_dvd_left (nthPrime_dvd_primorial k i hi) _

/- ## Coprime Residue Membership -/

/-- 1 is always a coprime residue of n > 1. -/
theorem coprimeResidues_one_mem (n : ℕ) (hn : 1 < n) : 1 ∈ coprimeResidues n := by
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range]
  exact ⟨hn, Nat.one_pos, Nat.gcd_one_left n⟩

/-- n - 1 is coprime to n for n > 1. -/
theorem coprime_n_sub_one (n : ℕ) (hn : 1 < n) : Nat.Coprime (n - 1) n := by
  have h : n = n - 1 + 1 := by omega
  conv_rhs => rw [h]
  exact Nat.coprime_succ_self (n - 1)

/-- n - 1 is a coprime residue of n for n > 1. -/
theorem coprimeResidues_nminus1_mem (n : ℕ) (hn : 1 < n) : n - 1 ∈ coprimeResidues n := by
  simp only [coprimeResidues, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by omega, coprime_n_sub_one n hn⟩

end Erdos854
