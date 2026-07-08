/-
  Aristotle targets for Erdős Problem #771 (Subsets Avoiding a Given Sum)
  Routine supporting lemmas for automated proof search.
  See Erdos771Problem.lean for the main formalization.

  Criteria for inclusion:
  - prime_multiples_size: |(multiples of p in {1,...,n})| = ⌊n/p⌋ (Mathlib count)
  - prime_multiples_avoid: multiples of p form an m-avoiding set when p ∤ m
    (any subset sum of p-multiples is divisible by p, but p ∤ m)
  - NOT f_characterization (maximal characterization of f, definitional)
  - NOT erdos_graham_conjecture_true (main theorem: f(n) ~ n/2·log n)
  - NOT leading_constant (asymptotic constant analysis)
-/
import Mathlib

namespace Erdos771ProblemAristotle

open Finset BigOperators Real Nat

/-- The set {1, ..., n}. -/
def Icc_n (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Multiples of p in {1,...,n}. -/
def primeMutliples (p n : ℕ) : Finset ℕ :=
  (Icc_n n).filter (fun k => p ∣ k)

-- Routine: Count of multiples of p in {1,...,n} equals ⌊n/p⌋.
-- Uses Finset.Nat.card_multiples or Icc filter card formula.
theorem prime_multiples_size (p n : ℕ) (_hp : p > 0) :
    (primeMutliples p n).card = n / p := by
  have hIcc : Icc_n n = Finset.Ioc 0 n := by
    unfold Icc_n; ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold primeMutliples
  rw [hIcc]
  exact Nat.Ioc_filter_dvd_card_eq_div n p

-- Routine: The set of all subset sums of S.
noncomputable def subsetSums (S : Finset ℕ) : Finset ℕ :=
  (S.powerset.image (fun A => ∑ a ∈ A, a)).filter (· > 0)

-- Routine: Definition of sum-avoidance.
def AvoidSum (S : Finset ℕ) (m : ℕ) : Prop :=
  m ∉ subsetSums S

-- Routine: Multiples of prime p avoid sum m when p ∤ m.
-- Every element of primeMutliples p n is divisible by p; any
-- nonempty subset sum is also divisible by p; since p ∤ m, m cannot
-- be achieved as a subset sum.
theorem prime_multiples_avoid (p m n : ℕ) (_hp : Nat.Prime p) (hpm : ¬p ∣ m) :
    AvoidSum (primeMutliples p n) m := by
  intro hmem
  rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
  obtain ⟨⟨A, hA, hAsum⟩, _⟩ := hmem
  rw [Finset.mem_powerset] at hA
  have hdvd : p ∣ ∑ a ∈ A, a := by
    refine Finset.dvd_sum (fun a ha => ?_)
    have ha' : a ∈ primeMutliples p n := hA ha
    rw [primeMutliples, Finset.mem_filter] at ha'
    exact ha'.2
  rw [hAsum] at hdvd
  exact hpm hdvd

end Erdos771ProblemAristotle
