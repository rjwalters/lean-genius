/-
  Aristotle targets for Erdős Problem #220: Squared Gaps Between Reduced Residues
  Routine supporting lemmas for automated proof search.
  See Erdos220Problem.lean for the main formalization.

  Targets:
  - reducedResidues_mem_range: m ∈ reducedResidues n → m < n  (from filter/range)
  - reducedResidues_coprime: m ∈ reducedResidues n → Nat.Coprime m n  (from filter)
  - reducedResidues_pos: m ∈ reducedResidues n → m ≥ 1  (from filter)
  - zero_not_in_reducedResidues: 0 ∉ reducedResidues n for n ≥ 2
  - reducedResidues_eq_totient_filter: reducedResidues n = totient-filter for n ≥ 2
  - card_reducedResidues_ge2: |reducedResidues n| = φ(n) for n ≥ 2

  Note: card_reducedResidues with n ≥ 1 (from main file) is likely incorrect at n = 1
  since reducedResidues 1 = ∅ but Nat.totient 1 = 1. We target the corrected n ≥ 2 form.

  Excluded:
  - sum_gaps_bound: requires List telescoping over sortedResidues/getD, too complex
  - montgomery_vaughan_* : axiomatized research results
-/
import Proofs.Erdos220Problem
import Mathlib

namespace Erdos220Aristotle

open Erdos220

/-- Elements of reducedResidues n are strictly less than n. -/
lemma reducedResidues_mem_range (n m : ℕ) (hm : m ∈ reducedResidues n) : m < n := by
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_range] at hm
  exact hm.1

/-- Elements of reducedResidues n are coprime with n. -/
lemma reducedResidues_coprime (n m : ℕ) (hm : m ∈ reducedResidues n) : Nat.Coprime m n := by
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_range] at hm
  exact hm.2.2

/-- Elements of reducedResidues n are at least 1. -/
lemma reducedResidues_pos (n m : ℕ) (hm : m ∈ reducedResidues n) : m ≥ 1 := by
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_range] at hm
  exact hm.2.1

/-- For n ≥ 2, 0 is not in reducedResidues n. -/
lemma zero_not_in_reducedResidues (n : ℕ) (hn : n ≥ 2) : 0 ∉ reducedResidues n := by
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_range, not_and]
  intro _
  omega

/-- For n ≥ 2, reducedResidues n agrees with the standard Nat.totient filter.
    The m ≥ 1 condition is redundant since 0 cannot be coprime with n ≥ 2. -/
lemma reducedResidues_eq_totient_filter (n : ℕ) (hn : n ≥ 2) :
    reducedResidues n = (Finset.range n).filter (Nat.Coprime n) := by
  ext m
  simp only [reducedResidues, Finset.mem_filter, Finset.mem_range, Nat.Coprime]
  constructor
  · rintro ⟨hlt, _, hcop⟩
    exact ⟨hlt, hcop.symm⟩
  · rintro ⟨hlt, hcop⟩
    refine ⟨hlt, ?_, hcop.symm⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp only [Nat.Coprime, Nat.gcd_zero_right] at hcop; omega
    · exact hpos

/-- For n ≥ 2, the cardinality of reducedResidues n equals Euler's totient φ(n). -/
lemma card_reducedResidues_ge2 (n : ℕ) (hn : n ≥ 2) :
    (reducedResidues n).card = Nat.totient n := by
  rw [reducedResidues_eq_totient_filter n hn]
  rfl

end Erdos220Aristotle
