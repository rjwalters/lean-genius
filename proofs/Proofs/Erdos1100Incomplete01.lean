/-
  Erdős Problem #1100: The First Consecutive Divisor Pair is Always Coprime
  Companion to Erdos1100Problem.lean (incomplete-01)

  Erdős #1100 concerns τ⊥(n) = the number of indices i for which the i-th and
  (i+1)-th divisors of n (in increasing order 1 = d₁ < d₂ < ⋯ < d_τ(n) = n)
  are coprime. The parent file Erdos1100Problem.lean states the deep results
  (Erdős–Hall, Erdős–Simonovits) as axioms and ALSO axiomatizes the "trivial"
  lower bound τ⊥(n) ≥ ω(n), commenting that a formal proof "requires intricate
  reasoning about sorted divisor positions."

  This self-contained companion proves, with 0 axioms / 0 sorries, the
  universal weak form of that lower bound that requires only the FIRST divisor:

    • `tauPerp_ge_one` : τ⊥(n) ≥ 1 for every n ≥ 2.

  The key observation is that the smallest divisor is always d₁ = 1, so the
  first consecutive pair (d₁, d₂) = (1, d₂) is automatically coprime
  (gcd(1, ·) = 1) — no matter what d₂ is. This gives a coprime pair for free,
  hence τ⊥(n) ≥ 1. It matches the axiomatized bound τ⊥(n) ≥ ω(n) exactly when
  ω(n) = 1 (prime powers), where it is tight.

  We also expose the coprimality of the first pair directly (`first_pair_coprime`)
  and pin the edge case `tauPerp_one = 0` (n = 1 has a single divisor and thus no
  consecutive pairs).

  Reference: https://erdosproblems.com/1100
-/

import Mathlib

namespace Erdos1100Coprime

open Finset

/- ## Definitions (matching Erdos1100Problem.lean) -/

/-- The list of divisors of n in increasing order: 1 = d₁ < d₂ < ⋯ < d_τ(n) = n. -/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).sort (· ≤ ·)

/-- τ⊥(n): the number of indices i with gcd(dᵢ, dᵢ₊₁) = 1.
    (Stated without the parent's `let` binding so the body unfolds cleanly.) -/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  ((List.range ((divisorList n).length - 1)).filter
    (fun i => Nat.gcd ((divisorList n).getD i 0) ((divisorList n).getD (i + 1) 0) = 1)).length

/- ## The divisor set: 1 and n are members -/

private lemma one_mem_divisorFilter (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℕ) ∈ Finset.filter (· ∣ n) (Finset.range (n + 1)) := by
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, one_dvd n⟩

private lemma self_mem_divisorFilter (n : ℕ) (_hn : 1 ≤ n) :
    n ∈ Finset.filter (· ∣ n) (Finset.range (n + 1)) := by
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, dvd_refl n⟩

/- ## The first divisor is 1, and there are ≥ 2 divisors when n ≥ 2 -/

/-- The first entry of the (sorted) divisor list is 1, for every n ≥ 1. -/
private lemma divisorList_getD_zero (n : ℕ) (hn : 1 ≤ n) :
    (divisorList n).getD 0 0 = 1 := by
  unfold divisorList
  have hne : (Finset.filter (· ∣ n) (Finset.range (n + 1))).Nonempty :=
    ⟨1, one_mem_divisorFilter n hn⟩
  have hpos : 0 < ((Finset.filter (· ∣ n) (Finset.range (n + 1))).sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact Finset.card_pos.mpr hne
  rw [List.getD_eq_getElem _ _ hpos, Finset.sorted_zero_eq_min']
  -- Goal: (filter …).min' _ = 1
  refine le_antisymm (Finset.min'_le _ 1 (one_mem_divisorFilter n hn)) ?_
  have hmem := Finset.min'_mem (Finset.filter (· ∣ n) (Finset.range (n + 1))) hne
  exact Nat.pos_of_dvd_of_pos (Finset.mem_filter.mp hmem).2 (by omega)

/-- A set with n ≥ 2 has at least two divisors (1 and n). -/
private lemma divisorList_length_ge_two (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ (divisorList n).length := by
  unfold divisorList
  rw [Finset.length_sort]
  have : 1 < (Finset.filter (· ∣ n) (Finset.range (n + 1))).card :=
    Finset.one_lt_card.mpr
      ⟨1, one_mem_divisorFilter n (by omega), n, self_mem_divisorFilter n (by omega), by omega⟩
  omega

/- ## Main results -/

/-- **The first consecutive divisor pair is always coprime, so τ⊥(n) ≥ 1.**
    Since d₁ = 1, the pair (d₁, d₂) = (1, d₂) is coprime for free. This proves
    the universal weak form of the parent's axiomatized τ⊥(n) ≥ ω(n) bound. -/
theorem tauPerp_ge_one (n : ℕ) (hn : 2 ≤ n) : 1 ≤ tauPerp n := by
  unfold tauPerp
  have h0 : (divisorList n).getD 0 0 = 1 := divisorList_getD_zero n (by omega)
  have hlen : 2 ≤ (divisorList n).length := divisorList_length_ge_two n hn
  -- index 0 satisfies the coprimality predicate and lies in range (length - 1)
  have hmem : 0 ∈ (List.range ((divisorList n).length - 1)).filter
      (fun i => Nat.gcd ((divisorList n).getD i 0) ((divisorList n).getD (i + 1) 0) = 1) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    have hp : Nat.gcd ((divisorList n).getD 0 0) ((divisorList n).getD (0 + 1) 0) = 1 := by
      rw [h0]; exact Nat.gcd_one_left _
    simpa using hp
  have := List.length_pos_iff.mpr (List.ne_nil_of_mem hmem)
  omega

/-- The first consecutive divisor pair, stated directly: gcd(d₁, d₂) = 1. -/
theorem first_pair_coprime (n : ℕ) (hn : 2 ≤ n) :
    Nat.gcd ((divisorList n).getD 0 0) ((divisorList n).getD 1 0) = 1 := by
  rw [divisorList_getD_zero n (by omega), Nat.gcd_one_left]

/-- Edge case: τ⊥(1) = 0 (a single divisor, no consecutive pairs). -/
theorem tauPerp_one : tauPerp 1 = 0 := by
  have hfilter : Finset.filter (· ∣ 1) (Finset.range (1 + 1)) = {1} := by decide
  have hd : divisorList 1 = [1] := by
    unfold divisorList; rw [hfilter]; simp
  unfold tauPerp
  rw [hd]
  simp

end Erdos1100Coprime
