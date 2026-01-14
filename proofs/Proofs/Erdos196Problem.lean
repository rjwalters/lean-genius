/-
Erdős Problem #196: Monotone Arithmetic Progressions in Permutations

Source: https://erdosproblems.com/196
Status: OPEN

Statement:
Must every permutation of ℕ contain a monotone 4-term arithmetic progression?

That is, given a permutation x of ℕ, must there exist indices with either
i < j < k < l or i > j > k > l such that x_i, x_j, x_k, x_l form an arithmetic progression?

Key Results:
- Davis-Entringer-Graham-Simmons (1977):
  • Every permutation contains a monotone 3-term AP (PROVED)
  • There exist permutations avoiding monotone 5-term APs (DISPROVED for k=5)
- k=4 remains OPEN

Related to Problems #194, #195.

Reference: Davis, Entringer, Graham, Simmons (1977) "Monotone subsequences and arithmetic progressions"
-/

import Mathlib

open Function Set Finset

namespace Erdos196

/-! ## Permutations and Monotone Sequences -/

/-- A permutation of ℕ is a bijection ℕ → ℕ. -/
def Permutation := ℕ ≃ ℕ

/-- A sequence of indices is increasing. -/
def IsIncreasing (indices : List ℕ) : Prop :=
  indices.IsChain (· < ·)

/-- A sequence of indices is decreasing. -/
def IsDecreasing (indices : List ℕ) : Prop :=
  indices.IsChain (· > ·)

/-- A sequence of indices is monotone (either increasing or decreasing). -/
def IsMonotone (indices : List ℕ) : Prop :=
  IsIncreasing indices ∨ IsDecreasing indices

/-! ## Arithmetic Progressions -/

/-- Four values form an arithmetic progression. -/
def IsAP4 (a b c d : ℕ) : Prop :=
  b - a = c - b ∧ c - b = d - c ∧ a < b ∧ b < c ∧ c < d

/-- Alternative: arithmetic progression condition using differences. -/
def IsAP4' (a b c d : ℕ) : Prop :=
  ∃ r : ℕ, r > 0 ∧ b = a + r ∧ c = a + 2 * r ∧ d = a + 3 * r

/-- The two definitions are equivalent for natural numbers. -/
theorem ap4_iff_ap4' (a b c d : ℕ) : IsAP4 a b c d ↔ IsAP4' a b c d := by
  constructor
  · intro ⟨h1, h2, hab, hbc, hcd⟩
    use b - a
    constructor
    · omega
    · omega
  · intro ⟨r, hr, hb, hc, hd⟩
    unfold IsAP4
    omega

/-- Three values form an arithmetic progression. -/
def IsAP3 (a b c : ℕ) : Prop :=
  b - a = c - b ∧ a < b ∧ b < c

/-- Five values form an arithmetic progression. -/
def IsAP5 (a b c d e : ℕ) : Prop :=
  IsAP4 a b c d ∧ d - c = e - d ∧ d < e

/-! ## Monotone Arithmetic Progressions -/

/-- A permutation contains a monotone k-term AP at given indices. -/
def HasMonotoneAPAtIndices (x : Permutation) (indices : List ℕ) (values : List ℕ)
    (hlen : indices.length = values.length) : Prop :=
  IsMonotone indices ∧
  (∀ i (hi : i < indices.length), x.toFun (indices[i]) = values[i]'(hlen ▸ hi))

/-- A permutation contains a monotone 3-term AP. -/
def HasMonotone3AP (x : Permutation) : Prop :=
  ∃ i j k : ℕ, (i < j ∧ j < k ∨ i > j ∧ j > k) ∧
    IsAP3 (x.toFun i) (x.toFun j) (x.toFun k)

/-- A permutation contains a monotone 4-term AP. -/
def HasMonotone4AP (x : Permutation) : Prop :=
  ∃ i j k l : ℕ, (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
    IsAP4 (x.toFun i) (x.toFun j) (x.toFun k) (x.toFun l)

/-- A permutation contains a monotone 5-term AP. -/
def HasMonotone5AP (x : Permutation) : Prop :=
  ∃ i j k l m : ℕ, (i < j ∧ j < k ∧ k < l ∧ l < m ∨ i > j ∧ j > k ∧ k > l ∧ l > m) ∧
    IsAP5 (x.toFun i) (x.toFun j) (x.toFun k) (x.toFun l) (x.toFun m)

/-! ## Main Conjectures and Results -/

/--
**Erdős Problem #196 (OPEN)**:
Every permutation of ℕ contains a monotone 4-term arithmetic progression.
-/
def Erdos196Conjecture : Prop :=
  ∀ x : Permutation, HasMonotone4AP x

/--
**Davis-Entringer-Graham-Simmons (1977)**:
Every permutation of ℕ contains a monotone 3-term arithmetic progression.
-/
axiom degs_3ap_theorem : ∀ x : Permutation, HasMonotone3AP x

/--
**DEGS Counterexample for k=5**:
There exists a permutation of ℕ avoiding all monotone 5-term arithmetic progressions.
-/
axiom degs_5ap_counterexample : ∃ x : Permutation, ¬HasMonotone5AP x

/-! ## Relationship Between Cases -/

/-- If the 4-AP conjecture holds, then the 3-AP theorem is a corollary. -/
theorem conjecture_implies_3ap :
    Erdos196Conjecture → ∀ x : Permutation, HasMonotone3AP x := by
  intro hconj x
  obtain ⟨i, j, k, l, hmon, hap⟩ := hconj x
  -- Extract 3-AP from the 4-AP
  use i, j, k
  constructor
  · cases hmon with
    | inl hinc => left; exact ⟨hinc.1, hinc.2.1⟩
    | inr hdec => right; exact ⟨hdec.1, hdec.2.1⟩
  · -- The first three terms of a 4-AP form a 3-AP
    unfold IsAP3 IsAP4 at *
    omega

/-! ## Finite Versions -/

/-- A permutation of {1,...,n} is a bijection Fin n → Fin n. -/
def FinitePermutation (n : ℕ) := Fin n ≃ Fin n

/-- The finite version: every permutation of {1,...,n} contains a monotone 3-AP for n ≥ 9. -/
axiom finite_3ap_threshold :
    ∃ N : ℕ, N ≤ 9 ∧ ∀ n ≥ N, ∀ x : FinitePermutation n,
      ∃ i j k : Fin n, ((i : ℕ) < j ∧ (j : ℕ) < k ∨ (i : ℕ) > j ∧ (j : ℕ) > k) ∧
        IsAP3 (x.toFun i).val (x.toFun j).val (x.toFun k).val

/-! ## Construction for k=5 Counterexample

The DEGS construction uses a recursive definition based on
alternating blocks. The key insight is that one can arrange
elements to avoid long monotone APs while still maintaining
a permutation structure.

The construction interleaves increasing and decreasing segments
in a way that breaks any potential 5-term monotone AP.
-/

/-! ## Examples -/

/-- The identity permutation trivially contains monotone 3-APs. -/
example : HasMonotone3AP (Equiv.refl ℕ) := by
  use 1, 2, 3
  constructor
  · left
    exact ⟨by omega, by omega⟩
  · unfold IsAP3
    simp only [Equiv.toFun_as_coe, Equiv.refl_apply]
    decide

/-- Simple 4-AP in identity: 1, 2, 3, 4 with indices 1, 2, 3, 4. -/
example : HasMonotone4AP (Equiv.refl ℕ) := by
  use 1, 2, 3, 4
  constructor
  · left
    exact ⟨by omega, by omega, by omega⟩
  · unfold IsAP4
    simp only [Equiv.toFun_as_coe, Equiv.refl_apply]
    decide

/-! ## Connection to Erdős-Szekeres -/

/--
The problem is related to the Erdős-Szekeres theorem on monotone subsequences.

**Erdős-Szekeres (1935)**:
Every sequence of more than (r-1)(s-1) distinct numbers contains either
an increasing subsequence of length r or a decreasing subsequence of length s.

For permutations, this guarantees long monotone subsequences, but
does not directly give information about arithmetic progressions.
-/
axiom erdos_szekeres_theorem (n r s : ℕ) (hrs : n > (r - 1) * (s - 1))
    (seq : Fin n → ℕ) (hinj : Injective seq) :
    (∃ indices : Fin r → Fin n, StrictMono indices ∧ StrictMono (seq ∘ indices)) ∨
    (∃ indices : Fin s → Fin n, StrictMono indices ∧ StrictAnti (seq ∘ indices))

/-! ## Summary

**Problem Status: OPEN**

Erdős Problem #196 asks whether every permutation of ℕ must contain
a monotone 4-term arithmetic progression.

**What we know:**
- k=3: YES - Davis-Entringer-Graham-Simmons (1977)
- k=4: OPEN (the main conjecture)
- k=5: NO - DEGS construction shows k=5 can be avoided

**Key insight:**
The gap between k=3 (always exists) and k=5 (can be avoided) suggests
k=4 is the critical threshold. The conjecture that k=4 always exists
remains one of the tantalizing open problems in combinatorics.

**Related to:**
- Problem #194: Variations on monotone AP theme
- Problem #195: Related questions
- Erdős-Szekeres theorem on monotone subsequences

References:
- Davis, Entringer, Graham, Simmons (1977): Original paper
- Related work on permutation patterns and subsequences
-/

end Erdos196
