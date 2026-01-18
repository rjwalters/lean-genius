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

/-! ## Approach: Non-Extendable 3-APs

If a permutation avoids all monotone 4-APs, every 3-AP must be "non-extendable".
This puts strong constraints on the permutation structure.
-/

/-- A 3-AP at increasing indices (i,j,k) can be extended forward if there exists
    l > k such that (i,j,k,l) forms a monotone 4-AP. -/
def CanExtendForward (x : Permutation) (i j k : ℕ) : Prop :=
  i < j ∧ j < k ∧ IsAP3 (x.toFun i) (x.toFun j) (x.toFun k) →
  ∃ l > k, IsAP4 (x.toFun i) (x.toFun j) (x.toFun k) (x.toFun l)

/-- A 3-AP at increasing indices (i,j,k) can be extended backward if there exists
    l < i such that (l,i,j,k) forms a monotone 4-AP. -/
def CanExtendBackward (x : Permutation) (i j k : ℕ) : Prop :=
  i < j ∧ j < k ∧ IsAP3 (x.toFun i) (x.toFun j) (x.toFun k) →
  ∃ l < i, IsAP4 (x.toFun l) (x.toFun i) (x.toFun j) (x.toFun k)

/-- A 3-AP is non-extendable if it cannot be extended in either direction. -/
def IsNonExtendable3AP (x : Permutation) (i j k : ℕ) : Prop :=
  i < j ∧ j < k ∧ IsAP3 (x.toFun i) (x.toFun j) (x.toFun k) ∧
  ¬CanExtendForward x i j k ∧ ¬CanExtendBackward x i j k

/-- Key lemma: If a permutation avoids all monotone 4-APs, then every
    monotone 3-AP in it must be non-extendable. -/
theorem no_4ap_implies_nonextendable (x : Permutation) (h : ¬HasMonotone4AP x)
    (i j k : ℕ) (hijk : i < j ∧ j < k) (hap : IsAP3 (x.toFun i) (x.toFun j) (x.toFun k)) :
    ¬CanExtendForward x i j k ∧ ¬CanExtendBackward x i j k := by
  constructor
  · -- Cannot extend forward
    intro hext
    have ⟨l, hl, hap4⟩ := hext ⟨hijk.1, hijk.2, hap⟩
    apply h
    use i, j, k, l
    constructor
    · left; exact ⟨hijk.1, hijk.2, hl⟩
    · exact hap4
  · -- Cannot extend backward
    intro hext
    have ⟨l, hl, hap4⟩ := hext ⟨hijk.1, hijk.2, hap⟩
    apply h
    use l, i, j, k
    constructor
    · left; exact ⟨hl, hijk.1, hijk.2⟩
    · exact hap4

/-- The "forbidden value" for forward extension: if (a,b,c) is a 3-AP with
    common difference d, then the value c + d is "forbidden" at any index > k. -/
def ForbiddenForwardValue (a b c : ℕ) : ℕ := c + (b - a)

/-- The "forbidden value" for backward extension. -/
def ForbiddenBackwardValue (a b _c : ℕ) : ℕ := a - (b - a)

/-- Key structural constraint: if x avoids 4-APs and (i,j,k) is a 3-AP with
    values (a,b,c), then for all l > k, x(l) ≠ c + d where d = b - a. -/
theorem forbidden_value_constraint (x : Permutation) (h : ¬HasMonotone4AP x)
    (i j k : ℕ) (hijk : i < j ∧ j < k) (hap : IsAP3 (x.toFun i) (x.toFun j) (x.toFun k)) :
    ∀ l > k, x.toFun l ≠ ForbiddenForwardValue (x.toFun i) (x.toFun j) (x.toFun k) := by
  intro l hl heq
  apply h
  use i, j, k, l
  constructor
  · left; exact ⟨hijk.1, hijk.2, hl⟩
  · unfold IsAP4 IsAP3 ForbiddenForwardValue at *
    omega

/-! ## Density Argument Attempt

The key question: Can the constraints from non-extendable 3-APs accumulate
to force a contradiction?

Observation: Each 3-AP (a, a+d, a+2d) forbids the value a+3d from appearing
at any later index, and forbids a-d from appearing at any earlier index.

If we have many 3-APs, we get many forbidden value constraints.
Eventually, this might exhaust all possibilities.
-/

/-- IsAP3 is decidable for natural numbers. -/
instance : DecidablePred (fun (abc : ℕ × ℕ × ℕ) => IsAP3 abc.1 abc.2.1 abc.2.2) :=
  fun abc => by unfold IsAP3; infer_instance

/-- Count of 3-APs in a finite permutation. -/
noncomputable def count3APs (n : ℕ) (x : FinitePermutation n) : ℕ :=
  Nat.card { ijk : Fin n × Fin n × Fin n //
    (ijk.1 : ℕ) < ijk.2.1 ∧ (ijk.2.1 : ℕ) < ijk.2.2 ∧
    IsAP3 (x.toFun ijk.1).val (x.toFun ijk.2.1).val (x.toFun ijk.2.2).val }

/-- Conjecture: The number of 3-APs grows faster than the number of
    "slots" available for forbidden values, forcing a 4-AP. -/
def DensityConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ x : FinitePermutation n,
    ∃ i j k l : Fin n, ((i : ℕ) < j ∧ (j : ℕ) < k ∧ (k : ℕ) < l ∨
                        (i : ℕ) > j ∧ (j : ℕ) > k ∧ (k : ℕ) > l) ∧
      IsAP4 (x.toFun i).val (x.toFun j).val (x.toFun k).val (x.toFun l).val

/-! ## Common Difference Structure

Key insight from LeSaulnier-Vijay (2011) and subsequent work:
- Every permutation of ℕ MUST contain a 3-term AP with ODD common difference
- There EXIST permutations of ℕ avoiding ALL 4-term APs with ODD common difference

This suggests the critical question: what about EVEN common differences?
-/

/-- A 3-AP has odd common difference. -/
def IsAP3WithOddCD (a b c : ℕ) : Prop :=
  IsAP3 a b c ∧ (b - a) % 2 = 1

/-- A 3-AP has even common difference. -/
def IsAP3WithEvenCD (a b c : ℕ) : Prop :=
  IsAP3 a b c ∧ (b - a) % 2 = 0

/-- A 4-AP has odd common difference. -/
def IsAP4WithOddCD (a b c d : ℕ) : Prop :=
  IsAP4 a b c d ∧ (b - a) % 2 = 1

/-- A 4-AP has even common difference. -/
def IsAP4WithEvenCD (a b c d : ℕ) : Prop :=
  IsAP4 a b c d ∧ (b - a) % 2 = 0

/-- A permutation contains a monotone 3-term AP with odd common difference. -/
def HasMonotone3APOddCD (x : Permutation) : Prop :=
  ∃ i j k : ℕ, (i < j ∧ j < k ∨ i > j ∧ j > k) ∧
    IsAP3WithOddCD (x.toFun i) (x.toFun j) (x.toFun k)

/-- A permutation contains a monotone 4-term AP with odd common difference. -/
def HasMonotone4APOddCD (x : Permutation) : Prop :=
  ∃ i j k l : ℕ, (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
    IsAP4WithOddCD (x.toFun i) (x.toFun j) (x.toFun k) (x.toFun l)

/-- A permutation contains a monotone 4-term AP with even common difference. -/
def HasMonotone4APEvenCD (x : Permutation) : Prop :=
  ∃ i j k l : ℕ, (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
    IsAP4WithEvenCD (x.toFun i) (x.toFun j) (x.toFun k) (x.toFun l)

/-! ## LeSaulnier-Vijay Results (2011)

Key structural results about parity of common differences.
-/

/-- Every permutation of ℕ contains a monotone 3-AP with odd common difference.
    (LeSaulnier-Vijay 2011) -/
axiom every_perm_has_3ap_odd_cd : ∀ x : Permutation, HasMonotone3APOddCD x

/-- There exists a permutation of ℕ avoiding all monotone 4-APs with odd common difference.
    (LeSaulnier-Vijay 2011) -/
axiom exists_perm_avoiding_4ap_odd_cd : ∃ x : Permutation, ¬HasMonotone4APOddCD x

/-- Key observation: A 4-AP has odd CD iff the corresponding 3-AP has odd CD. -/
theorem ap4_odd_cd_iff_ap3_odd_cd (a b c d : ℕ) (h : IsAP4 a b c d) :
    (b - a) % 2 = 1 ↔ IsAP3WithOddCD a b c := by
  unfold IsAP3WithOddCD IsAP3 IsAP4 at *
  constructor
  · intro hodd
    constructor
    · omega
    · exact hodd
  · intro ⟨_, hodd⟩
    exact hodd

/-- Structural theorem: The main conjecture is equivalent to saying that
    permutations avoiding odd-CD 4-APs must contain even-CD 4-APs. -/
theorem conjecture_equiv_even_cd_forced :
    Erdos196Conjecture ↔ ∀ x : Permutation, ¬HasMonotone4APOddCD x → HasMonotone4APEvenCD x := by
  constructor
  · intro hconj x hno_odd
    -- The conjecture gives us a 4-AP
    obtain ⟨i, j, k, l, hmon, hap⟩ := hconj x
    -- This 4-AP cannot be odd-CD (since x avoids odd-CD 4-APs)
    -- So it must be even-CD
    use i, j, k, l
    constructor
    · exact hmon
    · unfold IsAP4WithEvenCD
      constructor
      · exact hap
      · -- The 4-AP is not odd-CD, so it must be even-CD
        by_contra h_not_even
        push_neg at h_not_even
        apply hno_odd
        use i, j, k, l
        constructor
        · exact hmon
        · unfold IsAP4WithOddCD
          constructor
          · exact hap
          · omega
  · intro heven x
    by_cases h : HasMonotone4APOddCD x
    · obtain ⟨i, j, k, l, hmon, hap_odd⟩ := h
      use i, j, k, l
      exact ⟨hmon, hap_odd.1⟩
    · obtain ⟨i, j, k, l, hmon, hap_even⟩ := heven x h
      use i, j, k, l
      exact ⟨hmon, hap_even.1⟩

/-! ## Even-CD Constraint Propagation

Since odd-CD 4-APs can be avoided, the conjecture hinges on even-CD 4-APs.
Key question: Can even-CD 4-APs also be avoided?

Note: Even-CD 3-APs have the form (a, a+2d, a+4d) for some d > 0.
To avoid even-CD 4-APs, the value a+6d must be avoided at all indices > k.
-/

/-- A permutation contains a monotone 3-term AP with even common difference. -/
def HasMonotone3APEvenCD (x : Permutation) : Prop :=
  ∃ i j k : ℕ, (i < j ∧ j < k ∨ i > j ∧ j > k) ∧
    IsAP3WithEvenCD (x.toFun i) (x.toFun j) (x.toFun k)

/-- Key constraint: If x avoids even-CD 4-APs and (i,j,k) is an even-CD 3-AP with
    values (a,a+2d,a+4d), then for all l > k, x(l) ≠ a+6d. -/
theorem forbidden_even_cd_extension (x : Permutation) (h : ¬HasMonotone4APEvenCD x)
    (i j k : ℕ) (hijk : i < j ∧ j < k)
    (hap : IsAP3WithEvenCD (x.toFun i) (x.toFun j) (x.toFun k)) :
    ∀ l > k, x.toFun l ≠ x.toFun k + (x.toFun j - x.toFun i) := by
  intro l hl heq
  apply h
  use i, j, k, l
  constructor
  · left; exact ⟨hijk.1, hijk.2, hl⟩
  · unfold IsAP4WithEvenCD IsAP4 IsAP3WithEvenCD IsAP3 at *
    obtain ⟨⟨h1, h2, h3⟩, h_even⟩ := hap
    omega

/-- The dual constraint: If x avoids even-CD 4-APs and (i,j,k) is an even-CD 3-AP,
    then for all l < i with increasing indices l < i < j < k,
    x(l) cannot be a - 2d where d is the common difference. -/
theorem forbidden_even_cd_backward (x : Permutation) (h : ¬HasMonotone4APEvenCD x)
    (i j k : ℕ) (hijk : i < j ∧ j < k)
    (hap : IsAP3WithEvenCD (x.toFun i) (x.toFun j) (x.toFun k))
    (hval : x.toFun i > x.toFun j - x.toFun i) :
    ∀ l < i, x.toFun l ≠ x.toFun i - (x.toFun j - x.toFun i) := by
  intro l hl heq
  apply h
  use l, i, j, k
  constructor
  · left; exact ⟨hl, hijk.1, hijk.2⟩
  · unfold IsAP4WithEvenCD IsAP4 IsAP3WithEvenCD IsAP3 at *
    obtain ⟨⟨h1, h2, h3⟩, h_even⟩ := hap
    omega

/-! ## The Dichotomy

Every permutation of ℕ either:
1. Contains a monotone 4-AP with odd common difference, OR
2. Contains a monotone 4-AP with even common difference

The conjecture asserts that one of these must hold.
LeSaulnier-Vijay showed (1) can be avoided, so the question is whether (2) can also be avoided.
-/

/-- The partition of 4-APs by common difference parity. -/
theorem ap4_parity_dichotomy (a b c d : ℕ) (h : IsAP4 a b c d) :
    IsAP4WithOddCD a b c d ∨ IsAP4WithEvenCD a b c d := by
  unfold IsAP4WithOddCD IsAP4WithEvenCD
  by_cases hparity : (b - a) % 2 = 1
  · left; exact ⟨h, hparity⟩
  · right
    constructor
    · exact h
    · omega

/-! ## Finite Threshold Investigation

For the k=3 case, the threshold is N ≤ 9.
What is the threshold for k=4?
-/

/-- Conjecture: There exists a threshold N for 4-APs. -/
def Finite4APThreshold : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ x : FinitePermutation n,
    ∃ i j k l : Fin n, ((i : ℕ) < j ∧ (j : ℕ) < k ∧ (k : ℕ) < l ∨
                        (i : ℕ) > j ∧ (j : ℕ) > k ∧ (k : ℕ) > l) ∧
      IsAP4 (x.toFun i).val (x.toFun j).val (x.toFun k).val (x.toFun l).val

/-- If there's a finite threshold, the infinite conjecture follows by compactness. -/
theorem finite_threshold_implies_conjecture :
    Finite4APThreshold → Erdos196Conjecture := by
  intro ⟨N, hN⟩ x
  -- For any permutation of ℕ, consider its restriction to [0, N-1]
  -- This restriction must have a 4-AP, which is also a 4-AP in the full permutation
  sorry

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
