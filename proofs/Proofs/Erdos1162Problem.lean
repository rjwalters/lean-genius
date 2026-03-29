/-
# Erdős Problem #1162: Number of Subgroups of S_n

Source: https://erdosproblems.com/1162
Status: OPEN (partially resolved)

Statement:
Give an asymptotic formula for the number of subgroups of S_n.
Is there a statistical theorem on their order?

A problem of Erdős and Turán.

Known Results:
- Pyber (1993): log f(n) ≍ n² (exact order of magnitude) [DERIVED from RDT]
- Roney-Dougal-Tracey (2025): log f(n) = (1/16 + o(1))n² (asymptotic formula) [AXIOM]
Axioms: 7 (numSubgroups defined, numSubgroups_pos proved, trivial_upper proved)
Sorries: 0

The key insight is that most subgroups of S_n arise from subgroups of S_n
that contain a large elementary abelian 2-group acting on ⌊n/4⌋ points.
The constant 1/16 = (1/4)² comes from choosing pairs from ⌊n/4⌋ points.

References:
- [Va99,5.73] Vardi, "Paul Erdős: Selected problems" (1999)
- [Py93] Pyber, "Enumerating finite groups of given order" (1993)
- [RoTr25] Roney-Dougal-Tracey, "The number of subgroups of the symmetric group" (2025)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Subgroup.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset

open Real Filter

noncomputable section

namespace Erdos1162

/- ## Part I: Subgroups of S_n -/

/-- The symmetric group S_n, realized as permutations of Fin n. -/
def Sn (n : ℕ) := Equiv.Perm (Fin n)

/-- The type of subgroups of a finite group is Finite, since subgroups inject
    into Finset G via their carrier filtered from Finset.univ. -/
instance instFiniteSubgroupPerm (n : ℕ) : Finite (Subgroup (Equiv.Perm (Fin n))) := by
  classical
  apply Finite.of_injective
    (fun H : Subgroup (Equiv.Perm (Fin n)) => Finset.univ.filter (· ∈ H))
  intro H₁ H₂ heq
  ext x
  have : x ∈ Finset.univ.filter (· ∈ H₁) ↔ x ∈ Finset.univ.filter (· ∈ H₂) := by rw [heq]
  simpa using this

/-- f(n) = the number of subgroups of S_n.
    Defined as the cardinality of the type of all subgroups of S_n. -/
def numSubgroups (n : ℕ) : ℕ :=
  @Fintype.card (Subgroup (Equiv.Perm (Fin n))) (Fintype.ofFinite _)

/-- f(n) ≥ 1 since the trivial subgroup ⊥ always exists. -/
theorem numSubgroups_pos (n : ℕ) : numSubgroups n ≥ 1 := by
  unfold numSubgroups
  exact Fintype.card_pos

/- ## Part II: Trivial Bounds -/

/-- **Trivial Upper Bound:**
    f(n) ≤ 2^(n!) since each subgroup is a subset of S_n.
    Proved: subgroups inject into Finset G via carrier.toFinset,
    and |Finset G| = 2^|G| = 2^(n!). -/
theorem trivial_upper (n : ℕ) :
    (numSubgroups n : ℝ) ≤ 2 ^ (n.factorial : ℝ) := by
  unfold numSubgroups
  suffices h : @Fintype.card (Subgroup (Equiv.Perm (Fin n))) (Fintype.ofFinite _) ≤ 2 ^ n.factorial by
    have h2 : (@Fintype.card (Subgroup (Equiv.Perm (Fin n))) (Fintype.ofFinite _) : ℝ) ≤
        (2 ^ n.factorial : ℝ) := by exact_mod_cast h
    convert h2 using 1
    push_cast
    ring
  -- Inject subgroups into Finset G via Finset.univ.filter
  have hinj : Function.Injective (fun H : Subgroup (Equiv.Perm (Fin n)) =>
      @Set.toFinset _ (H : Set (Equiv.Perm (Fin n))) (inferInstance)) := by
    intro H₁ H₂ heq
    ext x
    have : x ∈ @Set.toFinset _ (H₁ : Set _) (inferInstance) ↔
           x ∈ @Set.toFinset _ (H₂ : Set _) (inferInstance) := by rw [heq]
    simp only [Set.mem_toFinset] at this
    exact this
  calc @Fintype.card (Subgroup (Equiv.Perm (Fin n))) (Fintype.ofFinite _)
      ≤ @Fintype.card (Finset (Equiv.Perm (Fin n))) inferInstance :=
        Fintype.card_le_of_injective _ hinj
    _ = 2 ^ Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_finset
    _ = 2 ^ n.factorial := by rw [Fintype.card_perm]

/-- **Lower Bound from Elementary Abelian 2-Groups:**
    S_n contains (Z/2Z)^⌊n/2⌋ as a subgroup (transpositions on disjoint pairs).
    This subgroup has 2^⌊n/2⌋ elements and hence many subgroups. -/

/- ## Part III: The Asymptotic Constant 1/16 (Roney-Dougal-Tracey 2025) -/

/-- The asymptotic constant: 1/16.
    This arises because the dominant contribution to subgroup count comes from
    elementary abelian 2-subgroups of the symmetric group on ⌊n/4⌋ points,
    and (1/4)² = 1/16 of the n² term. -/
def asymptoticConstant : ℝ := 1/16

/-- **Roney-Dougal-Tracey Theorem (2025):**
    log f(n) = (1/16 + o(1)) · n².
    This gives the precise asymptotic formula requested by Erdős and Turán.
    Axiomatized as a deep published result [RoTr25]. -/
axiom roney_dougal_tracey :
    Tendsto (fun n => Real.log (numSubgroups n : ℝ) / (n : ℝ)^2) atTop (nhds (1/16))

/-- **The asymptotic formula implies Pyber's theorem.**
    If f(n)/n² → 1/16, then choosing ε = 1/32 gives eventual bounds
    (1/32)n² ≤ log f(n) ≤ (3/32)n². -/
theorem rdt_implies_pyber :
    (Tendsto (fun n => Real.log (numSubgroups n : ℝ) / (n : ℝ)^2) atTop (nhds (1/16))) →
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
      c₁ * (n : ℝ)^2 ≤ Real.log (numSubgroups n : ℝ) ∧
      Real.log (numSubgroups n : ℝ) ≤ c₂ * (n : ℝ)^2 := by
  intro h
  refine ⟨1 / 32, 3 / 32, by norm_num, by norm_num, ?_⟩
  rw [Metric.tendsto_nhds] at h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h (1 / 32) (by norm_num))
  exact ⟨N, fun n hn => by
    have hd := hN n hn
    rw [Real.dist_eq] at hd
    have hab := abs_lt.mp hd
    have h_lo : Real.log (numSubgroups n : ℝ) / (n : ℝ) ^ 2 > 1 / 32 := by linarith [hab.1]
    have h_hi : Real.log (numSubgroups n : ℝ) / (n : ℝ) ^ 2 < 3 / 32 := by linarith [hab.2]
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by
      by_contra hle; push_neg at hle
      have := le_antisymm hle (sq_nonneg _)
      rw [this, div_zero] at h_lo; linarith
    constructor
    · rw [lt_div_iff hn2] at h_lo; linarith
    · rw [div_lt_iff hn2] at h_hi; linarith⟩

/- ## Part IV: Pyber's Theorem (1993) -/

/-- **Pyber's Theorem (1993):** log f(n) ≍ n².
    There exist constants c₁, c₂ > 0 such that
    c₁ · n² ≤ log f(n) ≤ c₂ · n² for all sufficiently large n.
    This follows from the stronger Roney-Dougal-Tracey asymptotic (2025). -/
theorem pyber_theorem :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    c₁ * (n : ℝ)^2 ≤ Real.log (numSubgroups n : ℝ) ∧
    Real.log (numSubgroups n : ℝ) ≤ c₂ * (n : ℝ)^2 :=
  rdt_implies_pyber roney_dougal_tracey

/- ## Part V: Elementary Abelian 2-Groups -/

/-- The rank of the largest elementary abelian 2-subgroup of S_n.
    This is ⌊n/2⌋ (achieved by disjoint transpositions). -/
def maxElem2Rank (n : ℕ) : ℕ := n / 2

/-- The subgroup (Z/2Z)^⌊n/2⌋ in S_n: products of disjoint transpositions.
    This is the largest elementary abelian 2-subgroup. -/

/-- Number of subgroups of (Z/2Z)^k.
    This is the Gaussian binomial coefficient sum, which grows as 2^(k²/4). -/
axiom numSubgroupsElem2 (k : ℕ) : ℕ

/-- **Key Fact:** log(number of subgroups of (Z/2Z)^k) ~ k²/4.
    The Gaussian binomial coefficients give the exact count. -/
axiom elem2_subgroup_count_asymptotic :
  Tendsto (fun k => Real.log (numSubgroupsElem2 k : ℝ) / (k : ℝ)^2) atTop (nhds (1/4))

/-- **Connection to 1/16:**
    The dominant contribution to f(n) comes from subgroups of the wreath product
    (Z/2Z) ≀ S_{⌊n/4⌋}. The elementary abelian 2-group of rank ⌊n/4⌋ has
    ~ 2^((n/4)²/4) = 2^(n²/64) subgroups, giving log f(n) ~ n²/16 · log 2. -/
theorem constant_explanation :
    (1 : ℝ) / 4 * (1 / 4) = 1 / 16 := by norm_num

/- ## Part VI: Subgroup Orders -/

/-- The "statistical theorem on their order" part of the problem:
    What is the distribution of |H| as H ranges over subgroups of S_n? -/

/-- Most subgroups of S_n are 2-groups (qualitative observation).
    The elementary abelian 2-subgroups dominate the count.
    A precise formalization would require defining the proportion of 2-group
    subgroups among all subgroups of S_n, which needs a Fintype instance
    for Subgroup (Equiv.Perm (Fin n)). -/

/- ## Part VII: Small Cases -/

/-- f(1) = 1: S_1 has only the trivial subgroup. -/
axiom f1 : numSubgroups 1 = 1

/-- f(2) = 2: S_2 has {e} and S_2 itself. -/
axiom f2 : numSubgroups 2 = 2

/-- f(3) = 6: S_3 has {e}, three copies of Z/2Z, one Z/3Z, and S_3 itself. -/
axiom f3 : numSubgroups 3 = 6

/-- f(4) = 30: S_4 has 30 subgroups. -/
axiom f4 : numSubgroups 4 = 30

/- ## Part VIII: Growth Rate Summary -/

/-- The function n ↦ log f(n) / n² converges to 1/16. -/
def erdos1162_asymptotic : Prop :=
  Tendsto (fun n => Real.log (numSubgroups n : ℝ) / (n : ℝ)^2) atTop (nhds (1/16))

/-- **Erdős Problem #1162: Partially Resolved**

  Question: Give an asymptotic formula for the number of subgroups of S_n.
  Answer: log f(n) = (1/16 + o(1))n² (Roney-Dougal-Tracey 2025)

  The "statistical theorem on their order" part remains less explored. -/
theorem erdos_1162 : erdos1162_asymptotic := roney_dougal_tracey

end Erdos1162
