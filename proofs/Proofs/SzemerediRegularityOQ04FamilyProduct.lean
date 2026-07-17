/-
# Szemerédi Regularity (OQ-04): two-sided m×k whole-partition refinement monotonicity

The OQ-04 development proves refinement monotonicity of `partitionEnergy` at three
levels of generality:

* two-piece single-part split (`partitionEnergy_single_split_mono`, Bridge),
* arbitrary-family **one-part** split (`partitionEnergy_biUnion_split_mono`,
  FamilySplit) — refine a single part `A = ⋃ᵢ Aᵢ` into a family,
* the sharp `2×2` and `m×k` product *gain* at the **pair** level
  (`pairEnergy_prod_family_refinement_gain`, Product) — refine a single pair `(A,B)`
  simultaneously on both coordinates.

This file discharges the documented next step *"lift to the full two-sided `m×k`
product refinement of a partition (refine both `A` and `B` simultaneously into
families)"* at the **monotonicity** level:

* `pairEnergy_biUnion_split_mono_two` — the two-sided pair-energy floor:
  `pairEnergy G (⋃ᵢ Aᵢ) (⋃ⱼ Bⱼ) ≤ Σᵢ Σⱼ pairEnergy G (Aᵢ) (Bⱼ)`.
  This is the witness-free (`d = 0`) monotonicity floor underneath
  `pairEnergy_prod_family_refinement_gain`, obtained by composing the two
  one-sided m-fold splits of PART I of FamilySplit.
* `partitionEnergy_biUnion_split_mono_two` — **the two-part whole-partition
  refinement monotonicity.**  Splitting **two distinct parts** `A = ⋃ᵢ Aᵢ` and
  `B = ⋃ⱼ Bⱼ` of a partition *simultaneously* into arbitrary disjoint families never
  decreases `partitionEnergy`:
  `partitionEnergy G (insert A (insert B R)) ≤ partitionEnergy G (J.image Bs ∪ (I.image As ∪ R))`.

The whole-partition proof needs no fresh block bookkeeping: it iterates the
one-part `partitionEnergy_biUnion_split_mono` twice — first splitting `A` inside the
partition `insert A (insert B R)` (treating `insert B R` as the untouched rest),
then splitting `B` inside the resulting `insert B (I.image As ∪ R)` — with the
distinctness hypotheses of a genuine partition (`Aᵢ ≠ B`, `Aᵢ ≠ Bⱼ`, `A ≠ B`, all
cells `∉ R`) supplying the two freshness discharges.  The middle equality
`I.image As ∪ insert B R = insert B (I.image As ∪ R)` is `Finset.union_insert`.

**What remains open** (the strict *gain*): with a genuinely `ε`-irregular witness
sub-cell `(i₀,j₀)` in the `A×B` cross block, both ordered cross blocks
`(A-family, B-family)` and `(B-family, A-family)` of the refined partition acquire
the `pairEnergy_prod_family_refinement_gain` surplus, giving a `2·ε⁴·|A||B|/n²`
whole-partition energy jump.  Formalizing that requires the full ordered `3×3`
block decomposition of the refined partition (A-family / B-family / R) and is the
precise next lemma; the monotonicity floor proved here is its structural half.

0 axioms, 0 sorries.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04FamilySplit

namespace Szemeredi.RegularityOQ04FamilyProduct

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04FamilySplit

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: TWO-SIDED PAIR-ENERGY REFINEMENT MONOTONICITY FLOOR
-- ═══════════════════════════════════════════════════════════════════

/-- **Two-sided `m×k` pair-energy refinement monotonicity.**  Refining a pair
`(A, B)` simultaneously on *both* coordinates into arbitrary disjoint families
`{Aᵢ}_{i∈I}` (`A = ⋃ᵢ Aᵢ`) and `{Bⱼ}_{j∈J}` (`B = ⋃ⱼ Bⱼ`) never decreases the
normalized pair energy:

`pairEnergy G (⋃ᵢ Aᵢ) (⋃ⱼ Bⱼ) ≤ Σᵢ Σⱼ pairEnergy G (Aᵢ) (Bⱼ)`.

This is the witness-free (`d = 0`) monotonicity floor underneath
`pairEnergy_prod_family_refinement_gain`; it composes the two one-sided m-fold
splits — first split the `A`-side against the whole `B = ⋃ⱼ Bⱼ`, then split the
`B`-side inside each summand. -/
theorem pairEnergy_biUnion_split_mono_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs) :
    pairEnergy G (I.biUnion As) (J.biUnion Bs) ≤
      ∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j) := by
  refine (pairEnergy_biUnion_split_mono G I As (J.biUnion Bs) hA).trans ?_
  exact Finset.sum_le_sum
    (fun i _ => pairEnergy_biUnion_split_mono_right G (As i) J Bs hB)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: TWO-PART WHOLE-PARTITION REFINEMENT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- **Two-part whole-partition refinement monotonicity of `partitionEnergy`.**
Splitting two *distinct* parts `A = ⋃ᵢ Aᵢ` and `B = ⋃ⱼ Bⱼ` of a partition
`insert A (insert B R)` *simultaneously* into arbitrary disjoint families
(`As`/`Bs` injective on `I`/`J`, all fine cells and coarse parts pairwise distinct
and `∉ R`) never decreases `partitionEnergy`:

`partitionEnergy G (insert A (insert B R)) ≤ partitionEnergy G (J.image Bs ∪ (I.image As ∪ R))`.

Proved by iterating the one-part `partitionEnergy_biUnion_split_mono` twice: split
`A` treating `insert B R` as the untouched rest, then split `B` treating
`I.image As ∪ R` as the rest.  The distinctness hypotheses of a genuine partition
discharge the two freshness side-conditions; the middle equality is
`Finset.union_insert`. -/
theorem partitionEnergy_biUnion_split_mono_two (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (R : Finset (Finset V)) (I : Finset ι) (J : Finset κ)
    (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hAinj : Set.InjOn As ↑I)
    (hB : (↑J : Set κ).PairwiseDisjoint Bs) (hBinj : Set.InjOn Bs ↑J)
    (hAR : ∀ i ∈ I, As i ∉ R) (hBR : ∀ j ∈ J, Bs j ∉ R)
    (hAfresh : I.biUnion As ∉ R) (hBfresh : J.biUnion Bs ∉ R)
    (hAB : I.biUnion As ≠ J.biUnion Bs)
    (hAiB : ∀ i ∈ I, As i ≠ J.biUnion Bs)
    (hAiBj : ∀ i ∈ I, ∀ j ∈ J, As i ≠ Bs j) :
    partitionEnergy G (insert (I.biUnion As) (insert (J.biUnion Bs) R)) ≤
      partitionEnergy G (J.image Bs ∪ (I.image As ∪ R)) := by
  classical
  -- Step 1: split `A = ⋃ᵢ Aᵢ` inside `insert A (insert B R)`, rest `= insert B R`.
  have hAR1 : ∀ i ∈ I, As i ∉ insert (J.biUnion Bs) R := by
    intro i hi hcontra
    rw [Finset.mem_insert] at hcontra
    rcases hcontra with hEq | hR
    · exact hAiB i hi hEq
    · exact hAR i hi hR
  have hAfresh1 : I.biUnion As ∉ insert (J.biUnion Bs) R := by
    intro hcontra
    rw [Finset.mem_insert] at hcontra
    rcases hcontra with hEq | hR
    · exact hAB hEq
    · exact hAfresh hR
  have step1 := partitionEnergy_biUnion_split_mono G (insert (J.biUnion Bs) R) I As
    hA hAinj hAR1 hAfresh1
  -- Step 2: split `B = ⋃ⱼ Bⱼ` inside `insert B (I.image As ∪ R)`, rest `= I.image As ∪ R`.
  have hBR2 : ∀ j ∈ J, Bs j ∉ (I.image As ∪ R) := by
    intro j hj hcontra
    rw [Finset.mem_union, Finset.mem_image] at hcontra
    rcases hcontra with ⟨i, hi, hEq⟩ | hR
    · exact hAiBj i hi j hj hEq
    · exact hBR j hj hR
  have hBfresh2 : J.biUnion Bs ∉ (I.image As ∪ R) := by
    intro hcontra
    rw [Finset.mem_union, Finset.mem_image] at hcontra
    rcases hcontra with ⟨i, hi, hEq⟩ | hR
    · exact hAiB i hi hEq
    · exact hBfresh hR
  have step2 := partitionEnergy_biUnion_split_mono G (I.image As ∪ R) J Bs
    hB hBinj hBR2 hBfresh2
  calc partitionEnergy G (insert (I.biUnion As) (insert (J.biUnion Bs) R))
      ≤ partitionEnergy G (I.image As ∪ insert (J.biUnion Bs) R) := step1
    _ = partitionEnergy G (insert (J.biUnion Bs) (I.image As ∪ R)) := by
          rw [Finset.union_insert]
    _ ≤ partitionEnergy G (J.image Bs ∪ (I.image As ∪ R)) := step2

end Szemeredi.RegularityOQ04FamilyProduct
