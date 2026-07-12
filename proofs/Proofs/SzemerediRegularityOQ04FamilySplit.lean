/-
# Szemerédi Regularity (OQ-04): m-fold whole-partition refinement monotonicity

The `partitionEnergy` docstring states, as a general fact, that the size-weighted
energy is *"monotone under refinement (splitting a part never decreases energy)"*.
The OQ-04 development proves this only for a **two-piece** single-part split
(`partitionEnergy_single_split_mono`, Bridge) and for the sharp **2×2** product
refinement (`partitionEnergy_prod_refinement_gain`, Assembly).  This file discharges
the documented `2×2 → m×k` next step at the monotonicity level: refining **one part**
`A` into an arbitrary disjoint family `{Aᵢ}_{i∈I}` with `A = ⋃ᵢ Aᵢ` never decreases
`partitionEnergy`.

## What this file proves (0 axioms, 0 sorries)

* `pairEnergy_biUnion_split_mono` — the m-fold left analogue of `pairEnergy_split_mono`:
  `pairEnergy G (⋃ᵢ Aᵢ) B ≤ Σᵢ pairEnergy G (Aᵢ) B` for a disjoint family `{Aᵢ}`.
  Proved by `Finset.induction` on `I`, folding the two-piece split lemma over the
  `biUnion`.
* `pairEnergy_biUnion_split_mono_right` — its second-argument mirror, transported
  through `pairEnergy_comm`.
* `partitionEnergy_biUnion_split_mono` — **the m-fold whole-partition refinement
  monotonicity.**  For a disjoint family `{Aᵢ}_{i∈I}` (`As` injective on `I`, each
  `Aᵢ ∉ R`, and `⋃ᵢ Aᵢ ∉ R`),
  `partitionEnergy G (insert (⋃ᵢ Aᵢ) R) ≤ partitionEnergy G (I.image As ∪ R)`.

The whole-partition proof mirrors `partitionEnergy_single_split_mono`: the ordered-pair
sum `partitionEnergy = Σ_{P,Q} pairEnergy` (bridge `partitionEnergy_eq_sum_pairEnergy`)
splits into a diagonal block `(A,A)`, a row block `(A,R)`, a column block `(R,A)` and
the untouched `R × R` block; each of the three affected blocks is controlled by the
m-fold pair split lemmas above (the row/column blocks by a single application, the
diagonal by one on each coordinate).  Only the arithmetic of `Finset.sum_image`
(over the injective family) and `Finset.sum_comm` (to align the row block) is added.

This is the reusable structural half of the true AFKS refinement — where every part is
split simultaneously into many pieces — and it upgrades the `partitionEnergy` docstring's
general monotonicity claim from the two-piece special case to arbitrary finite families.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Bridge

namespace Szemeredi.RegularityOQ04FamilySplit

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: m-FOLD ONE-SIDED PAIR-ENERGY SPLIT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- **m-fold left refinement monotonicity of `pairEnergy`.**  Splitting the `A`-side of
a pair into an arbitrary disjoint family `{Aᵢ}_{i∈I}` (with `A = ⋃ᵢ Aᵢ`) never decreases
its total normalized energy contribution:
`pairEnergy G (⋃ᵢ Aᵢ) B ≤ Σᵢ pairEnergy G (Aᵢ) B`.  This is the `Finset`-family analogue
of the two-piece `pairEnergy_split_mono`, obtained by induction on `I` folding the
two-piece split over `Finset.biUnion`. -/
theorem pairEnergy_biUnion_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (As : ι → Finset V) (B : Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) :
    pairEnergy G (I.biUnion As) B ≤ ∑ i ∈ I, pairEnergy G (As i) B := by
  classical
  revert hA
  induction I using Finset.induction with
  | empty => intro _; simp [pairEnergy, Finset.biUnion_empty]
  | @insert a s ha ih =>
      intro hA
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      have hsub : (↑s : Set ι).PairwiseDisjoint As :=
        hA.subset (by rw [Finset.coe_insert]; exact Set.subset_insert _ _)
      have hdisj : Disjoint (As a) (s.biUnion As) := by
        rw [Finset.disjoint_biUnion_right]
        intro i hi
        exact hA (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact ha hi)
      calc pairEnergy G (As a ∪ s.biUnion As) B
          ≤ pairEnergy G (As a) B + pairEnergy G (s.biUnion As) B :=
            pairEnergy_split_mono G (As a) (s.biUnion As) B hdisj
        _ ≤ pairEnergy G (As a) B + ∑ i ∈ s, pairEnergy G (As i) B := by
            linarith [ih hsub]

/-- **m-fold right refinement monotonicity of `pairEnergy`.**  The second-argument
mirror of `pairEnergy_biUnion_split_mono`, transported through `pairEnergy_comm`:
`pairEnergy G A (⋃ⱼ Bⱼ) ≤ Σⱼ pairEnergy G A (Bⱼ)`. -/
theorem pairEnergy_biUnion_split_mono_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {ι : Type*} [DecidableEq ι] (J : Finset ι) (Bs : ι → Finset V)
    (hB : (↑J : Set ι).PairwiseDisjoint Bs) :
    pairEnergy G A (J.biUnion Bs) ≤ ∑ j ∈ J, pairEnergy G A (Bs j) := by
  rw [pairEnergy_comm G A (J.biUnion Bs)]
  refine (pairEnergy_biUnion_split_mono G J Bs A hB).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl (fun j _ => pairEnergy_comm G (Bs j) A)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: m-FOLD WHOLE-PARTITION REFINEMENT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- **m-fold whole-partition refinement monotonicity of `partitionEnergy`.**
Refining a single part `A = ⋃ᵢ Aᵢ` of a partition into an arbitrary disjoint family
`{Aᵢ}_{i∈I}` — the `As` injective on `I`, each fine cell `Aᵢ ∉ R`, and the coarse part
`⋃ᵢ Aᵢ ∉ R` — never decreases `partitionEnergy`:

`partitionEnergy G (insert (⋃ᵢ Aᵢ) R) ≤ partitionEnergy G (I.image As ∪ R)`.

This is the arbitrary-family generalization of the two-piece `partitionEnergy_single_split_mono`.
The ordered-pair sum decomposes into a diagonal `(A,A)` block, a row `(A,R)` block, a
column `(R,A)` block and the untouched `R × R` block; the three affected blocks are each
controlled by the m-fold pair split lemmas of PART I. -/
theorem partitionEnergy_biUnion_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (R : Finset (Finset V)) (I : Finset ι) (As : ι → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hinj : Set.InjOn As ↑I)
    (hAR : ∀ i ∈ I, As i ∉ R) (hfresh : I.biUnion As ∉ R) :
    partitionEnergy G (insert (I.biUnion As) R) ≤
      partitionEnergy G (I.image As ∪ R) := by
  classical
  -- The refined cells are disjoint from the untouched blocks `R`.
  have hdisjImR : Disjoint (I.image As) R := by
    rw [Finset.disjoint_left]
    intro x hx hxR
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hAR i hi hxR
  -- Nested-double-sum form of `partitionEnergy`, from the bridge lemma.
  have hdouble : ∀ parts : Finset (Finset V),
      partitionEnergy G parts = ∑ P ∈ parts, ∑ Q ∈ parts, pairEnergy G P Q := by
    intro parts
    rw [partitionEnergy_eq_sum_pairEnergy,
      show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]
  -- Rewrite the family image-sums as `I`-sums via injectivity.
  have himg : ∀ F : Finset V → ℚ, ∑ P ∈ I.image As, F P = ∑ i ∈ I, F (As i) := by
    intro F
    rw [Finset.sum_image]
    intro x hx y hy h
    exact hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h
  -- LHS block decomposition.
  have hL : partitionEnergy G (insert (I.biUnion As) R)
      = pairEnergy G (I.biUnion As) (I.biUnion As)
        + (∑ Q ∈ R, pairEnergy G (I.biUnion As) Q)
        + (∑ P ∈ R, pairEnergy G P (I.biUnion As))
        + (∑ P ∈ R, ∑ Q ∈ R, pairEnergy G P Q) := by
    rw [hdouble, Finset.sum_insert hfresh]
    simp only [Finset.sum_insert hfresh]
    rw [Finset.sum_add_distrib]
    ring
  -- RHS block decomposition.
  have hR : partitionEnergy G (I.image As ∪ R)
      = (∑ i ∈ I, ∑ j ∈ I, pairEnergy G (As i) (As j))
        + (∑ i ∈ I, ∑ Q ∈ R, pairEnergy G (As i) Q)
        + (∑ P ∈ R, ∑ i ∈ I, pairEnergy G P (As i))
        + (∑ P ∈ R, ∑ Q ∈ R, pairEnergy G P Q) := by
    rw [hdouble, Finset.sum_union hdisjImR]
    simp only [Finset.sum_union hdisjImR, Finset.sum_add_distrib, himg]
    ring
  -- Diagonal block: `pe A A ≤ Σᵢⱼ pe Aᵢ Aⱼ`.
  have hdiag : pairEnergy G (I.biUnion As) (I.biUnion As)
      ≤ ∑ i ∈ I, ∑ j ∈ I, pairEnergy G (As i) (As j) := by
    refine (pairEnergy_biUnion_split_mono G I As (I.biUnion As) hA).trans ?_
    exact Finset.sum_le_sum
      (fun i _ => pairEnergy_biUnion_split_mono_right G (As i) I As hA)
  -- Row block: `Σ_{Q∈R} pe A Q ≤ Σᵢ Σ_{Q∈R} pe Aᵢ Q`.
  have hrow : ∑ Q ∈ R, pairEnergy G (I.biUnion As) Q
      ≤ ∑ i ∈ I, ∑ Q ∈ R, pairEnergy G (As i) Q := by
    have step : ∑ Q ∈ R, pairEnergy G (I.biUnion As) Q
        ≤ ∑ Q ∈ R, ∑ i ∈ I, pairEnergy G (As i) Q :=
      Finset.sum_le_sum (fun Q _ => pairEnergy_biUnion_split_mono G I As Q hA)
    rwa [Finset.sum_comm] at step
  -- Column block: `Σ_{P∈R} pe P A ≤ Σ_{P∈R} Σᵢ pe P Aᵢ`.
  have hcol : ∑ P ∈ R, pairEnergy G P (I.biUnion As)
      ≤ ∑ P ∈ R, ∑ i ∈ I, pairEnergy G P (As i) :=
    Finset.sum_le_sum (fun P _ => pairEnergy_biUnion_split_mono_right G P I As hA)
  rw [hL, hR]
  linarith [hdiag, hrow, hcol]

end Szemeredi.RegularityOQ04FamilySplit
