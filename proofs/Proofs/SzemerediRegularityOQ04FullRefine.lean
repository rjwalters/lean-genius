/-
# Szemerédi Regularity (OQ-04): full simultaneous refinement monotonicity

The `partitionEnergy` docstring states, as a general fact, that the size-weighted
energy is *"monotone under refinement (splitting a part never decreases energy)"*.
The OQ-04 development proved this for a **two-piece** single-part split
(`partitionEnergy_single_split_mono`, Bridge), the sharp **2×2** product refinement
(`partitionEnergy_prod_refinement_gain`, Assembly), and — most recently — for the
**m-fold split of one part** into an arbitrary disjoint family
(`partitionEnergy_biUnion_split_mono`, FamilySplit).

This file closes the documented `2×2 → m×k` next step in **full generality**: it
refines **every part simultaneously**.  Given a partition `P` and, for each part `A`,
a disjoint family `pieces A` of fine cells with `⋃ (pieces A) = A`, the refined
partition `P.biUnion pieces` never has smaller `partitionEnergy` than `P`.

## What this file proves (0 axioms, 0 sorries)

* `pairEnergy_biUnion_split_mono_prod` — the two-sided m×k pair split:
  `pairEnergy G (⋃ᵢ Aᵢ) (⋃ⱼ Bⱼ) ≤ Σᵢ Σⱼ pairEnergy G (Aᵢ) (Bⱼ)`, obtained by chaining
  the left split `pairEnergy_biUnion_split_mono` with the right split
  `pairEnergy_biUnion_split_mono_right` inside the resulting sum.  This is the "product
  cell" pair bound underlying a simultaneous refinement of both coordinates.
* `partitionEnergy_refine_mono` — **full simultaneous refinement monotonicity.**  For a
  partition `P` and a cell assignment `pieces : Finset V → Finset (Finset V)` with
  * `hcover`  : each part is the union of its cells, `(pieces A).biUnion id = A`;
  * `hdisjIn` : the cells of each part are pairwise disjoint;
  * `hdisjOut`: distinct parts get disjoint cell-collections (`P.PairwiseDisjoint pieces`),
  the refined partition satisfies `partitionEnergy G P ≤ partitionEnergy G (P.biUnion pieces)`.

The proof is a direct pair decomposition, not an induction: writing
`partitionEnergy = Σ_{A,B} pairEnergy A B` (bridge, nested form), each ordered pair term
`pairEnergy A B` is bounded by `Σ_{c∈pieces A} Σ_{d∈pieces B} pairEnergy c d` via the
two-sided pair split (using `hcover` to expose `A = ⋃ cells`, `B = ⋃ cells`), and the
resulting quadruple sum reassembles — via `Finset.sum_biUnion` over the disjoint cell
families (`hdisjOut`) and one `Finset.sum_comm` — into `partitionEnergy (P.biUnion pieces)`.

This upgrades the `partitionEnergy` docstring's general monotonicity claim from the
one-part special case to the genuine AFKS refinement, where every part is split at once.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04FamilySplit

namespace Szemeredi.RegularityOQ04FullRefine

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04FamilySplit

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: TWO-SIDED (m×k) PAIR-ENERGY SPLIT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- **Two-sided m×k refinement monotonicity of `pairEnergy`.**  Splitting *both* sides
of a pair into disjoint families — `A = ⋃ᵢ Aᵢ`, `B = ⋃ⱼ Bⱼ` — never decreases the total
normalized energy contribution:
`pairEnergy G (⋃ᵢ Aᵢ) (⋃ⱼ Bⱼ) ≤ Σᵢ Σⱼ pairEnergy G (Aᵢ) (Bⱼ)`.  Obtained by chaining
the one-sided splits `pairEnergy_biUnion_split_mono` (left) and
`pairEnergy_biUnion_split_mono_right` (right, applied inside the sum). -/
theorem pairEnergy_biUnion_split_mono_prod (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (As : ι → Finset V) (J : Finset κ) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs) :
    pairEnergy G (I.biUnion As) (J.biUnion Bs)
      ≤ ∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j) := by
  calc pairEnergy G (I.biUnion As) (J.biUnion Bs)
      ≤ ∑ i ∈ I, pairEnergy G (As i) (J.biUnion Bs) :=
        pairEnergy_biUnion_split_mono G I As (J.biUnion Bs) hA
    _ ≤ ∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j) :=
        Finset.sum_le_sum
          (fun i _ => pairEnergy_biUnion_split_mono_right G (As i) J Bs hB)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: FULL SIMULTANEOUS REFINEMENT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- **Full simultaneous refinement monotonicity of `partitionEnergy`.**  Refining *every*
part `A` of a partition `P` into a disjoint family of cells `pieces A` (with `⋃ pieces A = A`)
and taking the union `P.biUnion pieces` of all cells never decreases `partitionEnergy`:

`partitionEnergy G P ≤ partitionEnergy G (P.biUnion pieces)`.

Hypotheses: each part is covered by its cells (`hcover`), the cells within a part are
pairwise disjoint (`hdisjIn`), and distinct parts receive disjoint cell-collections
(`hdisjOut`).  This is the genuine AFKS refinement — every part split at once — of which
`partitionEnergy_single_split_mono` and `partitionEnergy_biUnion_split_mono` are the
one-part special cases. -/
theorem partitionEnergy_refine_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset (Finset V)) (pieces : Finset V → Finset (Finset V))
    (hcover : ∀ A ∈ P, (pieces A).biUnion id = A)
    (hdisjIn : ∀ A ∈ P, (↑(pieces A) : Set (Finset V)).PairwiseDisjoint id)
    (hdisjOut : (↑P : Set (Finset V)).PairwiseDisjoint pieces) :
    partitionEnergy G P ≤ partitionEnergy G (P.biUnion pieces) := by
  classical
  -- Nested-double-sum form of `partitionEnergy`, from the bridge lemma.
  have hdouble : ∀ parts : Finset (Finset V),
      partitionEnergy G parts = ∑ P ∈ parts, ∑ Q ∈ parts, pairEnergy G P Q := by
    intro parts
    rw [partitionEnergy_eq_sum_pairEnergy,
      show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]
  -- Per ordered pair of parts: the coarse `pairEnergy A B` is dominated by the sum of
  -- fine-cell contributions, via the two-sided pair split (after exposing A, B as unions).
  have key : ∀ A ∈ P, ∀ B ∈ P,
      pairEnergy G A B ≤ ∑ c ∈ pieces A, ∑ d ∈ pieces B, pairEnergy G c d := by
    intro A hA B hB
    have h := pairEnergy_biUnion_split_mono_prod G (pieces A) id (pieces B) id
      (hdisjIn A hA) (hdisjIn B hB)
    rw [hcover A hA, hcover B hB] at h
    simpa using h
  -- Expansion of the refined-partition energy into the fine quadruple sum.
  have hPB : partitionEnergy G (P.biUnion pieces)
      = ∑ A ∈ P, ∑ c ∈ pieces A, ∑ B ∈ P, ∑ d ∈ pieces B, pairEnergy G c d := by
    rw [hdouble (P.biUnion pieces), Finset.sum_biUnion hdisjOut]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_biUnion hdisjOut]
  calc partitionEnergy G P
      = ∑ A ∈ P, ∑ B ∈ P, pairEnergy G A B := hdouble P
    _ ≤ ∑ A ∈ P, ∑ B ∈ P, ∑ c ∈ pieces A, ∑ d ∈ pieces B, pairEnergy G c d :=
        Finset.sum_le_sum (fun A hA =>
          Finset.sum_le_sum (fun B hB => key A hA B hB))
    _ = ∑ A ∈ P, ∑ c ∈ pieces A, ∑ B ∈ P, ∑ d ∈ pieces B, pairEnergy G c d :=
        Finset.sum_congr rfl (fun A _ => Finset.sum_comm)
    _ = partitionEnergy G (P.biUnion pieces) := hPB.symm

end Szemeredi.RegularityOQ04FullRefine
