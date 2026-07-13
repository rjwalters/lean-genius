/-
# Szemerédi Regularity (OQ-04): the m-fold whole-partition refinement GAIN

`SzemerediRegularityOQ04FamilySplit.lean` proves the **floor** for an arbitrary-family
whole-partition refinement — refining one part `A = ⋃ᵢ Aᵢ` of a partition into a disjoint
family `{Aᵢ}_{i∈I}` never *decreases* `partitionEnergy`
(`partitionEnergy_biUnion_split_mono`).  Separately, the Product file supplies the
quantitative **pair-level** gain over an arbitrary product family
(`pairEnergy_prod_family_refinement_gain`): a witness cell `(Aᵢ₀, Bⱼ₀)` whose density
deviates from the coarse density by `≥ d` forces a strict energy jump
`≥ |Aᵢ₀||Bⱼ₀|·d²/n²`.

This file combines the two into the documented next step: the **m-fold whole-partition
GAIN**.  Refining one part `A = ⋃ᵢ Aᵢ`, if two of the fine cells `Aᵢ₀, Aⱼ₀` have a density
spread `d` on the diagonal `(A,A)` block — i.e.
`|d(Aᵢ₀, Aⱼ₀) − d(A, A)| ≥ d` — then the whole-partition energy strictly increases by at
least the corresponding surplus on top of the monotonicity floor:

`partitionEnergy G (insert (⋃ᵢ Aᵢ) R) + |Aᵢ₀||Aⱼ₀|·d²/n² ≤ partitionEnergy G (I.image As ∪ R)`.

## Proof (0 axioms, 0 sorries)

The ordered-pair sum `partitionEnergy = Σ_{P,Q} pairEnergy` (bridge
`partitionEnergy_eq_sum_pairEnergy`) decomposes, exactly as in the monotonicity file, into
a diagonal `(A,A)` block, a row `(A,R)` block, a column `(R,A)` block, and the untouched
`R × R` block.  The row and column blocks are still bounded below only by monotonicity
(the m-fold pair split lemmas of `FamilySplit`); the surplus is injected on the **diagonal**
block, where `pairEnergy_prod_family_refinement_gain` with `I = J`, `As = Bs` gives
`pairEnergy G A A + |Aᵢ₀||Aⱼ₀|·d²/n² ≤ Σᵢⱼ pairEnergy G Aᵢ Aⱼ`.  Adding the three block
inequalities and the untouched block equality yields the whole-partition surplus.

This is the family analogue of the two-piece `partitionEnergy_single_split_gain` (Bridge),
lifting the strict energy increment from a single 2-way split to an arbitrary finite
family, and is the GAIN companion of `partitionEnergy_biUnion_split_mono`.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04FamilySplit
import Proofs.SzemerediRegularityOQ04Product

namespace Szemeredi.RegularityOQ04FamilyGain

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04FamilySplit

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **m-fold whole-partition refinement GAIN.**  Refining a single part `A = ⋃ᵢ Aᵢ` of a
partition into an arbitrary disjoint family `{Aᵢ}_{i∈I}` (the `As` injective on `I`, each
fine cell `Aᵢ ∉ R`, and the coarse part `⋃ᵢ Aᵢ ∉ R`), with a diagonal density-spread
witness `i₀, j₀ ∈ I` satisfying `d ≤ |d(Aᵢ₀, Aⱼ₀) − d(A, A)|`, increases `partitionEnergy`
by at least the surplus `|Aᵢ₀||Aⱼ₀|·d²/n²` on top of the monotonicity floor:

`partitionEnergy G (insert (⋃ᵢ Aᵢ) R) + |Aᵢ₀||Aⱼ₀|·d²/n² ≤ partitionEnergy G (I.image As ∪ R)`.

The row/column/`R×R` blocks contribute the monotonicity floor of
`partitionEnergy_biUnion_split_mono`; the diagonal `(A,A)` block carries the strict surplus,
supplied by `pairEnergy_prod_family_refinement_gain` at `I = J`, `As = Bs`. -/
theorem partitionEnergy_biUnion_split_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (R : Finset (Finset V)) (I : Finset ι) (As : ι → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hinj : Set.InjOn As ↑I)
    (hAR : ∀ i ∈ I, As i ∉ R) (hfresh : I.biUnion As ∉ R)
    (i₀ j₀ : ι) (hi₀ : i₀ ∈ I) (hj₀ : j₀ ∈ I) (d : ℚ) (hd : 0 ≤ d)
    (hdev : d ≤ |edgeDensity G (As i₀) (As j₀) -
                  edgeDensity G (I.biUnion As) (I.biUnion As)|) :
    partitionEnergy G (insert (I.biUnion As) R)
        + (↑(As i₀).card : ℚ) * ↑(As j₀).card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
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
  -- Diagonal block **with surplus**: the product-family gain at `I = J`, `As = Bs`.
  have hdiag : pairEnergy G (I.biUnion As) (I.biUnion As)
        + (↑(As i₀).card : ℚ) * ↑(As j₀).card / (Fintype.card V : ℚ) ^ 2 * d ^ 2
      ≤ ∑ i ∈ I, ∑ j ∈ I, pairEnergy G (As i) (As j) :=
    pairEnergy_prod_family_refinement_gain G I I As As hA hA i₀ j₀ hi₀ hj₀ d hd hdev
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

end Szemeredi.RegularityOQ04FamilyGain


