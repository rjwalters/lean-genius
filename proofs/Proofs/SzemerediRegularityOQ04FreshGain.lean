/-
# Szemerédi Regularity (OQ-04): freshness wired into the sharp 2×2 energy gain

This companion carries out the standing next-step of the OQ-04 assembly: **wire
`freshness_of_partition` (from `SzemerediRegularityOQ04Fresh`) into the whole-partition
sharp 2×2 gain lemmas of `SzemerediRegularityOQ04Assembly`, discharging their six
set-theoretic freshness side-conditions.**

## The six freshness hypotheses

`partitionEnergy_prod_refinement_gain` and its `ε⁴` floor `partitionEnergy_prod_gain_eps4`
each carry six `∉`-hypotheses recording that the coarse pieces `A, B` and the four fine
cells `A₁, A₂, B₁, B₂` are pairwise fresh with respect to each other and to the remaining
blocks `R`:

* `A ∉ insert B R`, `B ∉ R`,
* `A₁ ∉ insert A₂ (insert B₁ (insert B₂ R))`, `A₂ ∉ insert B₁ (insert B₂ R)`,
* `B₁ ∉ insert B₂ R`, `B₂ ∉ R`.

These are bookkeeping conditions the `Finset.sum_insert` expansion of `partitionEnergy`
needs; they say nothing analytic.  `freshness_of_partition` already proves all six from a
genuine partition model: the cells tile their coarse blocks (`A₁ ∪ A₂ = A`, `B₁ ∪ B₂ = B`),
the cells are nonempty and disjoint, the two coarse blocks are disjoint (`Disjoint A B`),
and every remaining block is disjoint from both (`hRA`, `hRB`).

## What this file proves (0 axioms, 0 sorries)

* `partitionEnergy_prod_refinement_gain_of_partition` — the sharp 2×2 whole-partition
  energy gain with the six freshness hypotheses **replaced** by the partition model
  (nonempty disjoint cells tiling two disjoint coarse blocks fresh against `R`).
* `partitionEnergy_prod_gain_eps4_of_partition` — the same replacement for the AFKS-consumable
  `ε⁴` floor `partitionEnergy_prod_gain_eps4`, the form the iteration-count engine consumes.

Both are thin corollaries: obtain the six `∉` from `freshness_of_partition`, then apply the
verified base lemma.  This strips the file's frontier from "six freshness side-conditions"
down to "the analytic size floors `|A₁| ≥ ε|A|`, `|B₁| ≥ ε|B|`, `d ≥ ε`", which is exactly
what the equipartition-realizability programme still needs to witness.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Assembly
import Proofs.SzemerediRegularityOQ04Fresh

namespace Szemeredi.RegularityOQ04Fresh

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Sharp 2×2 whole-partition energy gain, freshness discharged from a partition model.**
Identical conclusion to `partitionEnergy_prod_refinement_gain`, but the six `∉`-freshness
side-conditions are replaced by the genuine partition data they follow from: the four cells
`A₁, A₂, B₁, B₂` are nonempty, `A₁ ∪ A₂ = A` and `B₁ ∪ B₂ = B` with disjoint halves, the two
coarse blocks satisfy `Disjoint A B`, and every remaining block `Q ∈ R` is disjoint from both
`A` and `B`.  Proof: `freshness_of_partition` supplies the six `∉` facts, which are fed to the
verified base gain lemma. -/
theorem partitionEnergy_prod_refinement_gain_of_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hAunion : A₁ ∪ A₂ = A) (hBunion : B₁ ∪ B₂ = B)
    (hdisjA : Disjoint A₁ A₂) (hdisjB : Disjoint B₁ B₂)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hAB : Disjoint A B)
    (hRA : ∀ Q ∈ R, Disjoint Q A) (hRB : ∀ Q ∈ R, Disjoint Q B)
    (d : ℚ) (hd : 0 ≤ d)
    (hdev : d ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    partitionEnergy G (insert A (insert B R)) +
        (↑A₁.card : ℚ) * ↑B₁.card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
      partitionEnergy G
        (insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))) := by
  obtain ⟨hAins, hBR, hA₁ins, hA₂ins, hB₁ins, hB₂R⟩ :=
    freshness_of_partition hAunion hBunion hA₁ hA₂ hB₁ hB₂ hdisjA hdisjB hAB hRA hRB
  exact partitionEnergy_prod_refinement_gain G R A B A₁ A₂ B₁ B₂
    hAunion hBunion hdisjA hdisjB hAins hBR hA₁ins hA₂ins hB₁ins hB₂R d hd hdev

/-- **AFKS-consumable `ε⁴` floor, freshness discharged from a partition model.**  Identical
conclusion to `partitionEnergy_prod_gain_eps4` (the sharp partition-level `ε⁴·|A||B|/n²` jump
the iteration-count engine consumes), with the six `∉`-freshness hypotheses replaced by the
partition model.  The remaining hypotheses are exactly the analytic size floors
(`ε·|A| ≤ |A₁|`, `ε·|B| ≤ |B₁|`, `ε ≤ |d(A₁,B₁) − d(A,B)|`) — the genuine content the
equipartition-realizability step must still witness.  Proof: discharge the six `∉` via
`freshness_of_partition`, then apply the verified base floor lemma. -/
theorem partitionEnergy_prod_gain_eps4_of_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset (Finset V)) (A B A₁ A₂ B₁ B₂ : Finset V)
    (hAunion : A₁ ∪ A₂ = A) (hBunion : B₁ ∪ B₂ = B)
    (hdisjA : Disjoint A₁ A₂) (hdisjB : Disjoint B₁ B₂)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hAB : Disjoint A B)
    (hRA : ∀ Q ∈ R, Disjoint Q A) (hRB : ∀ Q ∈ R, Disjoint Q B)
    (eps : ℚ) (hε : 0 ≤ eps)
    (hcardA : eps * A.card ≤ (A₁.card : ℚ)) (hcardB : eps * B.card ≤ (B₁.card : ℚ))
    (hdev : eps ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B|) :
    partitionEnergy G (insert A (insert B R)) +
        eps ^ 4 * (↑A.card * ↑B.card) / (Fintype.card V : ℚ) ^ 2 ≤
      partitionEnergy G
        (insert A₁ (insert A₂ (insert B₁ (insert B₂ R)))) := by
  obtain ⟨hAins, hBR, hA₁ins, hA₂ins, hB₁ins, hB₂R⟩ :=
    freshness_of_partition hAunion hBunion hA₁ hA₂ hB₁ hB₂ hdisjA hdisjB hAB hRA hRB
  exact partitionEnergy_prod_gain_eps4 G R A B A₁ A₂ B₁ B₂
    hAunion hBunion hdisjA hdisjB hAins hBR hA₁ins hA₂ins hB₁ins hB₂R
    eps hε hcardA hcardB hdev

end Szemeredi.RegularityOQ04Fresh
