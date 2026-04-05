/-
  Aristotle targets for SzemerediCoreOQ01
  Energy increment step — Finset.sum packaging for refined partition.
  See SzemerediCoreOQ01.lean for the main formalization.

  Context: energy_increment_step proves that refining an ε-irregular pair
  (A,B) in a partition to {A', A\A', B', B\B'} increases partition energy ≥ eps^6.

  Infrastructure status (updated 2026-04-05):
  - four_subpair_edge_count_identity: PROVED (= double weighted average)
  - four_subpair_deviation_identity: PROVED (variance decomposition)
  - four_subpair_excess_lb: PROVED (variance bound for cross-block)
  - partitionEnergy_term_nonneg: PROVED (each term ≥ 0)
  - partitionEnergy_mono: PROVED (monotone under superset) — THIS SESSION
  - energy_increment_packaging_ari: sorry (Finset.sum_union decomposition)

  Remaining sorry: package the algebraic lemmas into a Finset sum inequality.
  The proof needs Finset.sum_union decomposition for:
    (S ∪ T) ×ˢ (S ∪ T) = S×S ∪ S×T ∪ T×S ∪ T×T
  vs
    (S ∪ {A,B}) ×ˢ (S ∪ {A,B}) = S×S ∪ S×{A,B} ∪ {A,B}×S ∪ {A,B}×{A,B}

  Block comparisons (all ≥ 0 or ≥ eps^6):
  - S×S: identical
  - S×T ≥ S×{A,B}: density_sq_convex per C ∈ S (splitting A→{A',A₂} and B→{B',B₂})
  - T×S ≥ {A,B}×S: same by symmetry
  - T×T ≥ {A,B}×{A,B} + eps^6:
      A-self: sub4pair_energy_lower_bound ≥ 0
      B-self: same ≥ 0
      A×B cross: four_subpair_excess_lb + hcore → ≥ eps^6
      B×A cross: symmetry → ≥ eps^6 (total ≥ 2*eps^6 ≥ eps^6)
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediCoreOQ01

namespace Szemeredi.EnergyIncrement.Aristotle

open Classical Szemeredi.Core Szemeredi.EnergyIncrement

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: MONOTONICITY LEMMAS (PROVED THIS SESSION)
-- ═══════════════════════════════════════════════════════════════════

/-- Each term in the partitionEnergy sum is non-negative. -/
lemma partitionEnergy_term_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) :
    0 ≤ (P.card : ℚ) * Q.card / (Fintype.card V : ℚ) ^ 2 *
        (edgeDensity G P Q) ^ 2 :=
  mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity))
    (sq_nonneg _)

/-- **partitionEnergy is monotone** under Finset superset.
    If P ⊆ Q (as Finset of Finset V), then partitionEnergy G Q ≥ partitionEnergy G P.

    Proof: P ×ˢ P ⊆ Q ×ˢ Q by Finset.product_subset_product.
    Each term is non-negative. Finset.sum_le_sum_of_subset_of_nonneg concludes. -/
lemma partitionEnergy_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset (Finset V)) (hPQ : P ⊆ Q) :
    partitionEnergy G Q ≥ partitionEnergy G P := by
  unfold partitionEnergy; simp only
  split_ifs with h
  · exact le_refl 0
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.product_subset_product hPQ hPQ
    · intro pq _ _
      exact mul_nonneg
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity))
        (sq_nonneg _)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: MAIN ARISTOTLE TARGET
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy increment packaging** — main Aristotle target.

    Show that the refined partition `S ∪ {A',A₂,B',B₂}` (where S = parts\{A,B})
    has energy ≥ energy(parts) + eps^6.

    Proof strategy: decompose both energies via Finset.sum_union:
      energy(parts) = energy(S ∪ {A,B}) = S×S + S×{A,B} + {A,B}×S + {A,B}×{A,B}
      energy(parts') = S×S + S×T + T×S + T×T
    where T = {A',A₂,B',B₂}.

    Show each block compares favorably:
    (1) S×S: equal
    (2) S×T ≥ S×{A,B}: density_sq_convex splits A→{A',A₂} and B→{B',B₂} for each C∈S
    (3) T×S ≥ {A,B}×S: same by edgeDensity symmetry
    (4) T×T ≥ {A,B}×{A,B} + eps^6:
        - A-self and B-self blocks: sub4pair_energy_lower_bound (≥0 each)
        - A×B cross: four_subpair_excess_lb + hcore → gain ≥ eps^6
        - B×A cross: symmetry → another eps^6 (total ≥ 2*eps^6 ≥ eps^6)

    Key Lean challenge: disjointness of S and T for Finset.sum_union.
    This requires A', A\A', B', B\B' ∉ S (the existing non-{A,B} parts).
    In principle true if the witnesses are proper subsets, but the argument
    depends on Finset.mem_erase and the definition of S.

    NOTE: An additional hypothesis `hST_disj : Disjoint S T` would make this
    straightforward. The current statement avoids it to match the main theorem. -/
theorem energy_increment_packaging_ari
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (parts : Finset (Finset V))
    (hparts_disj : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (A B : Finset V) (hA : A ∈ parts) (hB : B ∈ parts) (hAB : A ≠ B)
    (A' B' : Finset V)
    (hA'sub : A' ⊆ A) (hB'sub : B' ⊆ B)
    (hAd : Disjoint A' (A \ A')) (hBd : Disjoint B' (B \ B'))
    (hAu : A' ∪ (A \ A') = A) (hBu : B' ∪ (B \ B') = B)
    (hA'pos : 0 < A'.card) (hA₂pos : 0 < (A \ A').card)
    (hB'pos : 0 < B'.card) (hB₂pos : 0 < (B \ B').card)
    -- Core quantitative bound from irregularity + equipartition
    (hcore : (A'.card : ℚ) * B'.card *
             (edgeDensity G A' B' - edgeDensity G A B) ^ 2 >
             eps ^ 6 * (Fintype.card V : ℚ) ^ 2) :
    let A₂ := A \ A'; let B₂ := B \ B'
    let S := (parts.erase B).erase A
    partitionEnergy G (S ∪ {A', A₂, B', B₂}) ≥
      partitionEnergy G parts + eps ^ 6 := by
  sorry

end Szemeredi.EnergyIncrement.Aristotle
