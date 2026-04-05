/-
  Aristotle targets for SzemerediCoreOQ01
  Energy increment step — Finset.sum packaging for refined partition.
  See SzemerediCoreOQ01.lean for the main formalization.

  Status: 1 sorry in energy_increment_step. This file exposes that sorry
  as a standalone Aristotle target, plus two preparatory helper lemmas.

  Context: energy_increment_step proves that refining an ε-irregular pair
  (A,B) in a partition to {A', A\A', B', B\B'} increases partition energy ≥ eps^6.
  All algebraic lemmas (sub4pair, deviation_identity, excess_lb) are proved.
  The remaining sorry packages these via Finset.sum_union decomposition.

  Aristotle targets (3):
  1. partitionEnergy_mono: energy is monotone under partition Finset superset
  2. partitionEnergy_term_nonneg: each sum term is nonneg (for monotonicity proof)
  3. energy_increment_packaging_ari: main sorry — the sum packaging step

  Key tools:
  - Finset.sum_le_sum_of_subset_of_nonneg (monotone subset sums)
  - Finset.product_subset_product (product monotone in both args)
  - sub4pair_energy_lower_bound (proved: 4-split ≥ 2-split energy)
  - four_subpair_excess_lb (proved: excess ≥ A₁*B₁*(d₁₁-d)²)
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediCoreOQ01

namespace Szemeredi.EnergyIncrement.Aristotle

open Classical Szemeredi.Core Szemeredi.EnergyIncrement

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: HELPER LEMMAS
-- ═══════════════════════════════════════════════════════════════════

/-- Each term in the partitionEnergy sum is non-negative.

    `|P| * |Q| / n² * d(P,Q)²` is a product of non-negative factors:
    - |P|, |Q| are Nat.cast so ≥ 0
    - n² > 0 (or = 0 and we don't care)
    - d(P,Q)² ≥ 0 by sq_nonneg -/
lemma partitionEnergy_term_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) :
    0 ≤ (P.card : ℚ) * Q.card / (Fintype.card V : ℚ) ^ 2 *
        (edgeDensity G P Q) ^ 2 := by
  apply mul_nonneg
  · apply div_nonneg _ (by positivity)
    apply mul_nonneg <;> exact Nat.cast_nonneg _
  · exact sq_nonneg _

/-- **partitionEnergy is monotone** under Finset superset.
    If P ⊆ Q (as Finset of Finset V), then:
      partitionEnergy G Q ≥ partitionEnergy G P

    Proof: P × P ⊆ Q × Q (by Finset.product_subset_product).
    Each term is non-negative (partitionEnergy_term_nonneg).
    Apply Finset.sum_le_sum_of_subset_of_nonneg. -/
lemma partitionEnergy_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset (Finset V)) (hPQ : P ⊆ Q) :
    partitionEnergy G Q ≥ partitionEnergy G P := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART II: MAIN ARISTOTLE TARGET
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy increment packaging** — main Aristotle target.

    Show that the refined partition `(parts\{A,B}) ∪ {A',A₂,B',B₂}`
    has energy ≥ energy(parts) + eps^6.

    Given context:
    - S = parts.erase B |>.erase A  (all parts except A and B)
    - T = {A', A₂, B', B₂} where A₂ = A\A', B₂ = B\B'
    - A'∪A₂ = A, B'∪B₂ = B (from hAu, hBu)
    - sub4pair: energy({A',A₂,B',B₂}) ≥ energy({A,B})  [proved lemma]
    - hcore: A'.card * B'.card * dev² > eps^6 * n²      [proved in main]
    - four_subpair_excess_lb: 4-term sum excess ≥ A₁B₁*(d₁₁-d)²  [proved]

    Proof strategy (Finset.sum_union decomposition):
    1. parts = S ∪ {A,B} (as Finset of Finset V, with S ∩ {A,B} = ∅)
    2. parts' = S ∪ T   (with S ∩ T = ∅)
    3. Expand via Finset.sum_union: energy = S×S + S×{A,B} + {A,B}×S + {A,B}×{A,B}
       and energy' = S×S + S×T + T×S + T×T
    4. S×S: identical
    5. S×T + T×S ≥ S×{A,B} + {A,B}×S: splitting A,B by density_sq_convex
    6. T×T ≥ {A,B}×{A,B} + eps^6: from sub4pair + four_subpair_excess_lb + hcore

    Connection to eps^6:
    four_subpair_excess_lb gives:
      Σᵢⱼ Aᵢ*Bⱼ*dᵢⱼ² - A*B*d² ≥ A'.card*B'.card*(d(A',B')-d(A,B))²
    And hcore gives: A'.card*B'.card*(d-d_AB)² > eps^6 * n²
    Together: Σᵢⱼ Aᵢ*Bⱼ*dᵢⱼ²/n² > A*B*d²/n² + eps^6
    Which is: (T×T block for cross-terms) > ({A}×{B} energy) + eps^6 -/
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
    -- Core quantitative bound: enough excess for eps^6
    -- (same as hcore in energy_increment_step: proved from irregularity + equipartition)
    (hcore : (A'.card : ℚ) * B'.card *
             (edgeDensity G A' B' - edgeDensity G A B) ^ 2 >
             eps ^ 6 * (Fintype.card V : ℚ) ^ 2) :
    let A₂ := A \ A'; let B₂ := B \ B'
    let S := (parts.erase B).erase A
    partitionEnergy G (S ∪ {A', A₂, B', B₂}) ≥
      partitionEnergy G parts + eps ^ 6 := by
  sorry

end Szemeredi.EnergyIncrement.Aristotle
