/-
  Szemeredi Core Definitions

  Shared definitions and basic lemmas for the Szemeredi regularity pipeline.
  This module is imported by both SzemerediRegularity.lean (proof machinery)
  and SzemerediCounting.lean (counting/removal lemmas), preventing definition
  drift across the pipeline.

  Definitions:
  - edgeDensity: edge density between two vertex subsets
  - IsEpsilonRegular: epsilon-regularity of a pair
  - IsRegularPartition: epsilon-regular partition
  - partitionEnergy: energy of a partition

  Basic lemmas:
  - edgeDensity_nonneg, edgeDensity_le_one
  - partitionEnergy_nonneg

  Szemeredi (1975), Komlos-Simonovits (1996)
-/
import Mathlib

namespace Szemeredi.Core

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edge density between two disjoint vertex subsets in a simple graph.
    d(A,B) = |E(A,B)| / (|A| * |B|). -/
noncomputable def edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℚ :=
  if h : (A.card : ℚ) * B.card = 0 then 0
  else ((A.product B).filter (fun p => G.Adj p.1 p.2)).card / (A.card * B.card)

/-- A pair (A, B) of vertex subsets is epsilon-regular if for every
    A' ⊆ A, B' ⊆ B with |A'| >= eps|A| and |B'| >= eps|B|, the edge
    density d(A', B') is within eps of d(A, B). -/
def IsEpsilonRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Prop :=
  ∀ A' B' : Finset V,
    A' ⊆ A → B' ⊆ B →
    (A'.card : ℚ) ≥ eps * A.card →
    (B'.card : ℚ) ≥ eps * B.card →
    |edgeDensity G A' B' - edgeDensity G A B| ≤ eps

/-- An equipartition is epsilon-regular if at most epsilon * C(k,2) pairs
    are not epsilon-regular. -/
def IsRegularPartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) : Prop :=
  -- All parts have approximately equal size (equitable)
  (∀ P Q : Finset V, P ∈ parts → Q ∈ parts → (P.card : ℤ) - Q.card ≤ 1) ∧
  -- At most eps * C(k,2) pairs are irregular
  ((parts.product parts).filter (fun pq =>
    pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card ≤
    eps * (parts.card * (parts.card - 1))

/-- The size-weighted energy of a partition:
    q(P) = Σ_{i,j} (|Pᵢ|·|Pⱼ| / n²) · d(Pᵢ,Pⱼ)²
    where n = |V|. Energy lies in [0,1] for valid partitions and is
    monotone under refinement (splitting a part never decreases energy).
    This is the standard definition from Komlós-Simonovits (1996). -/
noncomputable def partitionEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : ℚ :=
  let n := (Fintype.card V : ℚ)
  if n = 0 then 0
  else (parts.product parts).sum (fun pq =>
    (pq.1.card : ℚ) * pq.2.card / n ^ 2 * (edgeDensity G pq.1 pq.2) ^ 2)

/-- Edge density is non-negative. -/
theorem edgeDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : 0 ≤ edgeDensity G A B := by
  unfold edgeDensity
  split_ifs
  · exact le_refl 0
  · positivity

/-- Edge density is at most 1. -/
theorem edgeDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : edgeDensity G A B ≤ 1 := by
  unfold edgeDensity
  split_ifs with h
  · exact zero_le_one
  · have hne : (A.card : ℚ) * B.card ≠ 0 := h
    have hpos : (0 : ℚ) < (A.card : ℚ) * B.card :=
      lt_of_le_of_ne (by positivity) hne.symm
    rw [div_le_one hpos]
    have h1 : {p ∈ A.product B | G.Adj p.1 p.2}.card ≤ A.card * B.card := by
      calc {p ∈ A.product B | G.Adj p.1 p.2}.card
          ≤ (A.product B).card := Finset.card_filter_le _ _
        _ = A.card * B.card := Finset.card_product A B
    exact_mod_cast h1

/-- Partition energy is non-negative. -/
theorem partitionEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    0 ≤ partitionEnergy G parts := by
  unfold partitionEnergy
  simp only
  split_ifs with h
  · exact le_refl 0
  · apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg
    · apply div_nonneg
      · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact sq_nonneg _
    · exact sq_nonneg _

end Szemeredi.Core
