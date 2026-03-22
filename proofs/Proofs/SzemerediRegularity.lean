/-
  Szemeredi Regularity Lemma

  Every large enough graph can be partitioned into a bounded number of
  parts such that edges between most pairs behave pseudo-randomly.
  The fundamental structural result in graph theory.

  Core definitions (edgeDensity, IsEpsilonRegular, IsRegularPartition,
  partitionEnergy) and basic lemmas live in SzemerediCore.lean.
  This file contains the proof machinery:
  - Density-squared convexity (Cauchy-Schwarz ingredient)
  - Energy increment step
  - Partition energy upper bound
  - Regularity lemma (main result)

  Szemeredi (1975), Komlos-Simonovits (1996)
-/
import Mathlib
import Proofs.SzemerediCore

namespace Szemeredi.Regularity

-- Re-export Core definitions so that downstream code referencing
-- Szemeredi.Regularity.edgeDensity etc. continues to compile.
export Szemeredi.Core (edgeDensity IsEpsilonRegular IsRegularPartition
  partitionEnergy edgeDensity_nonneg edgeDensity_le_one partitionEnergy_nonneg)

open Classical Szemeredi.Core

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: PARTITION ENERGY AND ENERGY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: |A| * |B| * edgeDensity(A,B) = edge count (as Q). -/
private theorem card_mul_edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (A.card : ℚ) * B.card * edgeDensity G A B =
    ↑((A.product B).filter (fun p => G.Adj p.1 p.2)).card := by
  unfold edgeDensity
  split_ifs with h
  · -- A.card * B.card = 0 implies A or B is empty, so product is empty
    rw [mul_zero]; symm
    rw [Nat.cast_eq_zero, Finset.card_eq_zero]
    rcases mul_eq_zero.mp h with ha | hb
    · have hA := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp ha)
      ext x; simp [hA, Finset.not_mem_empty]
    · have hB := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hb)
      ext x; simp [Finset.product, hB, Finset.not_mem_empty]
  · -- Non-zero case: n*m * (e/(n*m)) = e
    have hne : (↑A.card : ℚ) * ↑B.card ≠ 0 := h
    rw [mul_div_cancel₀ _ hne]

/-- Edge count additivity: for disjoint A1, A2, edge counts to B add. -/
private theorem edge_count_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂) :
    (((A₁ ∪ A₂).product B).filter (fun p => G.Adj p.1 p.2)).card =
    ((A₁.product B).filter (fun p => G.Adj p.1 p.2)).card +
    ((A₂.product B).filter (fun p => G.Adj p.1 p.2)).card := by
  -- Product distributes over union
  have h_prod : (A₁ ∪ A₂).product B = A₁.product B ∪ A₂.product B := by
    ext ⟨a, b⟩
    constructor
    · intro h
      have hab := Finset.mem_product.mp h
      rcases Finset.mem_union.mp hab.1 with ha | ha
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr ⟨ha, hab.2⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr ⟨ha, hab.2⟩))
    · intro h
      rcases Finset.mem_union.mp h with hab | hab <;> {
        have := Finset.mem_product.mp hab
        exact Finset.mem_product.mpr ⟨Finset.mem_union.mpr (by tauto), this.2⟩ }
  rw [h_prod, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_filter_filter
  rw [Finset.disjoint_left]
  intro x h₁ h₂
  exact absurd (Finset.mem_product.mp h₂).1
    (Finset.disjoint_left.mp hA (Finset.mem_product.mp h₁).1)

/-- Convexity lemma: splitting a vertex set increases the sum of squared densities.
    If A = A1 U A2 (disjoint), then |A1|*d(A1,B)^2 + |A2|*d(A2,B)^2 >= |A|*d(A,B)^2.
    This is the Cauchy-Schwarz ingredient for the energy increment. -/
theorem density_sq_convex (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂) :
    (A₁.card : ℚ) * (edgeDensity G A₁ B) ^ 2 +
    (A₂.card : ℚ) * (edgeDensity G A₂ B) ^ 2 ≥
    ((A₁.card + A₂.card) : ℚ) * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 := by
  -- Abbreviations
  set d₁ := edgeDensity G A₁ B
  set d₂ := edgeDensity G A₂ B
  set d := edgeDensity G (A₁ ∪ A₂) B
  set n₁ : ℚ := ↑A₁.card
  set n₂ : ℚ := ↑A₂.card
  -- Non-negativity
  have hn₁ : 0 ≤ n₁ := Nat.cast_nonneg _
  have hn₂ : 0 ≤ n₂ := Nat.cast_nonneg _
  -- The weighted average property: (n1+n2)*m*d = n1*m*d1 + n2*m*d2
  have hcard : (↑(A₁ ∪ A₂).card : ℚ) = n₁ + n₂ := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  have havg : (n₁ + n₂) * ↑B.card * d = n₁ * ↑B.card * d₁ + n₂ * ↑B.card * d₂ := by
    have h₁ := card_mul_edgeDensity G A₁ B
    have h₂ := card_mul_edgeDensity G A₂ B
    have h₃ := card_mul_edgeDensity G (A₁ ∪ A₂) B
    rw [hcard] at h₃
    have he : (↑(((A₁ ∪ A₂).product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) =
      ↑((A₁.product B).filter (fun p => G.Adj p.1 p.2)).card +
      ↑((A₂.product B).filter (fun p => G.Adj p.1 p.2)).card := by
      exact_mod_cast edge_count_union G A₁ A₂ B hA
    linarith
  -- Case 1: B empty (card = 0) -- all terms zero
  by_cases hB : (B.card : ℚ) = 0
  · have h0 : ∀ (S : Finset V), edgeDensity G S B = 0 := by
      intro S; unfold edgeDensity
      rw [dif_pos (show (↑S.card : ℚ) * ↑B.card = 0 from by rw [hB, mul_zero])]
    -- Unfold set abbreviations so simp can apply h0
    have hd₁0 : d₁ = 0 := h0 A₁
    have hd₂0 : d₂ = 0 := h0 A₂
    have hd0 : d = 0 := h0 (A₁ ∪ A₂)
    rw [hd₁0, hd₂0, hd0]; simp
  -- Case 2: n1 + n2 = 0 -- both sets empty, all terms zero
  by_cases hnn : n₁ + n₂ = 0
  · have h1 : n₁ = 0 := le_antisymm (by linarith) hn₁
    have h2 : n₂ = 0 := le_antisymm (by linarith) hn₂
    simp [h1, h2]
  -- Main case: B nonempty, n1 + n2 > 0
  · have hnn_pos : (0 : ℚ) < n₁ + n₂ :=
      lt_of_le_of_ne (by linarith) (Ne.symm hnn)
    -- Derive weighted average: (n1+n2)*d = n1*d1 + n2*d2 (cancel B.card)
    have hd_avg : (n₁ + n₂) * d = n₁ * d₁ + n₂ * d₂ := by
      have hB_ne : (B.card : ℚ) ≠ 0 := hB
      exact mul_left_cancel₀ hB_ne (show ↑B.card * ((n₁ + n₂) * d) =
        ↑B.card * (n₁ * d₁ + n₂ * d₂) from by nlinarith)
    -- Rewrite d using the weighted average
    have hd_eq : d = (n₁ * d₁ + n₂ * d₂) / (n₁ + n₂) := by
      rw [eq_div_iff (ne_of_gt hnn_pos)]; linarith [hd_avg]
    -- Goal: n1*d1^2 + n2*d2^2 >= (n1+n2)*d^2
    rw [ge_iff_le, ← sub_nonneg, hd_eq]
    -- The difference equals n1*n2*(d1-d2)^2/(n1+n2) >= 0
    have key : n₁ * d₁ ^ 2 + n₂ * d₂ ^ 2 -
        (n₁ + n₂) * ((n₁ * d₁ + n₂ * d₂) / (n₁ + n₂)) ^ 2 =
        n₁ * n₂ * (d₁ - d₂) ^ 2 / (n₁ + n₂) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (mul_nonneg (mul_nonneg hn₁ hn₂) (sq_nonneg _)) (le_of_lt hnn_pos)

/-- From a non-ε-regular partition with at least 2 parts, extract a specific
    irregular pair. The partition must fail the irregularity count bound
    (second condition of IsRegularPartition). -/
theorem exists_irregular_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (parts : Finset (Finset V))
    (hmany : ((parts.product parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card >
      eps * (parts.card * (parts.card - 1))) :
    ∃ P Q : Finset V, P ∈ parts ∧ Q ∈ parts ∧ P ≠ Q ∧
      ¬IsEpsilonRegular G eps P Q := by
  have hne : ((parts.product parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h, Finset.card_empty] at hmany; push_cast at hmany
    have hprod : (0 : ℚ) ≤ ↑parts.card * (↑parts.card - 1) := by
      rcases Nat.eq_zero_or_pos parts.card with hk | hk
      · simp [hk]
      · have h1 : (1 : ℚ) ≤ ↑parts.card := by exact_mod_cast hk
        exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h1)
    linarith [mul_nonneg (le_of_lt heps) hprod]
  obtain ⟨⟨P, Q⟩, hmem⟩ := hne
  have hf := Finset.mem_filter.mp hmem
  have hp := Finset.mem_product.mp hf.1
  exact ⟨P, Q, hp.1, hp.2, hf.2.1, hf.2.2⟩

/-- Algebraic identity for energy splitting: when d is the weighted
    average of d₁ and d₂ (weights n₁, n₂), the excess squared-density
    equals n₁n₂(d₁-d₂)²/(n₁+n₂). This is the key formula for the
    energy increment step. -/
theorem split_energy_identity (n₁ n₂ d₁ d₂ : ℚ)
    (hn : n₁ + n₂ ≠ 0) :
    n₁ * d₁ ^ 2 + n₂ * d₂ ^ 2 -
    (n₁ + n₂) * ((n₁ * d₁ + n₂ * d₂) / (n₁ + n₂)) ^ 2 =
    n₁ * n₂ * (d₁ - d₂) ^ 2 / (n₁ + n₂) := by
  field_simp
  ring

/-- The energy excess from splitting is non-negative (Cauchy-Schwarz). -/
theorem split_energy_excess_nonneg (n₁ n₂ d₁ d₂ : ℚ)
    (hn₁ : 0 ≤ n₁) (hn₂ : 0 ≤ n₂) (hn : n₁ + n₂ ≠ 0) :
    n₁ * d₁ ^ 2 + n₂ * d₂ ^ 2 ≥
    (n₁ + n₂) * ((n₁ * d₁ + n₂ * d₂) / (n₁ + n₂)) ^ 2 := by
  rw [ge_iff_le, ← sub_nonneg, split_energy_identity n₁ n₂ d₁ d₂ hn]
  exact div_nonneg (mul_nonneg (mul_nonneg hn₁ hn₂) (sq_nonneg _))
    (le_of_lt (lt_of_le_of_ne (by linarith) (Ne.symm hn)))

/-- Quantitative lower bound: if |d₁ - d₂| ≥ δ, the energy excess
    is at least n₁n₂δ²/(n₁+n₂). -/
theorem split_energy_excess_bound (n₁ n₂ d₁ d₂ δ : ℚ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hδ : 0 ≤ δ)
    (hdev : |d₁ - d₂| ≥ δ) :
    n₁ * n₂ * (d₁ - d₂) ^ 2 / (n₁ + n₂) ≥
    n₁ * n₂ * δ ^ 2 / (n₁ + n₂) := by
  have hsq : δ ^ 2 ≤ (d₁ - d₂) ^ 2 := by
    calc δ ^ 2 ≤ |d₁ - d₂| ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg (d₁ - d₂)]) hdev
      _ = (d₁ - d₂) ^ 2 := sq_abs _
  rw [ge_iff_le]
  have hnn_pos : (0 : ℚ) < n₁ + n₂ := by linarith
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsq (mul_nonneg (le_of_lt hn₁) (le_of_lt hn₂)))
    (le_of_lt hnn_pos)

/-- Unweighted squared-density convexity: splitting a vertex set into two
    disjoint pieces never decreases the unweighted sum of squared densities.
    d(A₁,B)² + d(A₂,B)² ≥ d(A₁∪A₂,B)², without size weighting.

    This follows from the algebraic identity:
      x² + y² ≥ (n₁x + n₂y)²/(n₁+n₂)²
    where x = e₁/n₁, y = e₂/n₂ are edge-count-to-size ratios.
    The difference equals (xn₂ - yn₁)²/(n₁+n₂)² + 2n₁n₂(x²+y²-xy)/(n₁+n₂)² ≥ 0. -/
private theorem unweighted_density_sq_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂) :
    (edgeDensity G A₁ B) ^ 2 + (edgeDensity G A₂ B) ^ 2 ≥
    (edgeDensity G (A₁ ∪ A₂) B) ^ 2 := by
  -- When both A₁ and A₂ are nonempty, use density_sq_convex and drop coefficients
  by_cases h₁ : A₁.card = 0
  · have hA₁ : A₁ = ∅ := Finset.card_eq_zero.mp h₁
    simp only [hA₁, Finset.empty_union]
    linarith [sq_nonneg (edgeDensity G ∅ B)]
  by_cases h₂ : A₂.card = 0
  · have hA₂ : A₂ = ∅ := Finset.card_eq_zero.mp h₂
    simp only [hA₂, Finset.union_empty]
    linarith [sq_nonneg (edgeDensity G ∅ B)]
  -- Both nonempty: use weighted convexity and the fact that n₁, n₂ ≥ 1
  have hn₁ : (0 : ℚ) < A₁.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₁)
  have hn₂ : (0 : ℚ) < A₂.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h₂)
  have hconv := density_sq_convex G A₁ A₂ B hA
  -- From n₁ * d₁² + n₂ * d₂² ≥ (n₁ + n₂) * d², derive d₁² + d₂² ≥ d²
  -- since n₁ * d₁² ≤ n₁ * d₁² and 1 ≤ n₁ (as natural), we get d₁² ≤ n₁ * d₁²
  -- So d₁² + d₂² ≤ n₁ * d₁² + n₂ * d₂² ≥ (n₁+n₂) * d² ≥ d²
  calc (edgeDensity G A₁ B) ^ 2 + (edgeDensity G A₂ B) ^ 2
      ≤ ↑A₁.card * (edgeDensity G A₁ B) ^ 2 +
        ↑A₂.card * (edgeDensity G A₂ B) ^ 2 := by
        have h1 : (edgeDensity G A₁ B) ^ 2 ≤
            ↑A₁.card * (edgeDensity G A₁ B) ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) (by linarith)
        have h2 : (edgeDensity G A₂ B) ^ 2 ≤
            ↑A₂.card * (edgeDensity G A₂ B) ^ 2 :=
          le_mul_of_one_le_left (sq_nonneg _) (by linarith)
        linarith
    _ ≥ (↑A₁.card + ↑A₂.card) * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 := hconv
    _ ≥ 1 * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith
    _ = (edgeDensity G (A₁ ∪ A₂) B) ^ 2 := one_mul _

/-- Cardinality bound for single-part split: splitting one part in a k-part
    collection gives at most k+1 parts, which is ≤ k * 2^k for k ≥ 2. -/
private theorem card_split_le_bound (k : ℕ) (hk : 2 ≤ k) :
    k + 1 ≤ k * 2 ^ k := by
  calc k + 1 ≤ k + k := by omega
    _ = 2 * k := by ring
    _ ≤ 2 ^ k * k := by
        apply Nat.mul_le_mul_right
        exact Nat.one_le_two_pow.trans (Nat.pow_le_pow_right (by omega) hk)
    _ = k * 2 ^ k := by ring

/-- Energy increment step: if a partition has too many irregular pairs,
    refinement increases energy by at least eps^5. This is the key
    technical lemma driving the regularity proof.

    PROOF STATUS: Decomposed into cases. The core difficulty is that our
    energy definition normalizes by 1/k² (unweighted), while the standard
    Komlos-Simonovits argument uses size-weighted energy Σ(nᵢnⱼ/n²)d²ᵢⱼ.
    For equitable partitions these agree, but the refinement step produces
    non-equitable parts, requiring careful accounting of the normalization
    change vs. density-squared gain. -/
theorem energy_increment_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (parts : Finset (Finset V))
    (hirr : ¬IsRegularPartition G eps parts) :
    ∃ parts' : Finset (Finset V),
      partitionEnergy G parts' ≥ partitionEnergy G parts + eps ^ 5 ∧
      parts'.card ≤ parts.card * 2 ^ parts.card := by
  -- Case split: is the partition equitable?
  by_cases h_equit : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts →
      (P.card : ℤ) - Q.card ≤ 1
  · -- CASE A: Equitable but not regular → irregularity bound fails.
    -- Since the partition satisfies equitability but ¬IsRegularPartition,
    -- the irregularity count must exceed eps * k*(k-1).
    have h_irreg : ¬(((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card ≤
        eps * (↑parts.card * (↑parts.card - 1))) := fun h => hirr ⟨h_equit, h⟩
    rw [not_le] at h_irreg
    -- Extract an irregular pair and its witnesses
    obtain ⟨P, Q, hP, hQ, hne, hirr_pair⟩ :=
      exists_irregular_pair G eps heps parts h_irreg
    obtain ⟨A', B', hA'P, hB'Q, hcA', hcB', hdev⟩ :=
      exists_irregular_witness G eps P Q hirr_pair
    -- CONSTRUCTION: split P into {A', P \ A'}, keep other parts.
    -- The irregular witnesses ensure density deviation > eps,
    -- which drives the energy increase via split_energy_excess_bound.
    --
    -- KEY TECHNICAL CHALLENGE: Our partitionEnergy normalizes by 1/k².
    -- Splitting P into 2 pieces changes k to k+1, diluting the
    -- normalization. The proof must show the density-squared gain
    -- from the irregular pair outweighs this dilution.
    -- For equitable partitions with the standard size-weighted energy,
    -- the eps^5 bound follows directly. With our 1/k² normalization,
    -- the argument requires that eps * k(k-1) irregular pairs each
    -- contribute enough gain to compensate for the (k+1)²/k² factor.
    sorry
  · -- CASE B: Not equitable.
    -- There exist parts P, Q with |P| - |Q| > 1.
    -- Splitting the larger part or re-balancing increases energy.
    sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART III: REGULARITY LEMMA (MAIN RESULT)
-- ═══════════════════════════════════════════════════════════════════

/-- Partition energy is bounded above by 1. -/
theorem partitionEnergy_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q →
      Disjoint P Q) :
    partitionEnergy G parts ≤ 1 := by
  unfold partitionEnergy
  split_ifs with h
  · exact zero_le_one
  · -- Each d(P,Q)^2 <= 1, and there are k^2 terms, so Sigma d^2 <= k^2
    -- Therefore (1/k^2) * Sigma d^2 <= (1/k^2) * k^2 = 1
    have hk2_ne : (↑(parts.card ^ 2) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero 2 h)
    have hsum : (parts.product parts).sum (fun pq => (edgeDensity G pq.1 pq.2) ^ 2)
        ≤ ↑(parts.card ^ 2) := by
      calc (parts.product parts).sum (fun pq => (edgeDensity G pq.1 pq.2) ^ 2)
          ≤ (parts.product parts).sum (fun _ => (1 : ℚ)) := by
            apply Finset.sum_le_sum; intro x _
            have h1 := edgeDensity_nonneg G x.1 x.2
            have h2 := edgeDensity_le_one G x.1 x.2
            have : (edgeDensity G x.1 x.2) ^ 2 ≤ edgeDensity G x.1 x.2 := by
              rw [sq]; exact mul_le_of_le_one_right h1 h2
            linarith
        _ = ↑(parts.product parts).card := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = ↑(parts.card ^ 2) := by
            congr 1
            exact (Finset.card_product parts parts).trans (by ring)
    calc (1 : ℚ) / ↑(parts.card ^ 2) *
          (parts.product parts).sum (fun pq => (edgeDensity G pq.1 pq.2) ^ 2)
        ≤ 1 / ↑(parts.card ^ 2) * ↑(parts.card ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by field_simp

/-- The energy of a regular partition is finite-step achievable: since
    energy lies in [0,1] and each increment adds at least eps^5,
    we need at most ceil(1/eps^5) iterations. -/
theorem max_iterations (eps : ℚ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ e : ℚ, 0 ≤ e → e ≤ 1 → e + N * eps ^ 5 > 1 := by
  -- By the Archimedean property, find N > 1/eps^5.
  -- Then N * eps^5 > 1, and with e >= 0 we get e + N * eps^5 > 1.
  have heps5 : (0 : ℚ) < eps ^ 5 := pow_pos heps 5
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / eps ^ 5)
  exact ⟨N, fun e he0 _ => by linarith [((div_lt_iff₀ heps5).mp hN)]⟩

/-- Extract witnesses from a non-ε-regular pair: there exist large subsets
    whose density deviates from the pair density by more than ε. -/
theorem exists_irregular_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (hirr : ¬IsEpsilonRegular G eps A B) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      (A'.card : ℚ) ≥ eps * A.card ∧
      (B'.card : ℚ) ≥ eps * B.card ∧
      |edgeDensity G A' B' - edgeDensity G A B| > eps := by
  unfold IsEpsilonRegular at hirr
  push_neg at hirr
  obtain ⟨A', B', hA', hB', hcA', hcB', hd⟩ := hirr
  exact ⟨A', B', hA', hB', hcA', hcB', hd⟩

/-- **Szemeredi Regularity Lemma**: For every epsilon > 0, every
    sufficiently large graph admits an epsilon-regular partition into
    at most M(epsilon) parts.

    The proof iterates: start with an arbitrary equipartition. If not
    regular, refine to increase energy by eps^5. Since energy in [0,1],
    this terminates after at most eps^{-5} steps.

    NOTE: This formulation is vacuously satisfied by the one-part partition
    {V} since it has no distinct pairs. The standard formulation requires
    a lower bound parts.card ≥ m₀ (see regularity_lemma_strong). -/
theorem regularity_lemma (eps : ℚ) (heps : 0 < eps) :
    ∃ M : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      Fintype.card V ≥ M →
      ∃ parts : Finset (Finset V), IsRegularPartition G eps parts ∧
        parts.card ≤ M := by
  -- The one-part partition {Finset.univ} is vacuously ε-regular:
  -- no distinct pairs exist, so the irregularity count is 0.
  refine ⟨1, fun V _ _ G _ _ => ⟨{Finset.univ}, ⟨?_, ?_⟩, by simp⟩⟩
  · -- Equitable: single part, P = Q, difference is 0 ≤ 1
    intro P Q hP hQ
    rw [Finset.mem_singleton.mp hP, Finset.mem_singleton.mp hQ]; simp
  · -- All pairs (P,Q) in {univ}×{univ} have P = Q, so filter for P≠Q is empty
    have h : (({Finset.univ} : Finset (Finset V)).product {Finset.univ}).filter
        (fun pq => pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2) = ∅ := by
      ext ⟨a, b⟩
      constructor
      · intro hmem
        have hf := Finset.mem_filter.mp hmem
        have hp := Finset.mem_product.mp hf.1
        have ha : a = Finset.univ := Finset.mem_singleton.mp hp.1
        have hb : b = Finset.univ := Finset.mem_singleton.mp hp.2
        subst ha; subst hb
        exact absurd rfl hf.2.1
      · intro hmem; exact absurd hmem (Finset.notMem_empty _)
    rw [h, Finset.card_empty, Nat.cast_zero]
    simp [Finset.card_singleton]

-- ═══════════════════════════════════════════════════════════════════
-- BRIDGE TO MATHLIB'S SZEMEREDI REGULARITY
-- ═══════════════════════════════════════════════════════════════════

/-- Our edge density agrees with Mathlib's SimpleGraph.edgeDensity. -/
private theorem edgeDensity_eq_mathlib (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    edgeDensity G A B = G.edgeDensity A B := by
  unfold edgeDensity
  simp only [SimpleGraph.edgeDensity, Rel.edgeDensity, Rel.interedges]
  split_ifs with h
  · -- Denominator is 0: both sides are 0
    have h0 : A.card * B.card = 0 := by
      cases mul_eq_zero.mp h with
      | inl ha => exact mul_eq_zero.mpr (Or.inl (Nat.cast_eq_zero.mp ha))
      | inr hb => exact mul_eq_zero.mpr (Or.inr (Nat.cast_eq_zero.mp hb))
    rw [show (↑A.card : ℚ) * ↑B.card = 0 from h, div_zero]
  · -- Non-zero: same rational expression
    rfl

/-- Mathlib's pairwise uniformity (strict <) implies our ε-regularity (≤). -/
private theorem mathlib_uniform_imp_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V)
    (h : G.IsUniform (↑eps : ℝ) A B) :
    IsEpsilonRegular G eps A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- The density comparison: |d(A',B') - d(A,B)| ≤ eps
  rw [edgeDensity_eq_mathlib, edgeDensity_eq_mathlib]
  -- Apply Mathlib's uniformity condition
  have hcA'_real : (↑A.card : ℝ) * ↑eps ≤ ↑A'.card := by
    have : (↑A.card : ℚ) * eps ≤ ↑A'.card := by linarith
    exact_mod_cast this
  have hcB'_real : (↑B.card : ℝ) * ↑eps ≤ ↑B'.card := by
    have : (↑B.card : ℚ) * eps ≤ ↑B'.card := by linarith
    exact_mod_cast this
  have hlt := h hA' hB' hcA'_real hcB'_real
  -- Convert strict < in ℝ to ≤ in ℚ
  have : |(↑(G.edgeDensity A' B') : ℝ) - ↑(G.edgeDensity A B)| < ↑eps := hlt
  rw [← Rat.cast_sub, ← Rat.cast_abs] at this
  exact_mod_cast le_of_lt this

/-- Equipartition in Mathlib's sense implies our equitability condition:
    all parts differ in size by at most 1. -/
private theorem equipartition_imp_equitable
    (P : Finpartition (Finset.univ : Finset V))
    (hequi : P.IsEquipartition) :
    ∀ A B : Finset V, A ∈ P.parts → B ∈ P.parts →
      (A.card : ℤ) - B.card ≤ 1 := by
  intro A B hA hB
  -- IsEquipartition unfolds to EquitableOn Finset.card:
  -- ∀ a ∈ ↑P.parts, ∀ b ∈ ↑P.parts, a.card ≤ b.card + 1
  have h := hequi (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hB)
  -- h : A.card ≤ B.card + 1 (in ℕ)
  omega

/-- The set of our irregular pairs is a subset of Mathlib's non-uniform pairs.
    This is because Mathlib uses strict < while we use ≤. -/
private theorem irregular_subset_nonuniform (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (P : Finpartition (Finset.univ : Finset V)) :
    ((P.parts.product P.parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card ≤
    (P.nonUniforms G (↑eps : ℝ)).card := by
  apply Finset.card_le_card
  intro ⟨A, B⟩ hmem
  have hf := Finset.mem_filter.mp hmem
  have hp := Finset.mem_product.mp hf.1
  -- Our pair is not ε-regular, so it's not ε-uniform (contrapositive)
  have hne := hf.2.1
  have hnreg := hf.2.2
  have hnunif : ¬G.IsUniform (↑eps : ℝ) A B :=
    fun hunif => hnreg (mathlib_uniform_imp_regular G eps A B hunif)
  -- Show membership in nonUniforms
  simp only [Finpartition.nonUniforms, Finset.mem_filter, Finset.mem_offDiag]
  exact ⟨⟨hp.1, hp.2, hne⟩, hnunif⟩

/-- **Szemeredi Regularity Lemma (Strong Form)**: For every epsilon > 0
    and m₀ ≥ 1, there exists M such that every graph on ≥ M vertices
    admits an ε-regular equipartition into k parts with m₀ ≤ k ≤ M.

    Proved by bridging to Mathlib's szemeredi_regularity theorem,
    which provides a complete formalization of the regularity lemma. -/
theorem regularity_lemma_strong (eps : ℚ) (heps : 0 < eps) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    ∃ M : ℕ, m₀ ≤ M ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        Fintype.card V ≥ M →
        ∃ parts : Finset (Finset V),
          IsRegularPartition G eps parts ∧
          m₀ ≤ parts.card ∧ parts.card ≤ M := by
  -- Use Mathlib's Szemeredi Regularity Lemma
  set M := max m₀ (SzemerediRegularity.bound (↑eps : ℝ) m₀) with hM_def
  refine ⟨M, le_max_left _ _, fun V _ _ G _ hV => ?_⟩
  -- Apply Mathlib's theorem with l = m₀
  have heps_real : (0 : ℝ) < (↑eps : ℝ) := by exact_mod_cast heps
  have hl : m₀ ≤ Fintype.card V :=
    le_trans (le_max_left _ _) hV
  obtain ⟨P, hequi, hle, hbound, hunif⟩ :=
    szemeredi_regularity G heps_real hl
  refine ⟨P.parts, ⟨?_, ?_⟩, hle, le_trans hbound (le_max_right _ _)⟩
  · -- Equitability: IsEquipartition → our equitability condition
    exact equipartition_imp_equitable P hequi
  · -- Irregularity count: IsUniform → at most eps * k*(k-1) irregular pairs
    -- Mathlib's IsUniform gives: nonUniforms.card ≤ k*(k-1) * eps (in ℝ)
    -- Our irregular pairs ⊆ Mathlib's non-uniform pairs
    have h_sub := irregular_subset_nonuniform G eps P
    -- Mathlib's uniformity bound
    have h_unif : (↑(P.nonUniforms G (↑eps : ℝ)).card : ℝ) ≤
        ↑(P.parts.card * (P.parts.card - 1)) * ↑eps := hunif
    -- Chain: our_count ≤ nonUniforms_count ≤ k*(k-1)*eps
    -- Work entirely in ℝ to avoid cast headaches, then cast back
    suffices h_real :
        (↑((P.parts.product P.parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card : ℝ) ≤
        (↑eps : ℝ) * ((↑P.parts.card : ℝ) * ((↑P.parts.card : ℝ) - 1)) by
      exact_mod_cast h_real
    -- In ℝ: our_count ≤ nonUniforms_count ≤ k*(k-1) * eps
    have h_sub_real : (↑((P.parts.product P.parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G eps pq.1 pq.2)).card : ℝ) ≤
        (↑(P.nonUniforms G (↑eps : ℝ)).card : ℝ) := by exact_mod_cast h_sub
    -- Mathlib bound: nonUniforms.card ≤ ↑(k*(k-1)) * eps
    -- Rewrite ↑(k*(k-1)) as ↑k * (↑k - 1) using k ≥ 1
    have h_k1 : 1 ≤ P.parts.card := le_trans hm₀ hle
    have h_cast_kk : (↑(P.parts.card * (P.parts.card - 1)) : ℝ) =
        (↑P.parts.card : ℝ) * ((↑P.parts.card : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub h_k1]; simp
    rw [h_cast_kk] at h_unif
    linarith

end Szemeredi.Regularity
