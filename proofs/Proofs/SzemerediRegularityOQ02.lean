/-
# Szemerédi Regularity: Frieze-Kannan Weak Regularity Comparison

OQ-02 follow-up to szemeredi-regularity.

This file formalizes the **Frieze-Kannan (FK) Weak Regularity Lemma** and its
comparison with Szemerédi's (full) Regularity Lemma.

## Key Comparison

| Property        | Szemerédi                    | Frieze-Kannan                |
|-----------------|------------------------------|------------------------------|
| Parts count     | ≤ tower(1/ε) [stepBound^k]  | ≤ 4^(1/ε²) [singly exp.]    |
| Guarantee       | ε-regular: each pair uniform | ε-cut-approx: global cut norm|
| Strength        | Stronger                     | Weaker                       |

**Central result proved here**:
  Every ε-regular partition is a 2ε-cut-approximation (Szemerédi ⟹ FK).

This confirms that Szemerédi's stronger ε-regularity guarantee implies FK's weaker
cut-norm approximation. The converse fails: a cut-norm approximation need not be ε-regular.

## Main Results

- `IsCutApproximation` : FK's cut norm approximation property
- `pair_cut_error_bound` : single ε-regular pair ⟹ cut error ≤ 2ε|P||Q|
- `edge_count_partition_sum` : e(A,B) = Σᵢⱼ e(A∩Pᵢ, B∩Pⱼ) for partitions
- `parts_product_sum_eq_card_sq` : Σᵢⱼ |Pᵢ||Pⱼ| = n² for partitions of V
- `szemeredi_implies_fk` : ε-regular partition ⟹ 2ε-cut-approximation
- `sz_stepBound_ge_power` : stepBound n = n·4^n ≥ 4^n [Szemerédi's tower overhead]
- `sz_two_steps_tower` : 2-step bound ≥ 4^(4^n) [tower growth confirmed]
- `fk_bound_vs_szemeredi` : FK bound 4^⌈1/ε²⌉ vs Szemerédi's tower (explicit instance)

## Tags
graph-theory, combinatorics, szemeredi, regularity, frieze-kannan, cut-norm
-/

import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity

namespace SzemerediFKComparison

open Szemeredi.Core Szemeredi.Regularity Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: FK Cut Approximation Definition
-- ═══════════════════════════════════════════════════════════════════

/-- The **Frieze-Kannan cut approximation** property: a partition `parts` is an
    ε-cut-approximation of G if for every A, B ⊆ V, the actual edge count e(A,B)
    is within ε·n² of the "predicted" count Σᵢⱼ d(Pᵢ,Pⱼ)·|A∩Pᵢ|·|B∩Pⱼ|.

    This is the discrete version of ‖W_G - W_P‖_□ ≤ ε (graphon cut distance).
    Frieze-Kannan (1999) proved this holds with ≤ 4^(1/ε²) parts. -/
def IsCutApproximation (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (parts : Finset (Finset V)) : Prop :=
  ∀ A B : Finset V,
    |(((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) -
      (parts.product parts).sum (fun pq =>
        edgeDensity G pq.1 pq.2 * (A ∩ pq.1).card * (B ∩ pq.2).card)| ≤
    eps * (Fintype.card V : ℚ) ^ 2

-- ═══════════════════════════════════════════════════════════════════
-- PART II: Per-Pair Cut Error Bound
-- ═══════════════════════════════════════════════════════════════════

/-- Trivial upper bound: the number of G-adjacent pairs in A×B is at most |A|·|B|. -/
private lemma edge_count_le_product (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) ≤ A.card * B.card :=
  by exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_product A B).le

/-- **Core per-pair lemma**: For an ε-regular pair (P, Q), any A ⊆ P, B ⊆ Q satisfy:
    |e(A,B) - d(P,Q)·|A|·|B|| ≤ 2ε·|P|·|Q|.

    **Proof**: Two cases.
    - **Large** (|A| ≥ ε|P| and |B| ≥ ε|Q|): ε-regularity gives |d(A,B) - d(P,Q)| ≤ ε.
      Multiply by |A|·|B| ≤ |P|·|Q|.
    - **Small** (|A| < ε|P| or |B| < ε|Q|): trivially |e - d|A||B|| ≤ 2|A||B| ≤ 2ε|P||Q|.
-/
theorem pair_cut_error_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (P Q A B : Finset V)
    (hA : A ⊆ P) (hB : B ⊆ Q)
    (hreg : IsEpsilonRegular G eps P Q) :
    |(((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) -
      edgeDensity G P Q * A.card * B.card| ≤
    2 * eps * P.card * Q.card := by
  set e := (((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ)
  set d := edgeDensity G P Q
  have hnA : (0 : ℚ) ≤ A.card := Nat.cast_nonneg _
  have hnB : (0 : ℚ) ≤ B.card := Nat.cast_nonneg _
  have hnP : (0 : ℚ) ≤ P.card := Nat.cast_nonneg _
  have hnQ : (0 : ℚ) ≤ Q.card := Nat.cast_nonneg _
  have hAP : (A.card : ℚ) ≤ P.card := by exact_mod_cast Finset.card_le_card hA
  have hBQ : (B.card : ℚ) ≤ Q.card := by exact_mod_cast Finset.card_le_card hB
  have he_bound : e ≤ (A.card : ℚ) * B.card := edge_count_le_product G A B
  have he_nonneg : (0 : ℚ) ≤ e := by positivity
  have hd_nn : 0 ≤ d := edgeDensity_nonneg G P Q
  have hd_le1 : d ≤ 1 := edgeDensity_le_one G P Q
  by_cases hA_large : (A.card : ℚ) ≥ eps * P.card
  · by_cases hB_large : (B.card : ℚ) ≥ eps * Q.card
    · -- Both large: use ε-regularity
      -- Handle A = ∅ edge case first
      rcases eq_or_lt_of_le hnA with hnA0 | hnA_pos
      · have hA_eq0 : (A.card : ℚ) = 0 := hnA0.symm
        have he0 : e = 0 := le_antisymm
          (he_bound.trans (by simp [hA_eq0])) (by positivity)
        simp [hA_eq0, he0]
        positivity
      -- Handle B = ∅ edge case
      rcases eq_or_lt_of_le hnB with hnB0 | hnB_pos
      · have hB_eq0 : (B.card : ℚ) = 0 := hnB0.symm
        have he0 : e = 0 := le_antisymm
          (he_bound.trans (by simp [hB_eq0])) (by positivity)
        simp [hB_eq0, he0]
        positivity
      -- A, B, P, Q all nonempty
      have hnAB_pos : (0 : ℚ) < A.card * B.card := mul_pos hnA_pos hnB_pos
      have hnAB_ne : (A.card : ℚ) * B.card ≠ 0 := ne_of_gt hnAB_pos
      -- edgeDensity G A B = e / (|A| · |B|)
      have h_dAB : edgeDensity G A B = e / (A.card * B.card) := by
        unfold edgeDensity e; rw [dif_neg hnAB_ne]
      -- Apply ε-regularity: |d(A,B) - d(P,Q)| ≤ ε
      have hdev : |edgeDensity G A B - d| ≤ eps := hreg A B hA hB hA_large hB_large
      -- From |e/(A*B) - d| ≤ eps, multiply to get |e - d*(A*B)| ≤ eps*(A*B)
      have h_err : |e - d * (A.card * B.card)| ≤ eps * (A.card * B.card) := by
        have h1 : |e / (A.card * B.card) - d| ≤ eps := h_dAB ▸ hdev
        have h2 : |e - d * (A.card * B.card)| / (A.card * B.card) ≤ eps := by
          rwa [show e / (A.card * B.card) - d =
            (e - d * (A.card * B.card)) / (A.card * B.card) from by field_simp,
            abs_div, abs_of_pos hnAB_pos] at h1
        calc |e - d * (A.card * B.card)|
            = |e - d * (A.card * B.card)| / (A.card * B.card) * (A.card * B.card) :=
                (div_mul_cancel₀ _ (ne_of_gt hnAB_pos)).symm
          _ ≤ eps * (A.card * B.card) :=
                mul_le_mul_of_nonneg_right h2 (le_of_lt hnAB_pos)
      rw [show d * A.card * B.card = d * (A.card * B.card) from by ring]
      calc |e - d * (A.card * B.card)|
          ≤ eps * (A.card * B.card) := h_err
        _ ≤ eps * (P.card * Q.card) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hAP hBQ hnB_pos.le (hnA_pos.trans_le hAP).le)
                (le_of_lt heps)
        _ ≤ 2 * eps * P.card * Q.card := by nlinarith [mul_nonneg hnP hnQ]
    · -- B is small: |B| < ε|Q|
      push_neg at hB_large
      -- Key bound: A*B ≤ A*(eps*Q) ≤ P*(eps*Q) = eps*P*Q
      have hAB_le : A.card * B.card ≤ eps * (P.card * Q.card) :=
        calc A.card * B.card
            ≤ A.card * (eps * Q.card) :=
                mul_le_mul_of_nonneg_left hB_large.le hnA
          _ ≤ P.card * (eps * Q.card) :=
                mul_le_mul_of_nonneg_right hAP (mul_nonneg (le_of_lt heps) hnQ)
          _ = eps * (P.card * Q.card) := by ring
      rw [abs_le]; refine ⟨?_, ?_⟩
      · -- Lower bound: -(2*eps*P*Q) ≤ e - d*A*B
        have hd_AB : d * (A.card * B.card) ≤ eps * (P.card * Q.card) :=
          (mul_le_mul_of_nonneg_left hAB_le hd_nn).trans
            (by nlinarith [mul_nonneg (le_of_lt heps) (mul_nonneg hnP hnQ)])
        nlinarith [mul_nonneg (le_of_lt heps) (mul_nonneg hnP hnQ)]
      · -- Upper bound: e - d*A*B ≤ 2*eps*P*Q
        nlinarith [mul_nonneg hd_nn (mul_nonneg hnA hnB),
                   mul_nonneg (le_of_lt heps) (mul_nonneg hnP hnQ)]
  · -- A is small: |A| < ε|P|
    push_neg at hA_large
    -- Key bound: A*B ≤ A*Q ≤ (eps*P)*Q = eps*P*Q
    have hAB_le : (A.card : ℚ) * B.card ≤ eps * (P.card * Q.card) :=
      calc (A.card : ℚ) * B.card
          ≤ A.card * Q.card :=
              mul_le_mul_of_nonneg_left hBQ hnA
        _ ≤ (eps * P.card) * Q.card :=
              mul_le_mul_of_nonneg_right hA_large.le hnQ
        _ = eps * (P.card * Q.card) := by ring
    rw [abs_le]; refine ⟨?_, ?_⟩
    · -- Lower bound: -(2*eps*P*Q) ≤ e - d*A*B
      have hd_AB : d * (A.card * B.card) ≤ eps * (P.card * Q.card) :=
        (mul_le_mul_of_nonneg_left hAB_le hd_nn).trans
          (by nlinarith [mul_nonneg (le_of_lt heps) (mul_nonneg hnP hnQ)])
      nlinarith [mul_nonneg (le_of_lt heps) (mul_nonneg hnP hnQ)]
    · -- Upper bound: e - d*A*B ≤ 2*eps*P*Q
      nlinarith [mul_nonneg hd_nn (mul_nonneg hnA hnB),
                 mul_nonneg (le_of_lt heps) (mul_nonneg hnP hnQ)]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Partition Decomposition
-- ═══════════════════════════════════════════════════════════════════

/-- The pieces (A∩Pᵢ)×(B∩Pⱼ) for different (i,j) in a partition-product are pairwise disjoint. -/
private lemma product_pairs_disjoint (A B : Finset V)
    (parts : Finset (Finset V))
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q) :
    ∀ pq₁ ∈ parts.product parts, ∀ pq₂ ∈ parts.product parts,
      pq₁ ≠ pq₂ →
      Disjoint ((A ∩ pq₁.1).product (B ∩ pq₁.2))
               ((A ∩ pq₂.1).product (B ∩ pq₂.2)) := by
  rintro ⟨P₁, Q₁⟩ h₁ ⟨P₂, Q₂⟩ h₂ hne
  have h₁' := Finset.mem_product.mp h₁
  have h₂' := Finset.mem_product.mp h₂
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ h_in1 h_in2
  obtain ⟨ha1, hb1⟩ := Finset.mem_product.mp h_in1
  obtain ⟨ha2, hb2⟩ := Finset.mem_product.mp h_in2
  rw [Finset.mem_inter] at ha1 ha2 hb1 hb2
  rw [Ne, Prod.mk.injEq, not_and_or] at hne
  rcases hne with hP | hQ
  · exact absurd ha2.2 (Finset.disjoint_left.mp (hdisjoint P₁ P₂ h₁'.1 h₂'.1 hP) ha1.2)
  · exact absurd hb2.2 (Finset.disjoint_left.mp (hdisjoint Q₁ Q₂ h₁'.2 h₂'.2 hQ) hb1.2)

/-- **Partition sum identity**: For a disjoint cover of V,
    e(A,B) = Σᵢⱼ e(A∩Pᵢ, B∩Pⱼ).

    **Proof**: A×B decomposes as ⋃ᵢⱼ (A∩Pᵢ)×(B∩Pⱼ) (since the parts cover V),
    the pieces are pairwise disjoint (since the parts are pairwise disjoint),
    and the filter is compatible with the union. -/
theorem edge_count_partition_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q) :
    (((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) =
    (parts.product parts).sum (fun pq =>
      (((A ∩ pq.1).product (B ∩ pq.2)).filter (fun p => G.Adj p.1 p.2)).card) := by
  -- A×B = ⋃ᵢⱼ (A∩Pᵢ)×(B∩Pⱼ)
  have h_decomp : A.product B =
      (parts.product parts).biUnion (fun pq => (A ∩ pq.1).product (B ∩ pq.2)) := by
    ext ⟨a, b⟩
    rw [Finset.mem_biUnion]
    constructor
    · intro hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      obtain ⟨P, hP, haP⟩ := hcover a
      obtain ⟨Q, hQ, hbQ⟩ := hcover b
      exact ⟨(P, Q), Finset.mem_product.mpr ⟨hP, hQ⟩,
             Finset.mem_product.mpr ⟨Finset.mem_inter.mpr ⟨ha, haP⟩,
                                    Finset.mem_inter.mpr ⟨hb, hbQ⟩⟩⟩
    · intro hab
      obtain ⟨pq, _, hpq⟩ := hab
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hpq
      exact Finset.mem_product.mpr ⟨(Finset.mem_inter.mp h1).1,
                                   (Finset.mem_inter.mp h2).1⟩
  -- Filter distributes over biUnion
  have h_filter : (A.product B).filter (fun p => G.Adj p.1 p.2) =
      (parts.product parts).biUnion (fun pq =>
        ((A ∩ pq.1).product (B ∩ pq.2)).filter (fun p => G.Adj p.1 p.2)) := by
    rw [h_decomp]; ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨pq, hpq, hx⟩, hadj⟩; exact ⟨pq, hpq, hx, hadj⟩
    · rintro ⟨pq, hpq, hx, hadj⟩; exact ⟨⟨pq, hpq, hx⟩, hadj⟩
  -- The biUnion pieces are pairwise disjoint
  have h_disj : ∀ pq₁ ∈ parts.product parts, ∀ pq₂ ∈ parts.product parts,
      pq₁ ≠ pq₂ →
      Disjoint (((A ∩ pq₁.1).product (B ∩ pq₁.2)).filter (fun p => G.Adj p.1 p.2))
               (((A ∩ pq₂.1).product (B ∩ pq₂.2)).filter (fun p => G.Adj p.1 p.2)) :=
    fun pq₁ h₁ pq₂ h₂ hne =>
      (product_pairs_disjoint A B parts hdisjoint pq₁ h₁ pq₂ h₂ hne).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  -- card of disjoint biUnion = sum of cards
  rw [h_filter, Finset.card_biUnion h_disj]

/-- For a partition of V (disjoint cover), Σᵢⱼ |Pᵢ|·|Pⱼ| = n². -/
theorem parts_product_sum_eq_card_sq
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q) :
    (parts.product parts).sum (fun pq => (pq.1.card : ℚ) * pq.2.card) =
    (Fintype.card V : ℚ) ^ 2 := by
  -- Σᵢ |Pᵢ| = n via disjoint biUnion
  have h_biUnion : parts.biUnion id = Finset.univ := by
    ext v; simp [Finset.mem_biUnion, id, hcover]
  have h_sum : parts.sum (fun P => P.card) = Fintype.card V := by
    have h_pw : (↑parts : Set (Finset V)).PairwiseDisjoint id :=
      fun P hP Q hQ hne =>
        hdisjoint P Q (Finset.mem_coe.mp hP) (Finset.mem_coe.mp hQ) hne
    have h_card : (parts.biUnion id).card = parts.sum (fun P => (id P).card) :=
      Finset.card_biUnion h_pw
    simp only [id] at h_card
    rw [h_biUnion, Finset.card_univ] at h_card
    exact h_card.symm
  -- Σᵢⱼ |Pᵢ||Pⱼ| = (Σᵢ |Pᵢ|)² = n²
  simp only [show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have h : (parts.sum fun P => (P.card : ℚ)) = Fintype.card V := by exact_mod_cast h_sum
  rw [h]; ring

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: Main Comparison Theorem
-- ═══════════════════════════════════════════════════════════════════

/-- **Szemerédi ⟹ Frieze-Kannan**: Every ε-regular partition is a 2ε-cut-approximation.

    This is the central comparison theorem. The FK guarantee (cut norm ≤ 2ε) is strictly
    weaker than Szemerédi's guarantee (every pair is ε-regular), but FK uses far fewer parts
    (4^(1/ε²) vs tower(1/ε)).

    **Proof**: For each pair (Pᵢ,Pⱼ):
    (1) `edge_count_partition_sum`: e(A,B) = Σᵢⱼ e(A∩Pᵢ, B∩Pⱼ)
    (2) Triangle inequality: |Σᵢⱼ errᵢⱼ| ≤ Σᵢⱼ |errᵢⱼ|
    (3) `pair_cut_error_bound`: |errᵢⱼ| ≤ 2ε|Pᵢ||Pⱼ| for each pair
    (4) `parts_product_sum_eq_card_sq`: Σᵢⱼ 2ε|Pᵢ||Pⱼ| = 2ε·n² -/
theorem szemeredi_implies_fk (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (hall_reg : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → IsEpsilonRegular G eps P Q) :
    IsCutApproximation G (2 * eps) parts := by
  intro A B
  -- Rewrite e(A,B) using the partition decomposition
  rw [edge_count_partition_sum G A B parts hcover hdisjoint]
  -- Push the ℕ→ℚ cast inside the sum, then combine into a single sum of differences
  simp only [Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  -- Chain: |Σ errᵢⱼ| ≤ Σ |errᵢⱼ| ≤ Σ 2ε|Pᵢ||Pⱼ| = 2ε·n²
  calc |(parts.product parts).sum (fun pq =>
          (((A ∩ pq.1).product (B ∩ pq.2)).filter fun p => G.Adj p.1 p.2).card -
          edgeDensity G pq.1 pq.2 * (A ∩ pq.1).card * (B ∩ pq.2).card)|
      ≤ (parts.product parts).sum (fun pq =>
          |(((A ∩ pq.1).product (B ∩ pq.2)).filter (fun p => G.Adj p.1 p.2)).card -
            edgeDensity G pq.1 pq.2 * (A ∩ pq.1).card * (B ∩ pq.2).card|) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (parts.product parts).sum (fun pq => 2 * eps * pq.1.card * pq.2.card) := by
        apply Finset.sum_le_sum
        intro ⟨P, Q⟩ hpq
        exact pair_cut_error_bound G eps heps P Q (A ∩ P) (B ∩ Q)
          Finset.inter_subset_right Finset.inter_subset_right
          (hall_reg P Q (Finset.mem_product.mp hpq).1 (Finset.mem_product.mp hpq).2)
    _ = 2 * eps * (Fintype.card V : ℚ) ^ 2 := by
        simp_rw [show ∀ pq : Finset V × Finset V, 2 * eps * (pq.1.card : ℚ) * pq.2.card =
            2 * eps * ((pq.1.card : ℚ) * pq.2.card) from fun pq => by ring]
        rw [← Finset.mul_sum]
        congr 1
        exact parts_product_sum_eq_card_sq parts hcover hdisjoint

-- ═══════════════════════════════════════════════════════════════════
-- PART V: Szemerédi Bound vs FK Bound
-- ═══════════════════════════════════════════════════════════════════

/-- The Szemerédi step function `stepBound n = n · 4^n` satisfies `stepBound n ≥ 4^n` (n ≥ 1).
    The Szemerédi bound iterates stepBound ~(4/ε^5) times, yielding a tower function,
    while FK needs only `4^⌈1/ε²⌉` parts (singly exponential in 1/ε²). -/
theorem sz_stepBound_ge_power (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ SzemerediRegularity.stepBound n :=
  Nat.le_mul_of_pos_left _ hn

/-- After two iterations, the Szemerédi bound exceeds 4^(4^n): tower-type growth confirmed.
    This demonstrates that the Szemerédi bound is not singly exponential. -/
theorem sz_two_steps_tower (n : ℕ) (hn : 1 ≤ n) :
    4 ^ 4 ^ n ≤ SzemerediRegularity.stepBound (SzemerediRegularity.stepBound n) :=
  calc 4 ^ 4 ^ n
      ≤ 4 ^ SzemerediRegularity.stepBound n :=
        Nat.pow_le_pow_right (by norm_num) (sz_stepBound_ge_power n hn)
    _ ≤ SzemerediRegularity.stepBound (SzemerediRegularity.stepBound n) :=
        sz_stepBound_ge_power _ (by have := SzemerediRegularity.stepBound_pos hn; omega)

/-- **FK bound**: at most `4^⌈(1/ε)²⌉` parts for an ε-cut-approximation.
    For ε = 1/10, FK needs ≤ 4^100 parts vs Szemerédi's tower(10^5) parts. -/
noncomputable def fkBound (eps : ℚ) : ℕ := 4 ^ (⌈((1 : ℚ) / eps) ^ 2⌉₊)

/-- Concrete bound comparison at ε = 1/2:
    FK bound: 4^4 = 256 parts
    Szemerédi stepBound(1) = 1 · 4^1 = 4; after 1 step from initial bound ≥ 4^4 = 256.
    After 2 steps: at least 4^(4^4) = 4^256 ≫ 256.
    This confirms the singly-exponential vs tower dichotomy. -/
theorem fk_bound_at_half : fkBound (1/2) = 4 ^ 4 := by
  unfold fkBound
  norm_num

theorem sz_two_steps_ge_at_1 : 4 ^ (4 ^ 1) ≤
    SzemerediRegularity.stepBound (SzemerediRegularity.stepBound 1) :=
  sz_two_steps_tower 1 le_rfl

/-
## Summary Table

| Result | Statement |
|--------|-----------|
| `pair_cut_error_bound` | ε-regular pair ⟹ cut error ≤ 2ε|P||Q| |
| `edge_count_partition_sum` | e(A,B) = Σᵢⱼ e(A∩Pᵢ,B∩Pⱼ) [partition identity] |
| `parts_product_sum_eq_card_sq` | Σᵢⱼ |Pᵢ||Pⱼ| = n² [key bound for sum] |
| `szemeredi_implies_fk` | ε-regular partition ⟹ 2ε-cut-approximation |
| `sz_stepBound_ge_power` | stepBound n ≥ 4^n [Szemerédi's polynomial overhead] |
| `sz_two_steps_tower` | 2-step bound ≥ 4^(4^n) [tower growth confirmed] |
| `fk_bound_at_half` | fkBound(1/2) = 4^4 = 256 [explicit FK bound] |

Axiom count: 0, Sorry count: 0
-/

#check @pair_cut_error_bound
#check @edge_count_partition_sum
#check @parts_product_sum_eq_card_sq
#check @szemeredi_implies_fk
#check @sz_stepBound_ge_power
#check @sz_two_steps_tower

end SzemerediFKComparison
