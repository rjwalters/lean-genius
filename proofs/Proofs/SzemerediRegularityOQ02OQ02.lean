/-
# Szemerédi ⟹ Frieze-Kannan: the cut-approximation constant is 1, not 2

OQ-02-OQ-02 follow-up to `szemeredi-regularity-oq-02` (Frieze-Kannan comparison).

## The question

`SzemerediRegularityOQ02.szemeredi_implies_fk` proves that every ε-regular
partition is a **2ε**-cut-approximation. The open question asks:

> Is the factor-of-2 constant tight, or can it be improved to 1?

## The answer: improvable to 1

The factor of 2 is **not** intrinsic — it is an artifact of a loose triangle-inequality
step in the "small subset" case of the per-pair bound. We sharpen the per-pair estimate
to the optimal `ε·|P|·|Q|` and conclude that every ε-regular partition is already an
**ε**-cut-approximation (`szemeredi_implies_fk_sharp`).

### Why the sharp bound holds

For an ε-regular pair `(P,Q)` and `A ⊆ P`, `B ⊆ Q`, write `e = e(A,B)` and
`d = d(P,Q) ∈ [0,1]`. We bound `|e − d·|A|·|B||`:

- **Large case** (`|A| ≥ ε|P|`, `|B| ≥ ε|Q|`): ε-regularity gives
  `|d(A,B) − d| ≤ ε`; multiplying by `|A||B| ≤ |P||Q|` yields `≤ ε|P||Q|`.
- **Small case** (`|A| < ε|P|` or `|B| < ε|Q|`): here `|A||B| ≤ ε|P||Q|`, so
  **both** `e ≤ |A||B| ≤ ε|P||Q|` and `d·|A||B| ≤ |A||B| ≤ ε|P||Q|` individually.
  For nonnegative `x, y` one has `|x − y| ≤ max(x, y)`, hence `|e − d|A||B|| ≤ ε|P||Q|`.

The old proof used the weaker `|e − d|A||B|| ≤ e + d|A||B| ≤ 2ε|P||Q|` in the small
case. Replacing `x + y` by `max(x, y)` recovers the factor of 1. Summing over all
`|parts|²` pairs (via the same partition decomposition as the original) turns the
per-pair `ε|P||Q|` into the global `ε·n²`.

This is optimal: the large case already forces the `ε` rate, so no constant below 1
is achievable by this route. Thus the answer to the OQ is **1** (the constant 2 was
slack, not tight).

## Main results

- `pair_cut_error_bound_sharp` : single ε-regular pair ⟹ cut error ≤ ε|P||Q|
- `szemeredi_implies_fk_sharp` : ε-regular partition ⟹ **ε**-cut-approximation

## Tags
graph-theory, combinatorics, szemeredi, regularity, frieze-kannan, cut-norm, sharp-constant
-/

import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity
import Proofs.SzemerediRegularityOQ02

namespace SzemerediFKComparisonSharp

open Szemeredi.Core Szemeredi.Regularity SzemerediFKComparison Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- Sharp per-pair cut error bound: ε|P||Q| (was 2ε|P||Q|)
-- ═══════════════════════════════════════════════════════════════════

/-- **Sharp per-pair lemma**: For an ε-regular pair `(P, Q)`, any `A ⊆ P`, `B ⊆ Q`
    satisfy `|e(A,B) − d(P,Q)·|A|·|B|| ≤ ε·|P|·|Q|`.

    This improves `SzemerediRegularityOQ02.pair_cut_error_bound` (which gives
    `2ε·|P|·|Q|`) by a factor of 2. The improvement is in the "small" case: instead of
    `|e − d|A||B|| ≤ e + d|A||B| ≤ 2ε|P||Q|`, we observe that `e` and `d|A||B|` are
    *each* `≤ ε|P||Q|`, so their difference is too (`|x − y| ≤ max(x,y)` for `x,y ≥ 0`). -/
theorem pair_cut_error_bound_sharp (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (P Q A B : Finset V)
    (hA : A ⊆ P) (hB : B ⊆ Q)
    (hreg : IsEpsilonRegular G eps P Q) :
    |(((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) -
      edgeDensity G P Q * A.card * B.card| ≤
    eps * P.card * Q.card := by
  set e := (((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) with he_def
  set d := edgeDensity G P Q with hd_def
  have hnA : (0 : ℚ) ≤ A.card := Nat.cast_nonneg _
  have hnB : (0 : ℚ) ≤ B.card := Nat.cast_nonneg _
  have hnP : (0 : ℚ) ≤ P.card := Nat.cast_nonneg _
  have hnQ : (0 : ℚ) ≤ Q.card := Nat.cast_nonneg _
  have hAP : (A.card : ℚ) ≤ P.card := by exact_mod_cast Finset.card_le_card hA
  have hBQ : (B.card : ℚ) ≤ Q.card := by exact_mod_cast Finset.card_le_card hB
  have he_bound : e ≤ (A.card : ℚ) * B.card := by
    simp only [he_def]
    exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_product A B).le
  have he_nonneg : (0 : ℚ) ≤ e := by simp only [he_def]; positivity
  have hd_nn : 0 ≤ d := edgeDensity_nonneg G P Q
  have hd_le1 : d ≤ 1 := edgeDensity_le_one G P Q
  by_cases hA_large : (A.card : ℚ) ≥ eps * P.card
  · by_cases hB_large : (B.card : ℚ) ≥ eps * Q.card
    · -- Both large: use ε-regularity — the difference is ≤ ε|A||B| ≤ ε|P||Q|.
      rcases eq_or_lt_of_le hnA with hnA0 | hnA_pos
      · have hA_eq0 : (A.card : ℚ) = 0 := hnA0.symm
        have he0 : e = 0 := le_antisymm
          (he_bound.trans (by simp [hA_eq0])) he_nonneg
        simp [hA_eq0, he0]
        positivity
      rcases eq_or_lt_of_le hnB with hnB0 | hnB_pos
      · have hB_eq0 : (B.card : ℚ) = 0 := hnB0.symm
        have he0 : e = 0 := le_antisymm
          (he_bound.trans (by simp [hB_eq0])) he_nonneg
        simp [hB_eq0, he0]
        positivity
      have hnAB_pos : (0 : ℚ) < A.card * B.card := mul_pos hnA_pos hnB_pos
      have hnAB_ne : (A.card : ℚ) * B.card ≠ 0 := ne_of_gt hnAB_pos
      have h_dAB : edgeDensity G A B = e / (A.card * B.card) := by
        unfold edgeDensity e; rw [dif_neg hnAB_ne]
      have hdev : |edgeDensity G A B - d| ≤ eps := hreg A B hA hB hA_large hB_large
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
        _ = eps * P.card * Q.card := by ring
    · -- B small (|B| < ε|Q|): both e and d|A||B| are ≤ ε|P||Q| individually.
      push_neg at hB_large
      have hAB_le : (A.card : ℚ) * B.card ≤ eps * (P.card * Q.card) :=
        calc (A.card : ℚ) * B.card
            ≤ A.card * (eps * Q.card) :=
                mul_le_mul_of_nonneg_left hB_large.le hnA
          _ ≤ P.card * (eps * Q.card) :=
                mul_le_mul_of_nonneg_right hAP (mul_nonneg (le_of_lt heps) hnQ)
          _ = eps * (P.card * Q.card) := by ring
      have he_le : e ≤ eps * (P.card * Q.card) := he_bound.trans hAB_le
      have hd_AB : d * (A.card * B.card) ≤ eps * (P.card * Q.card) :=
        (mul_le_of_le_one_left (by positivity) hd_le1).trans hAB_le
      have hd_AB_nn : (0 : ℚ) ≤ d * (A.card * B.card) := by positivity
      rw [show d * A.card * B.card = d * (A.card * B.card) from by ring, abs_le]
      exact ⟨by nlinarith, by nlinarith⟩
  · -- A small (|A| < ε|P|): both e and d|A||B| are ≤ ε|P||Q| individually.
    push_neg at hA_large
    have hAB_le : (A.card : ℚ) * B.card ≤ eps * (P.card * Q.card) :=
      calc (A.card : ℚ) * B.card
          ≤ A.card * Q.card :=
              mul_le_mul_of_nonneg_left hBQ hnA
        _ ≤ (eps * P.card) * Q.card :=
              mul_le_mul_of_nonneg_right hA_large.le hnQ
        _ = eps * (P.card * Q.card) := by ring
    have he_le : e ≤ eps * (P.card * Q.card) := he_bound.trans hAB_le
    have hd_AB : d * (A.card * B.card) ≤ eps * (P.card * Q.card) :=
      (mul_le_of_le_one_left (by positivity) hd_le1).trans hAB_le
    have hd_AB_nn : (0 : ℚ) ≤ d * (A.card * B.card) := by positivity
    rw [show d * A.card * B.card = d * (A.card * B.card) from by ring, abs_le]
    exact ⟨by nlinarith, by nlinarith⟩

-- ═══════════════════════════════════════════════════════════════════
-- Sharp main comparison: ε-regular ⟹ ε-cut-approximation
-- ═══════════════════════════════════════════════════════════════════

/-- **Szemerédi ⟹ Frieze-Kannan, sharp constant**: Every ε-regular partition is an
    **ε**-cut-approximation (not merely `2ε`).

    This answers `szemeredi-regularity-oq-02-oq-02`: the factor-of-2 in
    `SzemerediRegularityOQ02.szemeredi_implies_fk` is *not* tight — it improves to 1.
    The proof is identical to the original, but calls the sharp per-pair bound
    `pair_cut_error_bound_sharp`, so the summed error is `ε·n²` rather than `2ε·n²`. -/
theorem szemeredi_implies_fk_sharp (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (hall_reg : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → IsEpsilonRegular G eps P Q) :
    IsCutApproximation G eps parts := by
  intro A B
  rw [edge_count_partition_sum G A B parts hcover hdisjoint]
  simp only [Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  calc |(parts.product parts).sum (fun pq =>
          (((A ∩ pq.1).product (B ∩ pq.2)).filter fun p => G.Adj p.1 p.2).card -
          edgeDensity G pq.1 pq.2 * (A ∩ pq.1).card * (B ∩ pq.2).card)|
      ≤ (parts.product parts).sum (fun pq =>
          |(((A ∩ pq.1).product (B ∩ pq.2)).filter (fun p => G.Adj p.1 p.2)).card -
            edgeDensity G pq.1 pq.2 * (A ∩ pq.1).card * (B ∩ pq.2).card|) :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (parts.product parts).sum (fun pq => eps * pq.1.card * pq.2.card) := by
        apply Finset.sum_le_sum
        intro ⟨P, Q⟩ hpq
        exact pair_cut_error_bound_sharp G eps heps P Q (A ∩ P) (B ∩ Q)
          Finset.inter_subset_right Finset.inter_subset_right
          (hall_reg P Q (Finset.mem_product.mp hpq).1 (Finset.mem_product.mp hpq).2)
    _ = eps * (Fintype.card V : ℚ) ^ 2 := by
        simp_rw [show ∀ pq : Finset V × Finset V, eps * (pq.1.card : ℚ) * pq.2.card =
            eps * ((pq.1.card : ℚ) * pq.2.card) from fun pq => by ring]
        rw [← Finset.mul_sum]
        congr 1
        exact parts_product_sum_eq_card_sq parts hcover hdisjoint

/-- Sanity check: the sharp bound really is stronger. Since `ε ≤ 2ε` for `ε ≥ 0`,
    an `ε`-cut-approximation is in particular a `2ε`-cut-approximation, so
    `szemeredi_implies_fk_sharp` recovers the original `szemeredi_implies_fk`. -/
theorem sharp_recovers_original (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (hall_reg : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → IsEpsilonRegular G eps P Q) :
    IsCutApproximation G (2 * eps) parts := by
  intro A B
  have hsharp := szemeredi_implies_fk_sharp G eps heps parts hcover hdisjoint hall_reg A B
  have hmono : eps * (Fintype.card V : ℚ) ^ 2 ≤ 2 * eps * (Fintype.card V : ℚ) ^ 2 := by
    have : (0 : ℚ) ≤ eps * (Fintype.card V : ℚ) ^ 2 := by positivity
    nlinarith
  linarith

#check @pair_cut_error_bound_sharp
#check @szemeredi_implies_fk_sharp

end SzemerediFKComparisonSharp

-- Axiom audit: expect only propext / Classical.choice / Quot.sound.
#print axioms SzemerediFKComparisonSharp.pair_cut_error_bound_sharp
#print axioms SzemerediFKComparisonSharp.szemeredi_implies_fk_sharp
#print axioms SzemerediFKComparisonSharp.sharp_recovers_original
