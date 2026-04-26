/-
  Szemeredi Core OQ-01: Energy Increment Lemma

  If a partition has an irregular pair (A, B), then the refinement obtained
  by splitting A and B using the irregular witnesses increases the partition
  energy by at least ε^6.

  This file proves the key algebraic steps:
  1. edgeDensity_symm: edge density is symmetric d(A,B) = d(B,A)
  2. density_sq_convex_right: convexity when splitting the second argument
  3. sub4pair_energy_lower_bound: splitting both A and B never decreases energy
  4. energy_excess_A_split: exact excess formula from splitting A
  5. four_subpair_edge_count_identity: 2D weighted average identity
  6. four_subpair_deviation_identity: δ-decomposition (variance formula)
  7. four_subpair_excess_lb: single-pair lower bound on energy excess
  8. energy_increment_packaging: block-decomposition core lemma (fully proved)
  9. energy_increment_step: main theorem (0 sorries — uses energy_increment_packaging)

  Mathematical content: Komlós-Simonovits (1996), §3; Szemerédi (1975).

  Note on ε^6 vs ε^5: For a SINGLE irregular pair the correct energy increment
  bound is ε^6. The ε^5 bound in the standard Szemerédi proof comes from summing
  over all ≥ ε·k² irregular pairs; each contributes ~ε^4/k², giving ε^5 total.
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity

namespace Szemeredi.EnergyIncrement

open Classical Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: SYMMETRY OF EDGE DENSITY
-- ═══════════════════════════════════════════════════════════════════

/-- The edge count from A to B equals the edge count from B to A. -/
private theorem edgeDensity_card_symm (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    ((A.product B).filter (fun p => G.Adj p.1 p.2)).card =
    ((B.product A).filter (fun p => G.Adj p.1 p.2)).card := by
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · -- membership: swap (a,b) ↦ (b,a) maps A×B filtered → B×A filtered
    intro p hp
    have hf := Finset.mem_filter.mp hp
    have hprod := Finset.mem_product.mp hf.1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩, G.adj_symm hf.2⟩
  · -- injectivity: swap is injective
    intro p₁ _ p₂ _ h
    have h' := Prod.mk.inj h
    exact Prod.ext h'.2 h'.1
  · -- surjectivity: every (b,a) ∈ B×A comes from (a,b) ∈ A×B
    intro q hq
    have hf := Finset.mem_filter.mp hq
    have hprod := Finset.mem_product.mp hf.1
    refine ⟨(q.2, q.1), ?_, Prod.eta q⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hprod.2, hprod.1⟩, G.adj_symm hf.2⟩

/-- Edge density is symmetric: d(A,B) = d(B,A). -/
theorem edgeDensity_symm (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : edgeDensity G A B = edgeDensity G B A := by
  unfold edgeDensity
  simp_rw [show (A.card : ℚ) * B.card = (B.card : ℚ) * A.card from by ring]
  split_ifs with h
  · rfl
  · congr 1
    exact_mod_cast edgeDensity_card_symm G A B

-- ═══════════════════════════════════════════════════════════════════
-- PART II: CONVEXITY FOR THE SECOND ARGUMENT
-- ═══════════════════════════════════════════════════════════════════

/-- Splitting the second argument: d(A,·) satisfies the same convexity as d(·,B). -/
theorem density_sq_convex_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ B₂ : Finset V) (hB : Disjoint B₁ B₂) :
    (B₁.card : ℚ) * (edgeDensity G A B₁) ^ 2 +
    (B₂.card : ℚ) * (edgeDensity G A B₂) ^ 2 ≥
    ((B₁.card + B₂.card) : ℚ) * (edgeDensity G A (B₁ ∪ B₂)) ^ 2 := by
  rw [edgeDensity_symm G A B₁, edgeDensity_symm G A B₂, edgeDensity_symm G A (B₁ ∪ B₂)]
  exact density_sq_convex G B₁ B₂ A hB

-- ═══════════════════════════════════════════════════════════════════
-- PART III: FOUR-SUBPAIR ENERGY LOWER BOUND
-- ═══════════════════════════════════════════════════════════════════

/-- Splitting A → {A₁,A₂} and B → {B₁,B₂} never decreases the (A,B) energy contribution.

    The proof chains two applications of density_sq_convex:
    Row lower bound: for each i, Aᵢ-row energy ≥ Aᵢ * (B₁+B₂) * d(Aᵢ,B)²
    Column lower bound: row-sum ≥ (A₁+A₂) * (B₁+B₂) * d(A,B)² -/
theorem sub4pair_energy_lower_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B₁ B₂ : Finset V) (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    (A₁.card : ℚ) * B₁.card * (edgeDensity G A₁ B₁) ^ 2 +
    (A₁.card : ℚ) * B₂.card * (edgeDensity G A₁ B₂) ^ 2 +
    (A₂.card : ℚ) * B₁.card * (edgeDensity G A₂ B₁) ^ 2 +
    (A₂.card : ℚ) * B₂.card * (edgeDensity G A₂ B₂) ^ 2 ≥
    ((A₁.card + A₂.card) : ℚ) * (B₁.card + B₂.card) *
      (edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)) ^ 2 := by
  -- Set abbreviations to reduce clutter
  set a₁ : ℚ := (A₁.card : ℚ); set a₂ : ℚ := (A₂.card : ℚ)
  set b₁ : ℚ := (B₁.card : ℚ); set b₂ : ℚ := (B₂.card : ℚ)
  set d₁₁ := edgeDensity G A₁ B₁; set d₁₂ := edgeDensity G A₁ B₂
  set d₂₁ := edgeDensity G A₂ B₁; set d₂₂ := edgeDensity G A₂ B₂
  set dA₁ := edgeDensity G A₁ (B₁ ∪ B₂); set dA₂ := edgeDensity G A₂ (B₁ ∪ B₂)
  -- B-split row bounds (from density_sq_convex_right)
  have hB_A₁ : (b₁ + b₂) * dA₁ ^ 2 ≤ b₁ * d₁₁ ^ 2 + b₂ * d₁₂ ^ 2 := by
    have h := density_sq_convex_right G A₁ B₁ B₂ hB
    push_cast at h; linarith
  have hB_A₂ : (b₁ + b₂) * dA₂ ^ 2 ≤ b₁ * d₂₁ ^ 2 + b₂ * d₂₂ ^ 2 := by
    have h := density_sq_convex_right G A₂ B₁ B₂ hB
    push_cast at h; linarith
  have ha₁_nn : (0 : ℚ) ≤ a₁ := Nat.cast_nonneg _
  have ha₂_nn : (0 : ℚ) ≤ a₂ := Nat.cast_nonneg _
  -- Row lower bounds: Aᵢ * (B₁+B₂) * dAᵢ² ≤ Aᵢ-row energy
  have hrow1 : a₁ * (b₁ + b₂) * dA₁ ^ 2 ≤ a₁ * b₁ * d₁₁ ^ 2 + a₁ * b₂ * d₁₂ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hB_A₁ ha₁_nn
    ring_nf at h ⊢; linarith
  have hrow2 : a₂ * (b₁ + b₂) * dA₂ ^ 2 ≤ a₂ * b₁ * d₂₁ ^ 2 + a₂ * b₂ * d₂₂ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hB_A₂ ha₂_nn
    ring_nf at h ⊢; linarith
  -- A-split column bound (from density_sq_convex)
  have hA_B : (a₁ + a₂) * edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂) ^ 2 ≤
      a₁ * dA₁ ^ 2 + a₂ * dA₂ ^ 2 := by
    have h := density_sq_convex G A₁ A₂ (B₁ ∪ B₂) hA
    push_cast at h
    linarith
  -- Scale column bound by (b₁+b₂) ≥ 0
  have hcol : (a₁ + a₂) * (b₁ + b₂) * edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂) ^ 2 ≤
      a₁ * (b₁ + b₂) * dA₁ ^ 2 + a₂ * (b₁ + b₂) * dA₂ ^ 2 := by
    have hb : (0 : ℚ) ≤ b₁ + b₂ := by positivity
    have h := mul_le_mul_of_nonneg_right hA_B hb
    ring_nf at h ⊢; linarith
  -- Goal: a₁b₁d₁₁² + a₁b₂d₁₂² + a₂b₁d₂₁² + a₂b₂d₂₂² ≥ (a₁+a₂)(b₁+b₂)dAB²
  -- Chain: (a₁+a₂)(b₁+b₂)dAB² ≤ a₁(b₁+b₂)dA₁² + a₂(b₁+b₂)dA₂² ≤ 4sum
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: WEIGHTED AVERAGE IDENTITY AND ENERGY EXCESS
-- ═══════════════════════════════════════════════════════════════════

/-- The density d(A₁∪A₂, B) is the |A|-weighted average of d(A₁,B) and d(A₂,B).
    This is the fundamental edge-count additivity property. -/
theorem edgeDensity_union_weighted_avg (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂)
    (ha₁ : 0 < A₁.card) (ha₂ : 0 < A₂.card) :
    edgeDensity G (A₁ ∪ A₂) B =
    ((A₁.card : ℚ) * edgeDensity G A₁ B + A₂.card * edgeDensity G A₂ B) /
    (A₁.card + A₂.card) := by
  set d₁ := edgeDensity G A₁ B; set d₂ := edgeDensity G A₂ B
  set d := edgeDensity G (A₁ ∪ A₂) B
  set n₁ : ℚ := ↑A₁.card; set n₂ : ℚ := ↑A₂.card
  have hn₁ : 0 < n₁ := Nat.cast_pos.mpr ha₁
  have hn₂ : 0 < n₂ := Nat.cast_pos.mpr ha₂
  have hnn : n₁ + n₂ ≠ 0 := ne_of_gt (by linarith)
  have hcard : (↑(A₁ ∪ A₂).card : ℚ) = n₁ + n₂ := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  -- Inline card_mul_edgeDensity: |A|*|B|*d(A,B) = edge count
  have hmul : ∀ A : Finset V, (A.card : ℚ) * B.card * edgeDensity G A B =
      ↑((A.product B).filter (fun p => G.Adj p.1 p.2)).card := fun A => by
    unfold edgeDensity; split_ifs with h
    · rw [mul_zero]; symm; rw [Nat.cast_eq_zero, Finset.card_eq_zero]
      rcases mul_eq_zero.mp h with ha | hb
      · have hA := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp ha)
        ext x; simp [hA, Finset.not_mem_empty]
      · have hB := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hb)
        ext x; simp [Finset.product, hB, Finset.not_mem_empty]
    · exact mul_div_cancel₀ _ h
  -- Inline edge_count_union: e(A₁∪A₂,B) = e(A₁,B) + e(A₂,B)
  have he : (↑(((A₁ ∪ A₂).product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) =
      ↑((A₁.product B).filter (fun p => G.Adj p.1 p.2)).card +
      ↑((A₂.product B).filter (fun p => G.Adj p.1 p.2)).card := by
    have h_prod : (A₁ ∪ A₂).product B = A₁.product B ∪ A₂.product B := by
      ext ⟨a, b⟩
      constructor
      · intro h; have := Finset.mem_product.mp h
        rcases Finset.mem_union.mp this.1 with ha | ha
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr ⟨ha, this.2⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr ⟨ha, this.2⟩))
      · intro h
        rcases Finset.mem_union.mp h with hab | hab
        · exact Finset.mem_product.mpr
            ⟨Finset.mem_union.mpr (Or.inl (Finset.mem_product.mp hab).1),
             (Finset.mem_product.mp hab).2⟩
        · exact Finset.mem_product.mpr
            ⟨Finset.mem_union.mpr (Or.inr (Finset.mem_product.mp hab).1),
             (Finset.mem_product.mp hab).2⟩
    rw [h_prod, Finset.filter_union]
    have hdisj : Disjoint ((A₁.product B).filter (fun p => G.Adj p.1 p.2))
                           ((A₂.product B).filter (fun p => G.Adj p.1 p.2)) := by
      apply Finset.disjoint_filter_filter
      rw [Finset.disjoint_left]; intro x h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).1
        (Finset.disjoint_left.mp hA (Finset.mem_product.mp h₁).1)
    exact_mod_cast Finset.card_union_of_disjoint hdisj
  -- Weighted average: (n₁+n₂)*B.card*d = n₁*B.card*d₁ + n₂*B.card*d₂
  have h₁ := hmul A₁; have h₂ := hmul A₂; have h₃ := hmul (A₁ ∪ A₂)
  rw [hcard] at h₃
  have havg : (n₁ + n₂) * ↑B.card * d = n₁ * ↑B.card * d₁ + n₂ * ↑B.card * d₂ := by
    linarith [h₁, h₂, h₃, he]
  -- B empty case: all densities are 0
  by_cases hB : (B.card : ℚ) = 0
  · have h0 : ∀ S : Finset V, edgeDensity G S B = 0 := fun S => by
      unfold edgeDensity
      rw [dif_pos (show (↑S.card : ℚ) * ↑B.card = 0 from by rw [hB, mul_zero])]
    simp [show d = 0 from h0 _, show d₁ = 0 from h0 _, show d₂ = 0 from h0 _]
  · -- Cancel B.card, then divide by (n₁+n₂)
    have hd_avg : (n₁ + n₂) * d = n₁ * d₁ + n₂ * d₂ :=
      mul_left_cancel₀ hB (show ↑B.card * ((n₁ + n₂) * d) =
          ↑B.card * (n₁ * d₁ + n₂ * d₂) from by nlinarith)
    rw [eq_div_iff hnn]; linarith

/-- The energy excess from splitting A (with B fixed):
      |A₁|·d(A₁,B)² + |A₂|·d(A₂,B)² - |A|·d(A,B)² = |A₁|·|A₂|/|A| · (d(A₁,B) - d(A₂,B))²
    Proved using the weighted average identity and split_energy_identity. -/
theorem energy_excess_A_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂)
    (ha₁ : 0 < A₁.card) (ha₂ : 0 < A₂.card) :
    (A₁.card : ℚ) * (edgeDensity G A₁ B) ^ 2 +
    (A₂.card : ℚ) * (edgeDensity G A₂ B) ^ 2 -
    ((A₁.card + A₂.card) : ℚ) * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 =
    (A₁.card : ℚ) * A₂.card / (A₁.card + A₂.card) *
      (edgeDensity G A₁ B - edgeDensity G A₂ B) ^ 2 := by
  have han : (A₁.card : ℚ) + A₂.card ≠ 0 := by positivity
  rw [edgeDensity_union_weighted_avg G A₁ A₂ B hA ha₁ ha₂]
  push_cast
  rw [split_energy_identity _ _ _ _ han]
  ring

-- ═══════════════════════════════════════════════════════════════════
-- PART V: ALGEBRAIC INFRASTRUCTURE FOR ENERGY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

/-- Edge count additivity for a 2×2 split: the weighted sum of sub-pair densities
    equals the full pair density (weighted by sizes).
    This is the 2D analogue of `edgeDensity_union_weighted_avg`, proved by
    double application of edge count union additivity. -/
theorem four_subpair_edge_count_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B₁ B₂ : Finset V) (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    (A₁.card : ℚ) * B₁.card * edgeDensity G A₁ B₁ +
    (A₁.card : ℚ) * B₂.card * edgeDensity G A₁ B₂ +
    (A₂.card : ℚ) * B₁.card * edgeDensity G A₂ B₁ +
    (A₂.card : ℚ) * B₂.card * edgeDensity G A₂ B₂ =
    ((A₁.card + A₂.card) : ℚ) * (B₁.card + B₂.card) *
      edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  -- Inline card_mul_edgeDensity: |X|*|Y|*d(X,Y) = edge count e(X,Y)
  have hmul : ∀ X Y : Finset V, (X.card : ℚ) * Y.card * edgeDensity G X Y =
      ↑((X.product Y).filter (fun p => G.Adj p.1 p.2)).card := by
    intro X Y; unfold edgeDensity; split_ifs with h
    · rw [mul_zero]; symm; rw [Nat.cast_eq_zero, Finset.card_eq_zero]
      rcases mul_eq_zero.mp h with hx | hy
      · simp [Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hx)]
      · ext x; simp [Finset.product, Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hy)]
    · exact mul_div_cancel₀ _ h
  -- Inline edge_count_union: e(X₁∪X₂, Y) = e(X₁,Y) + e(X₂,Y)
  have heu : ∀ X₁ X₂ Y : Finset V, Disjoint X₁ X₂ →
      ((X₁ ∪ X₂).product Y).filter (fun p => G.Adj p.1 p.2) =
      (X₁.product Y).filter (fun p => G.Adj p.1 p.2) ∪
      (X₂.product Y).filter (fun p => G.Adj p.1 p.2) := by
    intro X₁ X₂ Y hd
    ext ⟨a, b⟩
    constructor
    · intro h
      have hf := Finset.mem_filter.mp h
      have hp := Finset.mem_product.mp hf.1
      rcases Finset.mem_union.mp hp.1 with ha | ha
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha, hp.2⟩, hf.2⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha, hp.2⟩, hf.2⟩))
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · have hf := Finset.mem_filter.mp h
        have hp := Finset.mem_product.mp hf.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_union.mpr (Or.inl hp.1), hp.2⟩, hf.2⟩
      · have hf := Finset.mem_filter.mp h
        have hp := Finset.mem_product.mp hf.1
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_union.mpr (Or.inr hp.1), hp.2⟩, hf.2⟩
  have hcard_union : ∀ X₁ X₂ Y : Finset V, Disjoint X₁ X₂ →
      (↑(((X₁ ∪ X₂).product Y).filter (fun p => G.Adj p.1 p.2)).card : ℚ) =
      ↑(((X₁.product Y).filter (fun p => G.Adj p.1 p.2)).card) +
      ↑(((X₂.product Y).filter (fun p => G.Adj p.1 p.2)).card) := by
    intro X₁ X₂ Y hd
    rw [heu X₁ X₂ Y hd]
    have hdisj : Disjoint ((X₁.product Y).filter (fun p => G.Adj p.1 p.2))
                           ((X₂.product Y).filter (fun p => G.Adj p.1 p.2)) := by
      apply Finset.disjoint_filter_filter; rw [Finset.disjoint_left]
      intro x h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).1
        (Finset.disjoint_left.mp hd (Finset.mem_product.mp h₁).1)
    exact_mod_cast Finset.card_union_of_disjoint hdisj
  -- The sum e(A₁,B₁) + e(A₁,B₂) + e(A₂,B₁) + e(A₂,B₂) = e(A₁∪A₂, B₁∪B₂)
  have h1 := hmul A₁ B₁; have h2 := hmul A₁ B₂
  have h3 := hmul A₂ B₁; have h4 := hmul A₂ B₂
  have h5 := hmul (A₁ ∪ A₂) (B₁ ∪ B₂)
  -- Apply B-splits
  have hB1 : (↑(((A₁.product (B₁ ∪ B₂)).filter (fun p => G.Adj p.1 p.2)).card) : ℚ) =
      ↑((A₁.product B₁).filter (fun p => G.Adj p.1 p.2)).card +
      ↑((A₁.product B₂).filter (fun p => G.Adj p.1 p.2)).card := by
    have : A₁.product (B₁ ∪ B₂) = (A₁.product B₁) ∪ (A₁.product B₂) := by
      ext ⟨a, b⟩; simp [Finset.mem_product, Finset.mem_union]
    rw [show ((A₁.product (B₁ ∪ B₂)).filter (fun p => G.Adj p.1 p.2)) =
        (A₁.product B₁).filter (fun p => G.Adj p.1 p.2) ∪
        (A₁.product B₂).filter (fun p => G.Adj p.1 p.2) from by
      rw [this, Finset.filter_union]]
    have hd : Disjoint ((A₁.product B₁).filter (fun p => G.Adj p.1 p.2))
                        ((A₁.product B₂).filter (fun p => G.Adj p.1 p.2)) := by
      apply Finset.disjoint_filter_filter; rw [Finset.disjoint_left]
      intro x h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).2
        (Finset.disjoint_left.mp hB (Finset.mem_product.mp h₁).2)
    exact_mod_cast Finset.card_union_of_disjoint hd
  have hB2 : (↑(((A₂.product (B₁ ∪ B₂)).filter (fun p => G.Adj p.1 p.2)).card) : ℚ) =
      ↑((A₂.product B₁).filter (fun p => G.Adj p.1 p.2)).card +
      ↑((A₂.product B₂).filter (fun p => G.Adj p.1 p.2)).card := by
    have : A₂.product (B₁ ∪ B₂) = (A₂.product B₁) ∪ (A₂.product B₂) := by
      ext ⟨a, b⟩; simp [Finset.mem_product, Finset.mem_union]
    rw [show ((A₂.product (B₁ ∪ B₂)).filter (fun p => G.Adj p.1 p.2)) =
        (A₂.product B₁).filter (fun p => G.Adj p.1 p.2) ∪
        (A₂.product B₂).filter (fun p => G.Adj p.1 p.2) from by
      rw [this, Finset.filter_union]]
    have hd : Disjoint ((A₂.product B₁).filter (fun p => G.Adj p.1 p.2))
                        ((A₂.product B₂).filter (fun p => G.Adj p.1 p.2)) := by
      apply Finset.disjoint_filter_filter; rw [Finset.disjoint_left]
      intro x h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).2
        (Finset.disjoint_left.mp hB (Finset.mem_product.mp h₁).2)
    exact_mod_cast Finset.card_union_of_disjoint hd
  -- Now combine: e(A,B) = e(A₁,B) + e(A₂,B) = e(A₁,B₁) + e(A₁,B₂) + e(A₂,B₁) + e(A₂,B₂)
  have hA₁B := hmul A₁ (B₁ ∪ B₂)
  have hA₂B := hmul A₂ (B₁ ∪ B₂)
  have hcA := hcard_union A₁ A₂ (B₁ ∪ B₂) hA
  have hcardA : (A₁ ∪ A₂).card = A₁.card + A₂.card := Finset.card_union_of_disjoint hA
  have hcardB : (B₁ ∪ B₂).card = B₁.card + B₂.card := Finset.card_union_of_disjoint hB
  rw [hcardA, hcardB] at h5
  push_cast at h5 hA₁B hA₂B ⊢
  linarith [hcA, hA₁B, hA₂B, hB1, hB2, h1, h2, h3, h4, h5]

/-- Delta decomposition identity: the 4-subpair energy excess equals the sum of
    squared density deviations from d(A,B).
    Σᵢⱼ |Aᵢ||Bⱼ|*dᵢⱼ² - |A||B|*d² = Σᵢⱼ |Aᵢ||Bⱼ|*(dᵢⱼ - d)²
    (Here d = d(A,B) is the overall density of A₁∪A₂ vs B₁∪B₂.) -/
theorem four_subpair_deviation_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B₁ B₂ : Finset V) (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    let d := edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)
    (A₁.card : ℚ) * B₁.card * (edgeDensity G A₁ B₁) ^ 2 +
    (A₁.card : ℚ) * B₂.card * (edgeDensity G A₁ B₂) ^ 2 +
    (A₂.card : ℚ) * B₁.card * (edgeDensity G A₂ B₁) ^ 2 +
    (A₂.card : ℚ) * B₂.card * (edgeDensity G A₂ B₂) ^ 2 -
    ((A₁.card + A₂.card) : ℚ) * (B₁.card + B₂.card) * d ^ 2 =
    (A₁.card : ℚ) * B₁.card * (edgeDensity G A₁ B₁ - d) ^ 2 +
    (A₁.card : ℚ) * B₂.card * (edgeDensity G A₁ B₂ - d) ^ 2 +
    (A₂.card : ℚ) * B₁.card * (edgeDensity G A₂ B₁ - d) ^ 2 +
    (A₂.card : ℚ) * B₂.card * (edgeDensity G A₂ B₂ - d) ^ 2 := by
  set d := edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)
  set d₁₁ := edgeDensity G A₁ B₁; set d₁₂ := edgeDensity G A₁ B₂
  set d₂₁ := edgeDensity G A₂ B₁; set d₂₂ := edgeDensity G A₂ B₂
  set a₁ : ℚ := ↑A₁.card; set a₂ : ℚ := ↑A₂.card
  set b₁ : ℚ := ↑B₁.card; set b₂ : ℚ := ↑B₂.card
  have hS := four_subpair_edge_count_identity G A₁ A₂ B₁ B₂ hA hB
  -- LHS - RHS = 2*d*(Σᵢⱼ aᵢbⱼdᵢⱼ - (a₁+a₂)(b₁+b₂)*d) = 0 by the weighted average hS
  push_cast at hS ⊢
  linear_combination (2 * d) * hS

/-- Lower bound on the 4-subpair energy excess:
    The excess of the 4-subpair energy over the original pair energy is at least
    |A₁||B₁| × (d(A₁,B₁) - d(A,B))², the contribution of the (A₁,B₁) deviation term. -/
theorem four_subpair_excess_lb (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B₁ B₂ : Finset V) (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    let d := edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)
    (A₁.card : ℚ) * B₁.card * (edgeDensity G A₁ B₁) ^ 2 +
    (A₁.card : ℚ) * B₂.card * (edgeDensity G A₁ B₂) ^ 2 +
    (A₂.card : ℚ) * B₁.card * (edgeDensity G A₂ B₁) ^ 2 +
    (A₂.card : ℚ) * B₂.card * (edgeDensity G A₂ B₂) ^ 2 -
    ((A₁.card + A₂.card) : ℚ) * (B₁.card + B₂.card) * d ^ 2 ≥
    (A₁.card : ℚ) * B₁.card * (edgeDensity G A₁ B₁ - d) ^ 2 := by
  simp only
  rw [four_subpair_deviation_identity G A₁ A₂ B₁ B₂ hA hB]
  have h12 : (0 : ℚ) ≤ (A₁.card : ℚ) * B₂.card *
      (edgeDensity G A₁ B₂ - edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)) ^ 2 := by positivity
  have h21 : (0 : ℚ) ≤ (A₂.card : ℚ) * B₁.card *
      (edgeDensity G A₂ B₁ - edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)) ^ 2 := by positivity
  have h22 : (0 : ℚ) ≤ (A₂.card : ℚ) * B₂.card *
      (edgeDensity G A₂ B₂ - edgeDensity G (A₁ ∪ A₂) (B₁ ∪ B₂)) ^ 2 := by positivity
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: BLOCK-DECOMPOSITION PACKAGING LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy increment packaging** — block-decomposition core lemma.

    Shows that replacing {A, B} in a partition by the 4-piece refinement
    {A', A\A', B', B\B'} (where A' and B' are irregular witnesses) increases
    partitionEnergy by at least eps^6.

    This is the "Finset sum packaging" step that was left as sorry in the
    main theorem.  It does NOT require A\A' or B\B' to be nonempty; instead
    it uses `hparts_nonempty` (every part has positive card) to rule out the
    pathological case where A₂ = A\A' = ∅ could appear inside S. -/
theorem energy_increment_packaging
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (parts : Finset (Finset V))
    (hparts_disj : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (hparts_nonempty : ∀ P ∈ parts, 0 < P.card)
    (A B : Finset V) (hA : A ∈ parts) (hB : B ∈ parts) (hAB : A ≠ B)
    (A' B' : Finset V)
    (hA'sub : A' ⊆ A) (hB'sub : B' ⊆ B)
    (hAd : Disjoint A' (A \ A')) (hBd : Disjoint B' (B \ B'))
    (hAu : A' ∪ (A \ A') = A) (hBu : B' ∪ (B \ B') = B)
    (hA'pos : 0 < A'.card)
    (hB'pos : 0 < B'.card)
    (hcore : (A'.card : ℚ) * B'.card *
             (edgeDensity G A' B' - edgeDensity G A B) ^ 2 >
             eps ^ 6 * (Fintype.card V : ℚ) ^ 2) :
    let A₂ := A \ A'; let B₂ := B \ B'
    let S := (parts.erase B).erase A
    partitionEnergy G (S ∪ {A', A₂, B', B₂}) ≥
      partitionEnergy G parts + eps ^ 6 := by
  intro A₂ B₂ S

  -- ── n > 0 ────────────────────────────────────────────────────────
  have hn_pos : (0 : ℚ) < Fintype.card V := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with hV | hV
    · exact absurd (Nat.le_zero.mp ((Finset.card_le_univ A').trans hV.le) ▸ hA'pos)
        (lt_irrefl 0)
    · exact_mod_cast hV
  have hn : (Fintype.card V : ℚ) ≠ 0 := ne_of_gt hn_pos

  -- ── S ∪ {A, B} = parts ──────────────────────────────────────────
  have hSAB : S ∪ ({A, B} : Finset (Finset V)) = parts := by
    ext X; constructor
    · intro hX
      rcases Finset.mem_union.mp hX with hXS | hXAB
      · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hXAB
        rcases hXAB with hXeqA | hXeqB
        · exact hXeqA ▸ hA
        · exact hXeqB ▸ hB
    · intro hXparts
      rw [Finset.mem_union]
      by_cases hXA : X = A
      · exact Or.inr (Finset.mem_insert.mpr (Or.inl hXA))
      · by_cases hXB : X = B
        · exact Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hXB)))
        · exact Or.inl
            (Finset.mem_erase.mpr ⟨hXA, Finset.mem_erase.mpr ⟨hXB, hXparts⟩⟩)

  -- ── Disjoint S {A, B} ───────────────────────────────────────────
  have hSAB_disj : Disjoint S ({A, B} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXAB
    have hXneA : X ≠ A := (Finset.mem_erase.mp hXS).1
    have hXneB : X ≠ B := (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXAB
    rcases hXAB with hXeqA | hXeqB
    · exact hXneA hXeqA
    · exact hXneB hXeqB

  -- ── ne facts: A₂ ≠ A, B₂ ≠ B ─────────────────────────────────────
  -- A₂ ≠ A: if A₂ = A then A ⊆ A₂ = A\A', so A'=∅ contradicting hA'pos
  have hA₂neA : A₂ ≠ A := fun heq => by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact absurd hx (Finset.mem_sdiff.mp (heq ▸ hA'sub hx)).2
  -- B₂ ≠ B: symmetric
  have hB₂neB : B₂ ≠ B := fun heq => by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
    exact absurd hx (Finset.mem_sdiff.mp (heq ▸ hB'sub hx)).2

  -- ── Disjoint S {A', A₂, B', B₂} ────────────────────────────────
  -- Each of A', A₂, B', B₂ is a subset of A or B.
  -- Any X ∈ S that equals one of these would be in parts (via S ⊆ parts),
  -- so it has X.card > 0 (by hparts_nonempty), and X ⊆ A (or B) while
  -- X ≠ A (or B), giving Disjoint X A — contradicting X ⊆ A with X.card > 0.
  have hST_disj : Disjoint S ({A', A₂, B', B₂} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXT
    have hXparts : X ∈ parts :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).2
    -- X is a part, so X.card > 0
    have hXpos : 0 < X.card := hparts_nonempty X hXparts
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXT
    rcases hXT with hXA' | hXA₂ | hXB' | hXB₂
    · -- X = A' ⊆ A, A' ∈ parts, A' ≠ A → Disjoint X A, but X ⊆ A → ↯
      rw [hXA'] at hXpos hXparts
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hXpos
      exact absurd (hA'sub hx)
        (Finset.disjoint_left.mp (hparts_disj A' A hXparts hA
          (hXA' ▸ (Finset.mem_erase.mp hXS).1)) hx)
    · -- X = A₂: X.card > 0 (from hXpos rewritten via hXA₂), so ∃ x ∈ A₂
      rw [hXA₂] at hXpos hXparts
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hXpos
      exact absurd (Finset.mem_sdiff.mp hx).1
        (Finset.disjoint_left.mp (hparts_disj A₂ A hXparts hA hA₂neA) hx)
    · -- X = B' ⊆ B → same with B
      rw [hXB'] at hXpos hXparts
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hXpos
      exact absurd (hB'sub hx)
        (Finset.disjoint_left.mp (hparts_disj B' B hXparts hB
          (hXB' ▸ (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).1)) hx)
    · -- X = B₂ = B \ B' ⊆ B → same
      rw [hXB₂] at hXpos hXparts
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hXpos
      exact absurd (Finset.mem_sdiff.mp hx).1
        (Finset.disjoint_left.mp (hparts_disj B₂ B hXparts hB hB₂neB) hx)

  -- ── Card facts ───────────────────────────────────────────────────
  have hcard_A : A'.card + (A \ A').card = A.card := by
    have h := Finset.card_union_of_disjoint hAd; rw [hAu] at h; omega
  have hcard_B : B'.card + (B \ B').card = B.card := by
    have h := Finset.card_union_of_disjoint hBd; rw [hBu] at h; omega

  -- ── Rewrite: energy(parts) = energy(S ∪ {A,B}) ──────────────────
  rw [← hSAB]

  -- ── Additional distinctness facts ────────────────────────────────
  have hAB_disj : Disjoint A B := hparts_disj A B hA hB hAB
  have hA'A₂_ne : A' ≠ A₂ := by
    intro heq
    have hself : Disjoint A' A' := hAd.mono_right (le_of_eq heq)
    have h1 := Finset.card_union_of_disjoint hself
    rw [Finset.union_self] at h1; omega
  have hB'B₂_ne : B' ≠ B₂ := by
    intro heq
    have hself : Disjoint B' B' := hBd.mono_right (le_of_eq heq)
    have h1 := Finset.card_union_of_disjoint hself
    rw [Finset.union_self] at h1; omega
  have hA'B'_ne : A' ≠ B' := by
    intro h; obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact absurd (hB'sub (h ▸ hx)) (Finset.disjoint_left.mp hAB_disj (hA'sub hx))
  have hA'B₂_ne : A' ≠ B₂ := by
    intro h; obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact absurd (Finset.mem_sdiff.mp (h ▸ hx)).1
      (Finset.disjoint_left.mp hAB_disj (hA'sub hx))
  -- A₂ ≠ B': if A₂ = B' then A₂ ⊆ A ∩ B = ∅, but B'.card > 0
  have hA₂B'_ne : A₂ ≠ B' := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
    exact absurd (hB'sub hx)
      (Finset.disjoint_left.mp hAB_disj (Finset.sdiff_subset (heq ▸ hx)))
  -- A₂ ≠ B₂: if A₂ = B₂ then A₂ ⊆ A ∩ B = ∅, so A₂ = ∅ = B₂,
  --   hence A' = A and B' = B, giving d(A',B') = d(A,B), contradicting hcore > 0
  have hA₂B₂_ne : A₂ ≠ B₂ := by
    intro heq
    have hA₂_empty : A₂ = ∅ := by
      ext x; simp only [Finset.mem_empty_iff_false, iff_false]
      intro hxA₂
      exact absurd (Finset.sdiff_subset (heq ▸ hxA₂))
        (Finset.disjoint_left.mp hAB_disj (Finset.sdiff_subset hxA₂))
    have hA₂z : A₂.card = 0 := Finset.card_eq_zero.mpr hA₂_empty
    have hAcard_eq : A'.card = A.card := by
      have h : A'.card + A₂.card = A.card := by
        have := Finset.card_union_of_disjoint hAd; rw [hAu] at this; omega
      omega
    have hA'eq : A' = A := Finset.eq_of_subset_of_card_le hA'sub hAcard_eq.symm.le
    have hB₂_empty : B₂ = ∅ := heq.symm.trans hA₂_empty
    have hB₂z : B₂.card = 0 := Finset.card_eq_zero.mpr hB₂_empty
    have hBcard_eq : B'.card = B.card := by
      have h : B'.card + B₂.card = B.card := by
        have := Finset.card_union_of_disjoint hBd; rw [hBu] at this; omega
      omega
    have hB'eq : B' = B := Finset.eq_of_subset_of_card_le hB'sub hBcard_eq.symm.le
    have hzero : (A'.card : ℚ) * B'.card *
        (edgeDensity G A' B' - edgeDensity G A B) ^ 2 = 0 := by
      rw [hA'eq, hB'eq, sub_self]; ring
    linarith [hcore, mul_pos (pow_pos heps 6) (pow_pos hn_pos 2)]
  -- Non-membership for sum expansion of T = {A', A₂, B', B₂}
  have hA'_nm : A' ∉ ({A₂, B', B₂} : Finset (Finset V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hA'A₂_ne (fun h => h.elim hA'B'_ne hA'B₂_ne)
  have hA₂_nm : A₂ ∉ ({B', B₂} : Finset (Finset V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hA₂B'_ne hA₂B₂_ne
  have hB'_nm : B' ∉ ({B₂} : Finset (Finset V)) := by
    simp only [Finset.mem_singleton]; exact hB'B₂_ne
  have hA_nm : A ∉ ({B} : Finset (Finset V)) := by
    simp only [Finset.mem_singleton]; exact hAB

  -- ── Term function ef P Q = |P|·|Q|/n² · d(P,Q)² ─────────────────
  let ef : Finset V → Finset V → ℚ := fun P Q =>
    (P.card : ℚ) * Q.card / (Fintype.card V : ℚ) ^ 2 * (edgeDensity G P Q) ^ 2
  have ef_def : ∀ P Q : Finset V, ef P Q =
      ↑P.card * ↑Q.card / ↑(Fintype.card V) ^ 2 * (edgeDensity G P Q) ^ 2 :=
    fun _ _ => rfl

  -- ── Unfold partitionEnergy to nested double sums ──────────────────
  have pe_eq : ∀ R : Finset (Finset V),
      partitionEnergy G R = R.sum (fun P => R.sum (fun Q => ef P Q)) := by
    intro R
    unfold partitionEnergy
    simp only [if_neg hn]
    rw [show R.product R = R ×ˢ R from rfl, Finset.sum_product]
  simp only [pe_eq]

  -- ── Block decomposition helper ────────────────────────────────────
  have block_split : ∀ (X Y : Finset (Finset V)) (hd : Disjoint X Y),
      ∑ P ∈ X ∪ Y, ∑ Q ∈ X ∪ Y, ef P Q =
      (∑ P ∈ X, ∑ Q ∈ X, ef P Q) + (∑ P ∈ X, ∑ Q ∈ Y, ef P Q) +
      ((∑ P ∈ Y, ∑ Q ∈ X, ef P Q) + ∑ P ∈ Y, ∑ Q ∈ Y, ef P Q) := by
    intro X Y hd
    rw [Finset.sum_union hd]
    have split_inner : ∀ P, ∑ Q ∈ X ∪ Y, ef P Q = ∑ Q ∈ X, ef P Q + ∑ Q ∈ Y, ef P Q :=
      fun P => Finset.sum_union hd
    simp_rw [split_inner, Finset.sum_add_distrib]

  rw [block_split _ _ hST_disj, block_split _ _ hSAB_disj]

  -- ── Reduce to: ST + TS + TT ≥ SAB + ABS + ABAB + eps^6 ──────────
  suffices key :
      (∑ P ∈ S, ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q) +
      ((∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ∑ Q ∈ S, ef P Q) +
       ∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)),
         ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q) ≥
      (∑ P ∈ S, ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q) +
      ((∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ S, ef P Q) +
       ∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q) +
      eps ^ 6 by linarith

  -- ── ST ≥ SAB ─────────────────────────────────────────────────────
  have hST : ∑ P ∈ S, ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q ≥
      ∑ P ∈ S, ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q := by
    apply Finset.sum_le_sum; intro P _
    simp only [Finset.sum_insert hA'_nm, Finset.sum_insert hA₂_nm,
               Finset.sum_insert hB'_nm, Finset.sum_singleton,
               Finset.sum_insert hA_nm, Finset.sum_singleton]
    have hcA := density_sq_convex_right G P A' A₂ hAd
    have hcB := density_sq_convex_right G P B' B₂ hBd
    have hAcard : (A'.card : ℚ) + A₂.card = A.card := by exact_mod_cast hcard_A
    have hBcard : (B'.card : ℚ) + B₂.card = B.card := by exact_mod_cast hcard_B
    have hPnn : (0 : ℚ) ≤ (P.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
    push_cast at hcA hcB
    simp only [ef_def]
    push_cast
    rw [← hAcard, ← hBcard, ← hAu, ← hBu]
    have h1 := mul_le_mul_of_nonneg_left hcA hPnn
    have h2 := mul_le_mul_of_nonneg_left hcB hPnn
    ring_nf at h1 h2 ⊢; linarith

  -- ── TS ≥ ABS ─────────────────────────────────────────────────────
  have hTS : ∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ∑ Q ∈ S, ef P Q ≥
      ∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ S, ef P Q := by
    simp only [Finset.sum_insert hA'_nm, Finset.sum_insert hA₂_nm,
               Finset.sum_insert hB'_nm, Finset.sum_singleton,
               Finset.sum_insert hA_nm, Finset.sum_singleton]
    have hA_rows : (∑ Q ∈ S, ef A' Q) + (∑ Q ∈ S, ef A₂ Q) ≥ ∑ Q ∈ S, ef A Q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro Q _
      have hcA := density_sq_convex G A' A₂ Q hAd
      have hAcard : (A'.card : ℚ) + A₂.card = A.card := by exact_mod_cast hcard_A
      simp only [ef_def]; push_cast
      rw [← hAcard, ← hAu]
      have hQnn : (0 : ℚ) ≤ (Q.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
      have h := mul_le_mul_of_nonneg_left hcA hQnn
      ring_nf at h ⊢; linarith
    have hB_rows : (∑ Q ∈ S, ef B' Q) + (∑ Q ∈ S, ef B₂ Q) ≥ ∑ Q ∈ S, ef B Q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro Q _
      have hcB := density_sq_convex G B' B₂ Q hBd
      have hBcard : (B'.card : ℚ) + B₂.card = B.card := by exact_mod_cast hcard_B
      simp only [ef_def]; push_cast
      rw [← hBcard, ← hBu]
      have hQnn : (0 : ℚ) ≤ (Q.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
      have h := mul_le_mul_of_nonneg_left hcB hQnn
      ring_nf at h ⊢; linarith
    linarith [hA_rows, hB_rows]

  -- ── TT ≥ ABAB + eps^6 ────────────────────────────────────────────
  have hTT : ∑ P ∈ ({A', A₂, B', B₂} : Finset (Finset V)),
        ∑ Q ∈ ({A', A₂, B', B₂} : Finset (Finset V)), ef P Q ≥
      ∑ P ∈ ({A, B} : Finset (Finset V)), ∑ Q ∈ ({A, B} : Finset (Finset V)), ef P Q +
      eps ^ 6 := by
    simp only [Finset.sum_insert hA'_nm, Finset.sum_insert hA₂_nm,
               Finset.sum_insert hB'_nm, Finset.sum_singleton,
               Finset.sum_insert hA_nm, Finset.sum_singleton]
    have hAcard : (A'.card : ℚ) + A₂.card = A.card := by exact_mod_cast hcard_A
    have hBcard : (B'.card : ℚ) + B₂.card = B.card := by exact_mod_cast hcard_B
    have hsub_AA := sub4pair_energy_lower_bound G A' A₂ A' A₂ hAd hAd
    have hsub_AB_lb := four_subpair_excess_lb G A' A₂ B' B₂ hAd hBd
    have hsub_BA := sub4pair_energy_lower_bound G B' B₂ A' A₂ hBd hAd
    have hsub_BB := sub4pair_energy_lower_bound G B' B₂ B' B₂ hBd hBd
    simp only [ef_def]; push_cast
    rw [← hAu, ← hBu, ← hAcard, ← hBcard] at *
    -- Scale sub4pair bounds by 1/n² to match ef terms
    have hs : (0 : ℚ) ≤ 1 / (Fintype.card V : ℚ) ^ 2 := by positivity
    have hn2_pos : (0 : ℚ) < (Fintype.card V : ℚ) ^ 2 := by positivity
    have hAA_s := mul_le_mul_of_nonneg_right hsub_AA hs
    have hAB_s := mul_le_mul_of_nonneg_right hsub_AB_lb hs
    have hBA_s := mul_le_mul_of_nonneg_right hsub_BA hs
    have hBB_s := mul_le_mul_of_nonneg_right hsub_BB hs
    have hcore_s : ↑A'.card * ↑B'.card *
        (edgeDensity G A' B' - edgeDensity G (A' ∪ A₂) (B' ∪ B₂)) ^ 2 /
        (Fintype.card V : ℚ) ^ 2 > eps ^ 6 := by
      have h_num_pos : ↑A'.card * ↑B'.card *
          (edgeDensity G A' B' - edgeDensity G (A' ∪ A₂) (B' ∪ B₂)) ^ 2 -
          eps ^ 6 * (Fintype.card V : ℚ) ^ 2 > 0 := by linarith [hcore]
      have h_eq : (↑A'.card * ↑B'.card *
          (edgeDensity G A' B' - edgeDensity G (A' ∪ A₂) (B' ∪ B₂)) ^ 2 -
          eps ^ 6 * (Fintype.card V : ℚ) ^ 2) / (Fintype.card V : ℚ) ^ 2 =
          ↑A'.card * ↑B'.card *
          (edgeDensity G A' B' - edgeDensity G (A' ∪ A₂) (B' ∪ B₂)) ^ 2 /
          (Fintype.card V : ℚ) ^ 2 - eps ^ 6 := by field_simp
      linarith [div_pos h_num_pos hn2_pos, h_eq]
    ring_nf at hAA_s hAB_s hBA_s hBB_s hcore_s ⊢
    linarith [hAA_s, hAB_s, hBA_s, hBB_s, hcore_s]

  linarith [hST, hTS, hTT]

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: MAIN ENERGY INCREMENT THEOREM
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy Increment Lemma (OQ-01)** — Corrected bound ε^6:
    For an irregular pair (A, B) in an ε-equipartition, splitting (A,B) via
    the irregular witnesses increases partitionEnergy by at least ε^6.

    **Complete proof strategy**:
    Let S = parts \ {A,B}, T = {A', A\A', B', B\B'} (the 4 refined sets).
    The refined partition is P' = S ∪ T.

    Decompose both energies into blocks using Finset.sum_union:
      partitionEnergy G parts  = Σ_{S×S} + Σ_{S×{A,B}} + Σ_{{A,B}×S} + Σ_{{A,B}×{A,B}}
      partitionEnergy G parts' = Σ_{S×S} + Σ_{S×T}     + Σ_{T×S}     + Σ_{T×T}

    Block comparisons (each contributes ≥ 0 to the increment):
    (1) S×S: identical in both — zero increment
    (2) S×T ≥ S×{A,B}: for each C ∈ S, split A→{A',A₂} gives ≥ 0 by density_sq_convex,
        and split B→{B',B₂} also gives ≥ 0 by density_sq_convex_right
    (3) T×S ≥ {A,B}×S: same by symmetry
    (4) T×T ≥ {A,B}×{A,B} + eps^6:
        excess ≥ 2/n² * |A'||B'| * (d(A',B') - d(A,B))²   (four_subpair_excess_lb)
        > 2/n² * ε²n * ε²n * ε²                             (equipartition + irregularity)
        = 2 * eps^6 > eps^6

    All steps are now proved in `energy_increment_packaging` above;
    this theorem assembles the result and derives the necessary preconditions. -/
theorem energy_increment_step
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (parts : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ parts, v ∈ P)
    (hdisjoint : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q)
    (A B : Finset V) (hA : A ∈ parts) (hB : B ∈ parts) (hAB : A ≠ B)
    (hirr : ¬IsEpsilonRegular G eps A B)
    (hpart_size : ∀ P ∈ parts, (P.card : ℚ) ≥ eps * Fintype.card V) :
    ∃ parts' : Finset (Finset V),
      partitionEnergy G parts' ≥ partitionEnergy G parts + eps ^ 6 := by
  obtain ⟨A', B', hA'sub, hB'sub, hcA', hcB', hd⟩ := exists_irregular_witness G eps A B hirr
  let A₂ := A \ A'; let B₂ := B \ B'
  -- Disjointness: A' ∩ (A\A') = ∅ and B' ∩ (B\B') = ∅
  have hAd : Disjoint A' A₂ := by
    apply Finset.disjoint_left.mpr
    intro a ha₁ ha₂
    exact absurd ha₁ (Finset.mem_sdiff.mp ha₂).2
  have hBd : Disjoint B' B₂ := by
    apply Finset.disjoint_left.mpr
    intro b hb₁ hb₂
    exact absurd hb₁ (Finset.mem_sdiff.mp hb₂).2
  -- Union recovery: A' ∪ (A\A') = A and B' ∪ (B\B') = B
  have hAu : A' ∪ A₂ = A := Finset.union_sdiff_of_subset hA'sub
  have hBu : B' ∪ B₂ = B := Finset.union_sdiff_of_subset hB'sub
  -- V is non-empty: hd says |d(A',B') - d(A,B)| > eps > 0
  have hVpos : (0 : ℚ) < Fintype.card V := by
    by_contra h; push_neg at h
    have hVz : Fintype.card V = 0 := le_antisymm (by exact_mod_cast h) (Nat.zero_le _)
    have hall : ∀ S : Finset V, S = ∅ :=
      fun S => Finset.card_eq_zero.mp
        (Nat.le_zero.mp ((Finset.card_le_univ S).trans hVz.le))
    have hd0 : edgeDensity G A' B' = 0 := by
      rw [show A' = ∅ from hall A']; unfold edgeDensity; simp
    have hd1 : edgeDensity G A B = 0 := by
      rw [show A = ∅ from hall A]; unfold edgeDensity; simp
    rw [hd0, hd1, sub_self, abs_zero] at hd; linarith
  -- Core quantitative bound: |A'|*|B'|*(d(A',B')-d(A,B))² > eps^6 * n²
  have hcore : (A'.card : ℚ) * B'.card * (edgeDensity G A' B' - edgeDensity G A B) ^ 2 >
      eps ^ 6 * (Fintype.card V : ℚ) ^ 2 := by
    have hA'n : (A'.card : ℚ) ≥ eps ^ 2 * Fintype.card V :=
      calc (A'.card : ℚ) ≥ eps * A.card := hcA'
        _ ≥ eps * (eps * Fintype.card V) := by nlinarith [hpart_size A hA]
        _ = eps ^ 2 * Fintype.card V := by ring
    have hB'n : (B'.card : ℚ) ≥ eps ^ 2 * Fintype.card V :=
      calc (B'.card : ℚ) ≥ eps * B.card := hcB'
        _ ≥ eps * (eps * Fintype.card V) := by nlinarith [hpart_size B hB]
        _ = eps ^ 2 * Fintype.card V := by ring
    have hdev : (edgeDensity G A' B' - edgeDensity G A B) ^ 2 > eps ^ 2 := by
      nlinarith [sq_abs (edgeDensity G A' B' - edgeDensity G A B),
                 abs_nonneg (edgeDensity G A' B' - edgeDensity G A B)]
    have hnn : (0 : ℚ) ≤ eps ^ 2 * Fintype.card V := by positivity
    have h1 : (A'.card : ℚ) * B'.card ≥ (eps ^ 2 * Fintype.card V) ^ 2 :=
      calc (A'.card : ℚ) * B'.card
          ≥ eps ^ 2 * Fintype.card V * B'.card := by
              nlinarith [Nat.cast_nonneg (α := ℚ) B'.card]
        _ ≥ eps ^ 2 * Fintype.card V * (eps ^ 2 * Fintype.card V) := by nlinarith
        _ = (eps ^ 2 * Fintype.card V) ^ 2 := by ring
    have h2 : (0 : ℚ) < (eps ^ 2 * Fintype.card V) ^ 2 := by positivity
    have hstep1 : (A'.card : ℚ) * B'.card * (edgeDensity G A' B' - edgeDensity G A B) ^ 2 ≥
        (eps ^ 2 * Fintype.card V) ^ 2 *
          (edgeDensity G A' B' - edgeDensity G A B) ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hstep2 : (eps ^ 2 * Fintype.card V) ^ 2 * (edgeDensity G A' B' - edgeDensity G A B) ^ 2 >
        (eps ^ 2 * Fintype.card V) ^ 2 * eps ^ 2 :=
      mul_lt_mul_of_pos_left hdev h2
    have hstep3 : (eps ^ 2 * (Fintype.card V : ℚ)) ^ 2 * eps ^ 2 =
        eps ^ 6 * (Fintype.card V : ℚ) ^ 2 := by ring
    linarith
  -- The refined partition P' = (parts \ {A,B}) ∪ {A', A\A', B', B\B'}
  -- witnesses the energy increment.
  -- Derive preconditions for energy_increment_packaging
  have hparts_nonempty : ∀ P ∈ parts, 0 < P.card := by
    intro P hP
    have h := hpart_size P hP
    exact Nat.pos_of_ne_zero (by
      intro h0
      have : (P.card : ℚ) = 0 := by exact_mod_cast h0
      linarith [mul_pos heps hVpos])
  have hA'pos : 0 < A'.card := by
    by_contra h0; push_neg at h0
    have heq : (A'.card : ℚ) = 0 := by exact_mod_cast Nat.le_zero.mp h0
    have hcontra : (0 : ℚ) > eps ^ 6 * ↑(Fintype.card V) ^ 2 :=
      calc (0 : ℚ)
          = ↑A'.card * ↑B'.card * (edgeDensity G A' B' - edgeDensity G A B) ^ 2 := by
            rw [heq]; ring
        _ > eps ^ 6 * ↑(Fintype.card V) ^ 2 := hcore
    linarith [mul_pos (pow_pos heps 6) (pow_pos hVpos 2)]
  have hB'pos : 0 < B'.card := by
    by_contra h0; push_neg at h0
    have heq : (B'.card : ℚ) = 0 := by exact_mod_cast Nat.le_zero.mp h0
    have hcontra : (0 : ℚ) > eps ^ 6 * ↑(Fintype.card V) ^ 2 :=
      calc (0 : ℚ)
          = ↑A'.card * ↑B'.card * (edgeDensity G A' B' - edgeDensity G A B) ^ 2 := by
            rw [heq]; ring
        _ > eps ^ 6 * ↑(Fintype.card V) ^ 2 := hcore
    linarith [mul_pos (pow_pos heps 6) (pow_pos hVpos 2)]
  exact ⟨(parts.erase B).erase A ∪ {A', A₂, B', B₂},
    energy_increment_packaging G eps heps parts hdisjoint hparts_nonempty
      A B hA hB hAB A' B' hA'sub hB'sub hAd hBd hAu hBu hA'pos hB'pos hcore⟩

end Szemeredi.EnergyIncrement
