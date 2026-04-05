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
  8. energy_increment_step: main theorem (sorry for Finset sum packaging)

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
-- PART VI: MAIN ENERGY INCREMENT THEOREM
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

    **Current sorry**: Step (4) requires Finset sum decomposition using
    Finset.sum_union, product distributivity, and disjointness checks.
    The algebraic core (four_subpair_excess_lb + hcore) is fully proved below. -/
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
  exact ⟨(parts.erase B).erase A ∪ {A', A₂, B', B₂}, by
    sorry⟩

end Szemeredi.EnergyIncrement
