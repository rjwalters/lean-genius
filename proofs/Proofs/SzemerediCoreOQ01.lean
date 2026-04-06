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
  8. energy_increment_step: main theorem (Finset sum packaging)

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

    **Proof**: Block decomposition of partition energy sums via
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
  --
  -- ═══════════════════════════════════════════════════════════════════
  -- PROOF STRATEGY: Block decomposition of partition energy sums.
  --
  -- Let S = parts \ {A,B}, T = {A',A₂,B',B₂}, AB = {A,B}.
  -- parts = S ∪ AB, parts' = S ∪ T.
  --
  -- Decompose both energies into 4 blocks (using Finset.sum_product'):
  --   energy(S ∪ X) = Σ_{S×S} + Σ_{S×X} + Σ_{X×S} + Σ_{X×X}
  --
  -- Block comparisons:
  --   S×S:  identical (cancel)
  --   S×T ≥ S×AB:  density_sq_convex_right per row
  --   T×S ≥ AB×S:  by edgeDensity_symm + density_sq_convex
  --   T×T ≥ AB×AB + eps^6:  four_subpair_excess_lb + hcore
  -- ═══════════════════════════════════════════════════════════════════

  refine ⟨(parts.erase B).erase A ∪ {A', A₂, B', B₂}, ?_⟩

  -- ── Abbreviations ──────────────────────────────────────────────────
  set S := (parts.erase B).erase A with hS_def
  set n : ℚ := ↑(Fintype.card V) with hn_def
  have hn : n ≠ 0 := ne_of_gt hVpos
  have hn2_pos : (0 : ℚ) < n ^ 2 := by positivity

  -- ── Disjoint A B ──────────────────────────────────────────────────
  have hABdisj : Disjoint A B := hdisjoint A B hA hB hAB

  -- ── Positivity of witness cardinalities ────────────────────────────
  have hA'pos : 0 < A'.card := by
    have h : (A'.card : ℚ) > 0 := calc
      (A'.card : ℚ) ≥ eps * A.card := hcA'
      _ ≥ eps * (eps * Fintype.card V) := by nlinarith [hpart_size A hA]
      _ > 0 := by positivity
    exact Nat.pos_of_ne_zero (fun heq => by simp [heq] at h)
  have hB'pos : 0 < B'.card := by
    have h : (B'.card : ℚ) > 0 := calc
      (B'.card : ℚ) ≥ eps * B.card := hcB'
      _ ≥ eps * (eps * Fintype.card V) := by nlinarith [hpart_size B hB]
      _ > 0 := by positivity
    exact Nat.pos_of_ne_zero (fun heq => by simp [heq] at h)

  -- ── S ∪ {A, B} = parts ────────────────────────────────────────────
  have hSAB_eq : S ∪ ({A, B} : Finset (Finset V)) = parts := by
    ext X; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]
    constructor
    · rintro (⟨hXneA, hXneB, hXp⟩ | rfl | rfl) <;> [exact hXp; exact hA; exact hB]
    · intro hXp
      by_cases hXA : X = A
      · exact Or.inr (Or.inl hXA)
      · by_cases hXB : X = B
        · exact Or.inr (Or.inr hXB)
        · exact Or.inl ⟨hXA, hXB, hXp⟩

  -- ── Disjoint S {A, B} ─────────────────────────────────────────────
  have hSAB_disj : Disjoint S ({A, B} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXAB
    simp only [Finset.mem_erase] at hXS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXAB
    rcases hXAB with rfl | rfl
    · exact hXS.1 rfl
    · exact hXS.2.1 rfl

  -- ── Disjoint S {A', A₂, B', B₂} ──────────────────────────────────
  -- Each element of T is a subset of A or B. If any were also in S (hence
  -- in parts, ≠ A, ≠ B), partition disjointness forces it to be ∅, but
  -- all parts have positive cardinality.
  have hST_disj : Disjoint S ({A', A₂, B', B₂} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXT
    have hXp : X ∈ parts :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).2
    have hXneA : X ≠ A := (Finset.mem_erase.mp hXS).1
    have hXneB : X ≠ B :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXT
    -- Helper: if X ∈ parts, X ≠ P, X ⊆ P, then X = ∅ → contradiction with hpart_size
    have aux : ∀ P : Finset V, P ∈ parts → X ≠ P → X ⊆ P → False := by
      intro P hPp hXneP hXsub
      -- Disjoint X P (both in parts, distinct)
      have hd := hdisjoint X P hXp hPp hXneP
      -- X ⊆ P and Disjoint X P → X = ∅
      have hXe : X = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr
        (fun x hx => absurd (hXsub hx) (Finset.disjoint_left.mp hd hx))
      -- But X ∈ parts with card ≥ eps * n > 0
      have := hpart_size X hXp; rw [hXe] at this; simp at this; linarith
    rcases hXT with rfl | rfl | rfl | rfl
    -- X = A': either A' = A (then hXneA contradicts) or A' ⊊ A → contradiction via aux
    · exact if h : A' = A then absurd h hXneA else aux A hA h hA'sub
    -- X = A₂ = A\A': A₂ ⊆ A, and A₂ ≠ A (since A' is nonempty)
    · have hA₂neA : A₂ ≠ A := by
        intro heq; have ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
        exact absurd (hA'sub hx) ((show A₂ = A from heq) ▸ (Finset.mem_sdiff.mp
          (show x ∈ A₂ from by rw [heq]; exact hA'sub hx))).2
      exact if h : A₂ = A then absurd h hXneA else aux A hA hXneA Finset.sdiff_subset
    -- X = B': same as A' case but for B
    · exact if h : B' = B then absurd h hXneB else aux B hB h hB'sub
    -- X = B₂ = B\B'
    · exact aux B hB hXneB Finset.sdiff_subset

  -- ── Rewrite: partitionEnergy parts = partitionEnergy (S ∪ {A,B}) ──
  rw [← hSAB_eq]

  -- ── Unfold partitionEnergy to sum form ─────────────────────────────
  -- Both sides use the sum form since n ≠ 0.
  -- Let f(P,Q) = |P|·|Q|/n²·d(P,Q)²
  set f : Finset V × Finset V → ℚ := fun pq =>
    (pq.1.card : ℚ) * pq.2.card / n ^ 2 * (edgeDensity G pq.1 pq.2) ^ 2 with hf_def

  have h_pe_unfold : ∀ PP : Finset (Finset V),
      partitionEnergy G PP = (PP.product PP).sum f := by
    intro PP; unfold partitionEnergy; simp only [hn_def]
    rw [dif_neg hn]

  rw [h_pe_unfold, h_pe_unfold]

  -- ── Non-negativity of f ────────────────────────────────────────────
  have hf_nn : ∀ pq : Finset V × Finset V, 0 ≤ f pq := by
    intro ⟨P, Q⟩; simp only [hf_def]
    exact mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (sq_nonneg _)) (sq_nonneg _)

  -- ── Product-union decomposition lemma (general) ─────────────────────
  -- (P₁ ∪ P₂) ×ˢ (P₁ ∪ P₂) decomposes into 4 disjoint blocks.
  have h_sum_decomp : ∀ (P₁ P₂ : Finset (Finset V)), Disjoint P₁ P₂ →
      ((P₁ ∪ P₂).product (P₁ ∪ P₂)).sum f =
        (P₁.product P₁).sum f + (P₁.product P₂).sum f +
        (P₂.product P₁).sum f + (P₂.product P₂).sum f := by
    intro P₁ P₂ hd
    have hd_left : Disjoint (P₁.product (P₁ ∪ P₂)) (P₂.product (P₁ ∪ P₂)) := by
      rw [Finset.disjoint_left]; intro ⟨a, _⟩ h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).1
        (Finset.disjoint_left.mp hd (Finset.mem_product.mp h₁).1)
    have hd_r1 : Disjoint (P₁.product P₁) (P₁.product P₂) := by
      rw [Finset.disjoint_left]; intro ⟨_, b⟩ h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).2
        (Finset.disjoint_left.mp hd (Finset.mem_product.mp h₁).2)
    have hd_r2 : Disjoint (P₂.product P₁) (P₂.product P₂) := by
      rw [Finset.disjoint_left]; intro ⟨_, b⟩ h₁ h₂
      exact absurd (Finset.mem_product.mp h₂).2
        (Finset.disjoint_left.mp hd (Finset.mem_product.mp h₁).2)
    calc ((P₁ ∪ P₂).product (P₁ ∪ P₂)).sum f
        = (P₁.product (P₁ ∪ P₂) ∪ P₂.product (P₁ ∪ P₂)).sum f := by
            rw [Finset.union_product]
      _ = (P₁.product (P₁ ∪ P₂)).sum f + (P₂.product (P₁ ∪ P₂)).sum f :=
            Finset.sum_union hd_left
      _ = (P₁.product P₁ ∪ P₁.product P₂).sum f +
          (P₂.product P₁ ∪ P₂.product P₂).sum f := by
            rw [Finset.product_union, Finset.product_union]
      _ = _ := by rw [Finset.sum_union hd_r1, Finset.sum_union hd_r2]; ring

  -- ── Apply decomposition to both sides ──────────────────────────────
  set T : Finset (Finset V) := {A', A₂, B', B₂} with hT_def
  set AB : Finset (Finset V) := {A, B} with hAB_def

  rw [show ({A', A₂, B', B₂} : Finset (Finset V)) = T from rfl]
  rw [h_sum_decomp S T hST_disj, h_sum_decomp S AB hSAB_disj]
  -- Goal: SS + ST + TS + TT ≥ SS + SAB + ABS + ABAB + eps^6
  -- Cancelling SS: ST + TS + TT ≥ SAB + ABS + ABAB + eps^6

  -- ── Distinctness conditions for T = {A', A₂, B', B₂} ─────────────
  -- Needed for Finset sum expansions over T.
  have hA'neA₂ : A' ≠ A₂ := by
    intro heq; have ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact absurd hx (Finset.mem_sdiff.mp (heq ▸ hx)).2
  have hB'neB₂ : B' ≠ B₂ := by
    intro heq; have ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
    exact absurd hx (Finset.mem_sdiff.mp (heq ▸ hx)).2
  -- Cross-pair distinctness from Disjoint A B:
  -- If X ⊆ A, Y ⊆ B, and X has an element, then X ≠ Y.
  have hcross_ne : ∀ (X : Finset V), X ⊆ A → X.Nonempty →
      ∀ (Y : Finset V), Y ⊆ B → X ≠ Y := by
    intro X hXA ⟨x, hx⟩ Y hYB heq
    exact absurd (hYB (heq ▸ hx)) (Finset.disjoint_left.mp hABdisj (hXA hx))
  -- Similarly, if Y has an element:
  have hcross_ne' : ∀ (X : Finset V), X ⊆ A →
      ∀ (Y : Finset V), Y ⊆ B → Y.Nonempty → X ≠ Y := by
    intro X hXA Y hYB ⟨y, hy⟩ heq
    exact absurd (hXA (heq.symm ▸ hy)) (Finset.disjoint_right.mp hABdisj (hYB hy))
  have hA'neB' : A' ≠ B' := hcross_ne A' hA'sub (Finset.card_pos.mp hA'pos) B' hB'sub
  have hA'neB₂ : A' ≠ B₂ := hcross_ne A' hA'sub (Finset.card_pos.mp hA'pos) B₂
    Finset.sdiff_subset
  have hA₂neB' : A₂ ≠ B' :=
    hcross_ne' A₂ Finset.sdiff_subset B' hB'sub (Finset.card_pos.mp hB'pos)
  -- A₂ ≠ B₂: if A₂ = B₂, both ⊆ A ∩ B = ∅, so both = ∅.
  -- Then A' = A and B' = B, giving d(A',B') = d(A,B), contradicting hd.
  have hA₂neB₂ : A₂ ≠ B₂ := by
    intro heq
    -- A₂ ⊆ A, B₂ ⊆ B, A₂ = B₂ → A₂ ⊆ A ∩ B = ∅ → A₂ = ∅
    have hA₂e : A₂ = ∅ := Finset.eq_empty_iff_forall_not_mem.mpr
      (fun x hx => absurd (Finset.sdiff_subset hx)
        (Finset.disjoint_right.mp hABdisj (Finset.sdiff_subset (heq ▸ hx))))
    -- A₂ = A \ A' = ∅ → A' = A
    have hA'eqA : A' = A := by
      rw [Finset.eq_empty_iff_forall_not_mem] at hA₂e
      ext x; constructor
      · exact hA'sub
      · intro hx; by_contra hx'; exact hA₂e x (Finset.mem_sdiff.mpr ⟨hx, hx'⟩)
    -- B₂ = B \ B' = ∅ → B' = B
    have hB₂e : B₂ = ∅ := heq ▸ hA₂e
    have hB'eqB : B' = B := by
      rw [Finset.eq_empty_iff_forall_not_mem] at hB₂e
      ext x; constructor
      · exact hB'sub
      · intro hx; by_contra hx'; exact hB₂e x (Finset.mem_sdiff.mpr ⟨hx, hx'⟩)
    -- d(A', B') = d(A, B), contradicting hd: |d(A',B') - d(A,B)| > eps
    rw [hA'eqA, hB'eqB, sub_self, abs_zero] at hd; linarith

  -- ── T = T_A ∪ T_B decomposition ───────────────────────────────────
  set T_A : Finset (Finset V) := {A', A₂} with hTA_def
  set T_B : Finset (Finset V) := {B', B₂} with hTB_def

  have hT_eq : T = T_A ∪ T_B := by
    simp only [hT_def, hTA_def, hTB_def]
    ext X; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto

  have hTATB_disj : Disjoint T_A T_B := by
    rw [Finset.disjoint_left]; intro X hXTA hXTB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXTA hXTB
    rcases hXTA with rfl | rfl <;> rcases hXTB with rfl | rfl
    · exact absurd rfl hA'neB'
    · exact absurd rfl hA'neB₂
    · exact absurd rfl hA₂neB'
    · exact absurd rfl hA₂neB₂

  -- ── Decompose T×T into sub-blocks ─────────────────────────────────
  rw [hT_eq] at *
  have h_TT_decomp := h_sum_decomp T_A T_B hTATB_disj

  -- ── Cross block: S×T ≥ S×AB ───────────────────────────────────────
  -- For each C ∈ S, the inner sum over T is ≥ the inner sum over AB.
  -- This follows from density_sq_convex_right applied to the A-split
  -- and B-split of the second argument.
  -- Helper: f(P₁,Q) + f(P₂,Q) ≥ f(P₁∪P₂, Q) when Disjoint P₁ P₂
  -- (density_sq_convex scaled by |Q|/n²)
  have f_conv_left : ∀ (P₁ P₂ Q : Finset V), Disjoint P₁ P₂ →
      P₁ ∪ P₂ = A ∨ P₁ ∪ P₂ = B →
      f (P₁, Q) + f (P₂, Q) ≥ f (P₁ ∪ P₂, Q) := by
    intro P₁ P₂ Q hPd _
    simp only [hf_def]
    have hconv := density_sq_convex G P₁ P₂ Q hPd
    have hcardP : (P₁.card : ℚ) + P₂.card = ↑(P₁ ∪ P₂).card := by
      rw [Finset.card_union_of_disjoint hPd]; push_cast; ring
    have hQn : (0 : ℚ) ≤ (Q.card : ℚ) / n ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    calc (P₁.card : ℚ) * Q.card / n ^ 2 * (edgeDensity G P₁ Q) ^ 2 +
         (P₂.card : ℚ) * Q.card / n ^ 2 * (edgeDensity G P₂ Q) ^ 2
        = (Q.card : ℚ) / n ^ 2 * ((P₁.card : ℚ) * (edgeDensity G P₁ Q) ^ 2 +
            P₂.card * (edgeDensity G P₂ Q) ^ 2) := by ring
      _ ≥ (Q.card : ℚ) / n ^ 2 * (((P₁.card : ℚ) + P₂.card) *
            (edgeDensity G (P₁ ∪ P₂) Q) ^ 2) :=
          mul_le_mul_of_nonneg_left hconv hQn
      _ = (P₁ ∪ P₂).card * Q.card / n ^ 2 *
            (edgeDensity G (P₁ ∪ P₂) Q) ^ 2 := by rw [← hcardP]; push_cast; ring

  -- Helper: f(C,X₁) + f(C,X₂) ≥ f(C, X₁∪X₂) when Disjoint X₁ X₂
  -- (density_sq_convex_right scaled by |C|/n²)
  have f_conv_right : ∀ (C X₁ X₂ : Finset V), Disjoint X₁ X₂ →
      f (C, X₁) + f (C, X₂) ≥ f (C, X₁ ∪ X₂) := by
    intro C X₁ X₂ hXd
    simp only [hf_def]
    have hconv := density_sq_convex_right G C X₁ X₂ hXd
    have hcardX : (X₁.card : ℚ) + X₂.card = ↑(X₁ ∪ X₂).card := by
      rw [Finset.card_union_of_disjoint hXd]; push_cast; ring
    have hCn : (0 : ℚ) ≤ (C.card : ℚ) / n ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    calc (C.card : ℚ) * X₁.card / n ^ 2 * (edgeDensity G C X₁) ^ 2 +
         (C.card : ℚ) * X₂.card / n ^ 2 * (edgeDensity G C X₂) ^ 2
        = (C.card : ℚ) / n ^ 2 * ((X₁.card : ℚ) * (edgeDensity G C X₁) ^ 2 +
            X₂.card * (edgeDensity G C X₂) ^ 2) := by ring
      _ ≥ (C.card : ℚ) / n ^ 2 * (((X₁.card : ℚ) + X₂.card) *
            (edgeDensity G C (X₁ ∪ X₂)) ^ 2) :=
          mul_le_mul_of_nonneg_left hconv hCn
      _ = (C.card : ℚ) * (X₁ ∪ X₂).card / n ^ 2 *
            (edgeDensity G C (X₁ ∪ X₂)) ^ 2 := by rw [← hcardX]; push_cast; ring

  have h_ST_ge_SAB : (S.product (T_A ∪ T_B)).sum f ≥ (S.product AB).sum f := by
    rw [Finset.sum_product', Finset.sum_product']
    apply Finset.sum_le_sum
    intro C _hCS
    -- Expand inner sums
    rw [Finset.sum_union hTATB_disj]
    simp only [hTA_def, hTB_def, hAB_def]
    rw [Finset.sum_pair hA'neA₂, Finset.sum_pair hB'neB₂, Finset.sum_pair hAB]
    -- Goal: f(C,A') + f(C,A₂) + (f(C,B') + f(C,B₂)) ≥ f(C,A) + f(C,B)
    have h1 := f_conv_right C A' A₂ hAd; rw [hAu] at h1
    have h2 := f_conv_right C B' B₂ hBd; rw [hBu] at h2
    linarith

  -- ── Cross block: T×S ≥ AB×S ───────────────────────────────────────
  -- Row sums: g(P) = S.sum (fun Q => f(P,Q)).
  -- Need: g(A') + g(A₂) ≥ g(A) and g(B') + g(B₂) ≥ g(B).
  -- By Finset.sum_add_distrib + pointwise f_conv_left.
  have h_TS_ge_ABS : ((T_A ∪ T_B).product S).sum f ≥ (AB.product S).sum f := by
    rw [Finset.sum_product', Finset.sum_product']
    -- Expand outer sums
    rw [Finset.sum_union hTATB_disj]
    simp only [hTA_def, hTB_def, hAB_def]
    rw [Finset.sum_pair hA'neA₂, Finset.sum_pair hB'neB₂, Finset.sum_pair hAB]
    -- Goal: (gA' + gA₂) + (gB' + gB₂) ≥ gA + gB
    -- where gi = S.sum (fun Q => f(i,Q))
    have h1 : S.sum (fun Q => f (A', Q)) + S.sum (fun Q => f (A₂, Q)) ≥
        S.sum (fun Q => f (A, Q)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro Q _hQS
      have h := f_conv_left A' A₂ Q hAd (Or.inl hAu)
      rw [hAu] at h; exact h
    have h2 : S.sum (fun Q => f (B', Q)) + S.sum (fun Q => f (B₂, Q)) ≥
        S.sum (fun Q => f (B, Q)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro Q _hQS
      have h := f_conv_left B' B₂ Q hBd (Or.inr hBu)
      rw [hBu] at h; exact h
    linarith

  -- ── Internal block: T×T ≥ AB×AB + eps^6 ───────────────────────────
  have h_TT_ge_ABAB : ((T_A ∪ T_B).product (T_A ∪ T_B)).sum f ≥
      (AB.product AB).sum f + eps ^ 6 := by
    -- Decompose T×T into 4 sub-blocks
    rw [h_sum_decomp T_A T_B hTATB_disj]

    -- ── Algebraic bounds on sub-blocks (raw, without 1/n²) ──────────
    -- Each sub-block sum = (raw algebraic sum) / n²
    -- because f(P,Q) = |P|·|Q|·d(P,Q)² / n²

    -- AA sub-block raw bound
    have h_AA := sub4pair_energy_lower_bound G A' A₂ A' A₂ hAd hAd
    simp only [hAu] at h_AA
    -- h_AA: 4-sum_AA ≥ |A|²·d(A,A)²

    -- AB sub-block raw bound (STRICT, using hcore)
    have h_AB_strict : (A'.card : ℚ) * B'.card * (edgeDensity G A' B') ^ 2 +
        (A'.card : ℚ) * B₂.card * (edgeDensity G A' B₂) ^ 2 +
        (A₂.card : ℚ) * B'.card * (edgeDensity G A₂ B') ^ 2 +
        (A₂.card : ℚ) * B₂.card * (edgeDensity G A₂ B₂) ^ 2 >
        (A.card : ℚ) * B.card * (edgeDensity G A B) ^ 2 + eps ^ 6 * n ^ 2 := by
      have h_lb := four_subpair_excess_lb G A' A₂ B' B₂ hAd hBd
      simp only [hAu, hBu] at h_lb
      linarith

    -- BA sub-block raw bound
    have h_BA := sub4pair_energy_lower_bound G B' B₂ A' A₂ hBd hAd
    simp only [hBu, hAu] at h_BA
    -- h_BA: 4-sum_BA ≥ |B|·|A|·d(B,A)²

    -- BB sub-block raw bound
    have h_BB := sub4pair_energy_lower_bound G B' B₂ B' B₂ hBd hBd
    simp only [hBu] at h_BB
    -- h_BB: 4-sum_BB ≥ |B|²·d(B,B)²

    -- ── Expand Finset.sum over 2-element product sets ──────────────────
    -- Each (T_X ×ˢ T_Y).sum f expands to 4 terms of f, which equals
    -- (algebraic 4-term sum) / n² by ring.

    -- Helper: expand product sum over {a,b}×{c,d} into 4 terms
    have h_expand : ∀ (a b c d : Finset V), a ≠ b → c ≠ d →
        (({a, b} : Finset (Finset V)).product {c, d}).sum f =
          f (a, c) + f (a, d) + f (b, c) + f (b, d) := by
      intro a b c d hab hcd
      rw [Finset.sum_product']
      rw [Finset.sum_pair hab]
      rw [Finset.sum_pair hcd, Finset.sum_pair hcd]
      ring

    -- Expand sub-block sums
    rw [h_expand A' A₂ A' A₂ hA'neA₂ hA'neA₂,
        h_expand A' A₂ B' B₂ hA'neA₂ hB'neB₂,
        h_expand B' B₂ A' A₂ hB'neB₂ hA'neA₂,
        h_expand B' B₂ B' B₂ hB'neB₂ hB'neB₂]

    -- Expand AB×AB sum
    rw [show AB = ({A, B} : Finset (Finset V)) from rfl,
        h_expand A B A B hAB hAB]

    -- Goal is now: sum of 16 f-terms ≥ sum of 4 f-terms + eps^6
    -- Unfold f to raw expressions
    simp only [hf_def]

    -- Each f(P,Q) = |P|·|Q|·d(P,Q)² / n²
    -- Factor out 1/n² from all terms
    -- The algebraic bounds h_AA, h_AB_strict, h_BA, h_BB apply to
    -- the raw (non-normalized) sums.

    -- Collect: LHS - RHS ≥ eps^6
    -- LHS/n² - RHS/n² = (LHS_raw - RHS_raw) / n²
    -- LHS_raw ≥ RHS_raw + eps^6*n² (from algebraic bounds)
    -- So LHS/n² ≥ RHS/n² + eps^6

    -- All terms have the form (a * b / n^2) * d^2 = a * b * d^2 / n^2
    -- We can factor out 1/n^2 and work with raw sums.
    have h_raw_ge : ∀ (x y : ℚ), x > y + eps ^ 6 * n ^ 2 →
        x / n ^ 2 ≥ y / n ^ 2 + eps ^ 6 := by
      intro x y hxy
      rw [ge_iff_le, ← sub_le_iff_le_add, div_sub_div_eq_sub_div]
      rw [le_div_iff hn2_pos]
      linarith

    -- Combine all 16 terms into 4 groups matching the algebraic bounds
    -- AA group: f(A',A') + f(A',A₂) + f(A₂,A') + f(A₂,A₂) = AA_raw / n²
    -- AB group: f(A',B') + f(A',B₂) + f(A₂,B') + f(A₂,B₂) = AB_raw / n²
    -- BA group: f(B',A') + f(B',A₂) + f(B₂,A') + f(B₂,A₂) = BA_raw / n²
    -- BB group: f(B',B') + f(B',B₂) + f(B₂,B') + f(B₂,B₂) = BB_raw / n²
    --
    -- Old: f(A,A) + f(A,B) + f(B,A) + f(B,B) = old_raw / n²
    --
    -- Need: AA+AB+BA+BB ≥ old + eps^6
    -- Suffices: (AA+AB+BA+BB)*n² ≥ old*n² + eps^6*n⁴  -- NO, wrong
    -- Actually: each group_f = group_raw / n², so
    -- total_f = total_raw / n² and old_f = old_raw / n²
    -- Need: total_raw / n² ≥ old_raw / n² + eps^6
    -- ↔ total_raw ≥ old_raw + eps^6 * n²  (since n² > 0)
    -- Which follows from h_AA + h_AB_strict + h_BA + h_BB (algebraic bounds)

    -- Show each group sum = raw_sum / n²
    suffices h_suffices :
        (A'.card : ℚ) * A'.card * (edgeDensity G A' A') ^ 2 +
        (A'.card : ℚ) * A₂.card * (edgeDensity G A' A₂) ^ 2 +
        (A₂.card : ℚ) * A'.card * (edgeDensity G A₂ A') ^ 2 +
        (A₂.card : ℚ) * A₂.card * (edgeDensity G A₂ A₂) ^ 2 +
        ((A'.card : ℚ) * B'.card * (edgeDensity G A' B') ^ 2 +
        (A'.card : ℚ) * B₂.card * (edgeDensity G A' B₂) ^ 2 +
        (A₂.card : ℚ) * B'.card * (edgeDensity G A₂ B') ^ 2 +
        (A₂.card : ℚ) * B₂.card * (edgeDensity G A₂ B₂) ^ 2) +
        ((B'.card : ℚ) * A'.card * (edgeDensity G B' A') ^ 2 +
        (B'.card : ℚ) * A₂.card * (edgeDensity G B' A₂) ^ 2 +
        (B₂.card : ℚ) * A'.card * (edgeDensity G B₂ A') ^ 2 +
        (B₂.card : ℚ) * A₂.card * (edgeDensity G B₂ A₂) ^ 2) +
        ((B'.card : ℚ) * B'.card * (edgeDensity G B' B') ^ 2 +
        (B'.card : ℚ) * B₂.card * (edgeDensity G B' B₂) ^ 2 +
        (B₂.card : ℚ) * B'.card * (edgeDensity G B₂ B') ^ 2 +
        (B₂.card : ℚ) * B₂.card * (edgeDensity G B₂ B₂) ^ 2) ≥
        ((A.card : ℚ) * A.card * (edgeDensity G A A) ^ 2 +
        (A.card : ℚ) * B.card * (edgeDensity G A B) ^ 2 +
        (B.card : ℚ) * A.card * (edgeDensity G B A) ^ 2 +
        (B.card : ℚ) * B.card * (edgeDensity G B B) ^ 2) +
        eps ^ 6 * n ^ 2 by
      -- Convert between f-sum form and raw form
      -- f(P,Q) = |P|·|Q|/n²·d² = |P|·|Q|·d²/n²  (ring)
      -- sum of f = sum of (raw/n²) = (sum raw) / n²
      -- So suffices raw inequality → f inequality
      nlinarith [hn2_pos]
    -- Now prove the raw algebraic inequality using h_AA, h_AB_strict, h_BA, h_BB
    linarith

  -- ── Combine: SS + ST + TS + TT ≥ SS + SAB + ABS + ABAB + eps^6 ───
  linarith

end Szemeredi.EnergyIncrement
