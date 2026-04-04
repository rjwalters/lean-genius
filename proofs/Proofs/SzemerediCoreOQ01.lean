/-
  Szemeredi Core OQ-01: Energy Increment Lemma

  If a partition has an irregular pair (A, B), then the refinement obtained
  by splitting A and B using the irregular witnesses increases the partition
  energy by at least ε^5.

  This file proves the key algebraic steps:
  1. edgeDensity_symm: edge density is symmetric d(A,B) = d(B,A)
  2. density_sq_convex_right: convexity when splitting the second argument
  3. sub4pair_energy_lower_bound: splitting both A and B never decreases energy
  4. energy_excess_A_split: exact excess formula from splitting A (sorry for havg)
  5. energy_increment_step: main theorem (sorry for Finset sum)

  Mathematical content: Komlós-Simonovits (1996), §3; Szemerédi (1975).
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity

namespace Szemeredi.EnergyIncrement

open Classical Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════���════════════════════════���══════════════
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

-- ═════════════════════════════════════════════════════��═════════════
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

-- ══════════════════════���════════════════════════��═══════════════════
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

-- ═════════════════════════════════════════════════════���═════════════
-- PART V: MAIN ENERGY INCREMENT THEOREM
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy Increment Lemma (OQ-01)**:
    For an irregular pair (A, B) in an ε-equipartition, splitting (A,B) via
    the irregular witnesses increases partitionEnergy by at least ε^5.

    **Proof strategy**:
    1. Extract witnesses: A' ⊆ A, B' ⊆ B with |A'| ≥ ε|A|, |B'| ≥ ε|B|,
       and |d(A',B') - d(A,B)| > ε
    2. Split: A₁ = A', A₂ = A\A', B₁ = B', B₂ = B\B'
    3. sub4pair_energy_lower_bound: 4-subpair energy ≥ original (A,B) pair energy
    4. energy_excess_A_split (twice): excess = sum of squared density deviations
    5. From irregularity: (d(A₁,B₁) - d(A,B))² > ε² implies A-or-B deviation > ε/2
    6. Each part has size ≥ εn (equipartition hypothesis):
       excess × |A||B|/n² ≥ ε^4 × (εn/n)² = ε^6 — well, ε^5 after careful accounting
    7. All other pairs also weakly increase (density_sq_convex for each other pair)

    **Current sorry**: The Finset sum manipulation to formalize step 7
    (computing partitionEnergy over the refined partition) requires extensive
    Finset algebra. The algebraic core above is fully proved. -/
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
      partitionEnergy G parts' ≥ partitionEnergy G parts + eps ^ 5 := by
  obtain ⟨A', B', hA'sub, hB'sub, hcA', hcB', hd⟩ := exists_irregular_witness G eps A B hirr
  -- Refined partition: split A into {A', A\A'} and B into {B', B\B'}
  exact ⟨(parts.erase B).erase A ∪ {A', A \ A', B', B \ B'}, by sorry⟩

end Szemeredi.EnergyIncrement
