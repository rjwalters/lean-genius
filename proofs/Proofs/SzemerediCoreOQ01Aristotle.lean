/-
  Aristotle targets for SzemerediCoreOQ01
  Energy increment step — Finset.sum packaging for refined partition.
  See SzemerediCoreOQ01.lean for the main formalization.

  Infrastructure status (updated 2026-04-05, Session 3):
  - four_subpair_edge_count_identity: PROVED
  - four_subpair_deviation_identity: PROVED
  - four_subpair_excess_lb: PROVED
  - partitionEnergy_term_nonneg: PROVED
  - partitionEnergy_mono: PROVED
  - energy_increment_packaging_ari: STRUCTURAL PROOF (Session 3)
      PROVED: n > 0, S ∪ {A,B} = parts, Disjoint S {A,B}, Disjoint S T,
              ne facts (A' ≠ A, A₂ ≠ A, B' ≠ B, B₂ ≠ B), card facts
      REMAINING sorry: Finset.sum_union block decomposition

  Remaining sorry needs:
    unfold partitionEnergy → Finset.sum_product' → Finset.sum_union (×2) → 4 blocks
  Block comparisons (all in scope):
  - S×S: identical
  - S×T ≥ S×{A,B}: density_sq_convex_right per C ∈ S (A→{A',A₂}, B→{B',B₂})
  - T×S ≥ {A,B}×S: edgeDensity_symm
  - T×T ≥ {A,B}×{A,B} + eps^6:
      AA: sub4pair_energy_lower_bound G A' A₂ A' A₂ hAd hAd ≥ |A|²d(A,A)²
      AB: four_subpair_excess_lb G A' A₂ B' B₂ hAd hBd + hcore > |A||B|d(A,B)² + eps^6*n²
      BA: sub4pair_energy_lower_bound G B' B₂ A' A₂ hBd hAd ≥ |B||A|d(B,A)²
      BB: sub4pair_energy_lower_bound G B' B₂ B' B₂ hBd hBd ≥ |B|²d(B,B)²
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediCoreOQ01

namespace Szemeredi.EnergyIncrement.Aristotle

open Classical Szemeredi.Core Szemeredi.EnergyIncrement

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: MONOTONICITY LEMMAS (PROVED)
-- ═══════════════════════════════════════════════════════════════════

/-- Each term in the partitionEnergy sum is non-negative. -/
lemma partitionEnergy_term_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (P Q : Finset V) :
    0 ≤ (P.card : ℚ) * Q.card / (Fintype.card V : ℚ) ^ 2 *
        (edgeDensity G P Q) ^ 2 :=
  mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity))
    (sq_nonneg _)

/-- **partitionEnergy is monotone** under Finset superset. -/
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
    has energy ≥ energy(parts) + eps^6. -/
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
  -- S = (parts.erase B).erase A, so S ∪ {A,B} recovers all of parts.
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

  -- ── ne facts: A' ≠ A, A₂ ≠ A, B' ≠ B, B₂ ≠ B ──────────────────
  -- A' ≠ A: if A' = A then A₂ = A \ A = ∅, contradicting hA₂pos
  have hA'neA : A' ≠ A := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₂pos
    exact (Finset.mem_sdiff.mp hx).2 (heq ▸ (Finset.mem_sdiff.mp hx).1)
  -- A₂ ≠ A: if A₂ = A then A' ⊆ A₂ = A \ A', so A' = ∅, contradicting hA'pos
  have hA₂neA : A₂ ≠ A := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
    exact (Finset.mem_sdiff.mp (heq ▸ hA'sub hx)).2 hx
  -- B' ≠ B: symmetric
  have hB'neB : B' ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hB₂pos
    exact (Finset.mem_sdiff.mp hx).2 (heq ▸ (Finset.mem_sdiff.mp hx).1)
  -- B₂ ≠ B: symmetric
  have hB₂neB : B₂ ≠ B := by
    intro heq
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
    exact (Finset.mem_sdiff.mp (heq ▸ hB'sub hx)).2 hx

  -- ── Disjoint S {A', A₂, B', B₂} ────────────────────────────────
  -- Each of A', A₂, B', B₂ is a strict subset of A or B.
  -- If X ∈ S ∩ T: X ∈ parts and X ⊊ A (or B).
  -- hparts_disj gives Disjoint X A. But X ⊆ A → X = ∅ → contradicts positivity.
  have hST_disj : Disjoint S ({A', A₂, B', B₂} : Finset (Finset V)) := by
    rw [Finset.disjoint_left]
    intro X hXS hXT
    have hXparts : X ∈ parts :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hXS).2).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hXT
    -- Each case: X is a strict subset of A or B, contradicting partition disjointness
    rcases hXT with hXA' | hXA₂ | hXB' | hXB₂
    · -- X = A' ⊆ A, A' ∈ parts, A' ≠ A → Disjoint X A, but X ⊆ A → ↯
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hA'pos
      rw [hXA'] at hXparts
      exact absurd (hA'sub hx)
        (Finset.disjoint_left.mp (hparts_disj A' A hXparts hA hA'neA) hx)
    · -- X = A₂ = A \ A' ⊆ A → same
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hA₂pos
      rw [hXA₂] at hXparts
      exact absurd (Finset.mem_sdiff.mp hx).1
        (Finset.disjoint_left.mp (hparts_disj A₂ A hXparts hA hA₂neA) hx)
    · -- X = B' ⊆ B → same with B
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hB'pos
      rw [hXB'] at hXparts
      exact absurd (hB'sub hx)
        (Finset.disjoint_left.mp (hparts_disj B' B hXparts hB hB'neB) hx)
    · -- X = B₂ = B \ B' ⊆ B → same
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hB₂pos
      rw [hXB₂] at hXparts
      exact absurd (Finset.mem_sdiff.mp hx).1
        (Finset.disjoint_left.mp (hparts_disj B₂ B hXparts hB hB₂neB) hx)

  -- ── Card facts ───────────────────────────────────────────────────
  have hcard_A : A'.card + (A \ A').card = A.card := by
    have h := Finset.card_union_of_disjoint hAd; rw [hAu] at h; omega
  have hcard_B : B'.card + (B \ B').card = B.card := by
    have h := Finset.card_union_of_disjoint hBd; rw [hBu] at h; omega

  -- ── Rewrite: energy(parts) = energy(S ∪ {A,B}) ──────────────────
  rw [← hSAB]

  -- ── Main block decomposition (sorry) ────────────────────────────
  -- Goal: energy(S ∪ {A', A₂, B', B₂}) ≥ energy(S ∪ {A, B}) + eps^6
  --
  -- Available: hST_disj, hSAB_disj, hcard_A, hcard_B, hAu, hBu, hcore, hn
  -- Also: four_subpair_excess_lb, sub4pair_energy_lower_bound,
  --       density_sq_convex, density_sq_convex_right, edgeDensity_symm
  --
  -- Proof outline:
  -- 1. unfold partitionEnergy; simp only [if_neg hn]
  -- 2. rw [Finset.sum_product'] to get nested sums
  -- 3. Finset.sum_union hST_disj → split outer sum into S and T parts
  -- 4. Finset.sum_union (inner) → split inner sum into S and T parts (×2)
  -- 5. Repeat for old partition with hSAB_disj
  -- 6. Cancel SS blocks; compare ST≥S{AB}, TS≥{AB}S, TT≥{AB}{AB}+eps^6
  sorry

end Szemeredi.EnergyIncrement.Aristotle
