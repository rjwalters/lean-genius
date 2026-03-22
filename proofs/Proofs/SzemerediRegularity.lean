/-
  Szemeredi Regularity Lemma

  Every large enough graph can be partitioned into a bounded number of
  parts such that edges between most pairs behave pseudo-randomly.
  The fundamental structural result in graph theory.

  Part I: Epsilon-regular pairs and partitions
  Part II: Partition energy and energy increment
  Part III: Regularity lemma (main result)

  Szemeredi (1975), Komlos-Simonovits (1996)
-/
import Mathlib

namespace Szemeredi.Regularity

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: EPSILON-REGULAR PAIRS AND PARTITIONS
-- ═══════════════════════════════════════════════════════════════════

/-- Edge density between two disjoint vertex subsets in a simple graph.
    d(A,B) = |E(A,B)| / (|A| * |B|). -/
noncomputable def edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℚ :=
  if h : (A.card : ℚ) * B.card = 0 then 0
  else ((A.product B).filter (fun p => G.Adj p.1 p.2)).card / (A.card * B.card)

/-- A pair (A, B) of vertex subsets is epsilon-regular if for every
    A' ⊆ A, B' ⊆ B with |A'| ≥ ε|A| and |B'| ≥ ε|B|, the edge
    density d(A', B') is within ε of d(A, B). -/
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

-- ═══════════════════════════════════════════════════════════════════
-- PART II: PARTITION ENERGY AND ENERGY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

/-- The energy of a partition: E(P) = (1/k²) * Σ_{i,j} d(Vᵢ, Vⱼ)².
    Energy lies in [0,1] and increases under refinement. -/
noncomputable def partitionEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) : ℚ :=
  if h : parts.card = 0 then 0
  else (1 : ℚ) / (parts.card ^ 2) *
    (parts.product parts).sum (fun pq => (edgeDensity G pq.1 pq.2) ^ 2)

/-- Partition energy is non-negative. -/
theorem partitionEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) :
    0 ≤ partitionEnergy G parts := by
  unfold partitionEnergy
  split_ifs with h
  · exact le_refl 0
  · apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Helper: |A| * |B| * edgeDensity(A,B) = edge count (as ℚ). -/
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

/-- Edge count additivity: for disjoint A₁, A₂, edge counts to B add. -/
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
    If A = A₁ ∪ A₂ (disjoint), then |A₁|*d(A₁,B)² + |A₂|*d(A₂,B)² ≥ |A|*d(A,B)².
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
  -- The weighted average property: (n₁+n₂)*m*d = n₁*m*d₁ + n₂*m*d₂
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
  -- Case 1: B empty (card = 0) — all terms zero
  by_cases hB : (B.card : ℚ) = 0
  · have h0 : ∀ (S : Finset V), edgeDensity G S B = 0 := by
      intro S; unfold edgeDensity
      rw [dif_pos (show (↑S.card : ℚ) * ↑B.card = 0 from by rw [hB, mul_zero])]
    -- Unfold set abbreviations so simp can apply h0
    have hd₁0 : d₁ = 0 := h0 A₁
    have hd₂0 : d₂ = 0 := h0 A₂
    have hd0 : d = 0 := h0 (A₁ ∪ A₂)
    rw [hd₁0, hd₂0, hd0]; simp
  -- Case 2: n₁ + n₂ = 0 — both sets empty, all terms zero
  by_cases hnn : n₁ + n₂ = 0
  · have h1 : n₁ = 0 := le_antisymm (by linarith) hn₁
    have h2 : n₂ = 0 := le_antisymm (by linarith) hn₂
    simp [h1, h2]
  -- Main case: B nonempty, n₁ + n₂ > 0
  · have hnn_pos : (0 : ℚ) < n₁ + n₂ :=
      lt_of_le_of_ne (by linarith) (Ne.symm hnn)
    -- Derive weighted average: (n₁+n₂)*d = n₁*d₁ + n₂*d₂ (cancel B.card)
    have hd_avg : (n₁ + n₂) * d = n₁ * d₁ + n₂ * d₂ := by
      have hB_ne : (B.card : ℚ) ≠ 0 := hB
      exact mul_left_cancel₀ hB_ne (show ↑B.card * ((n₁ + n₂) * d) =
        ↑B.card * (n₁ * d₁ + n₂ * d₂) from by nlinarith)
    -- Rewrite d using the weighted average
    have hd_eq : d = (n₁ * d₁ + n₂ * d₂) / (n₁ + n₂) := by
      rw [eq_div_iff (ne_of_gt hnn_pos)]; linarith [hd_avg]
    -- Goal: n₁*d₁² + n₂*d₂² ≥ (n₁+n₂)*d²
    rw [ge_iff_le, ← sub_nonneg, hd_eq]
    -- The difference equals n₁*n₂*(d₁-d₂)²/(n₁+n₂) ≥ 0
    have key : n₁ * d₁ ^ 2 + n₂ * d₂ ^ 2 -
        (n₁ + n₂) * ((n₁ * d₁ + n₂ * d₂) / (n₁ + n₂)) ^ 2 =
        n₁ * n₂ * (d₁ - d₂) ^ 2 / (n₁ + n₂) := by
      field_simp
      ring
    rw [key]
    exact div_nonneg (mul_nonneg (mul_nonneg hn₁ hn₂) (sq_nonneg _)) (le_of_lt hnn_pos)

/-- Energy increment step: if a partition has too many irregular pairs,
    refinement increases energy by at least eps^5. This is the key
    technical lemma driving the regularity proof. -/
theorem energy_increment_step (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps) (parts : Finset (Finset V))
    (hirr : ¬IsRegularPartition G eps parts) :
    ∃ parts' : Finset (Finset V),
      partitionEnergy G parts' ≥ partitionEnergy G parts + eps ^ 5 ∧
      parts'.card ≤ parts.card * 2 ^ parts.card := by
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
  · -- Each d(P,Q)² ≤ 1, and there are k² terms, so Σ d² ≤ k²
    -- Therefore (1/k²) * Σ d² ≤ (1/k²) * k² = 1
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
    we need at most ⌈1/eps^5⌉ iterations. -/
theorem max_iterations (eps : ℚ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ e : ℚ, 0 ≤ e → e ≤ 1 → e + N * eps ^ 5 > 1 := by
  -- By the Archimedean property, find N > 1/eps^5.
  -- Then N * eps^5 > 1, and with e ≥ 0 we get e + N * eps^5 > 1.
  have heps5 : (0 : ℚ) < eps ^ 5 := pow_pos heps 5
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / eps ^ 5)
  exact ⟨N, fun e he0 _ => by linarith [((div_lt_iff₀ heps5).mp hN)]⟩

/-- **Szemeredi Regularity Lemma**: For every epsilon > 0, every
    sufficiently large graph admits an epsilon-regular partition into
    at most M(epsilon) parts.

    The proof iterates: start with an arbitrary equipartition. If not
    regular, refine to increase energy by eps^5. Since energy ∈ [0,1],
    this terminates after at most eps^{-5} steps. -/
theorem regularity_lemma (eps : ℚ) (heps : 0 < eps) :
    ∃ M : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj],
      Fintype.card V ≥ M →
      ∃ parts : Finset (Finset V), IsRegularPartition G eps parts ∧
        parts.card ≤ M := by
  sorry

end Szemeredi.Regularity
