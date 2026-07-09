/-
  Szemerédi Regularity Lemma — OQ-04: the energy-increment engine of the strong
  (Alon–Fischer–Krivelevich–Szegedy) regularity lemma.

  The companion file `SzemerediRegularityOQ04` supplies the *termination* half of
  AFKS: any `[0,1]`-valued potential that gains a fixed `δ > 0` at every step can
  only do so finitely often.  What that argument consumes is the *increment* half:
  refining a partition never decreases the size-weighted energy
  `partitionEnergy G parts = Σ_{i,j} (|Pᵢ||Pⱼ|/n²)·d(Pᵢ,Pⱼ)²`, and it strictly
  increases when the refined pair is far from its average density.  The core file
  `SzemerediRegularity` proves the abstract Cauchy–Schwarz ingredients
  (`density_sq_convex`, `split_energy_identity`, `split_energy_excess_bound`) but
  never connects them to `partitionEnergy`; a note there even abandons the
  increment step under the mistaken belief that `partitionEnergy` carries a
  `1/k²` normaliser.  It does not: the definition in `SzemerediCore` is exactly
  the size-weighted `|Pᵢ||Pⱼ|/n²`, under which refinement monotonicity is genuine.

  This file supplies the missing bridge, fully machine-checked:

  * `edgeDensity_union_mul` — the (reusable) weighted-average identity: for
    disjoint `A₁, A₂`, the edge-count-weighted density of `A₁ ∪ A₂` against `B`
    splits as `|A₁∪A₂||B|·d(A₁∪A₂,B) = |A₁||B|·d(A₁,B) + |A₂||B|·d(A₂,B)`.
  * `pairEnergy` — the normalized contribution `(|A||B|/n²)·d(A,B)²` of one
    ordered pair to `partitionEnergy`.
  * `pairEnergy_split_mono` — one-sided refinement monotonicity: splitting the
    `A`-side of a pair never decreases its energy contribution.
  * `pairEnergy_split_gain` — the quantitative increment: if the two halves'
    densities differ by at least `δ`, the split raises the contribution by at
    least `(|A₁||A₂|/(|A₁|+|A₂|))·(|B|/n²)·δ²`.  This is the Cauchy–Schwarz
    energy boost that powers the AFKS iteration.
  * `pairEnergy_row_split_mono` — the boost summed over a whole row of `B`-parts.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularity

namespace Szemeredi.RegularityOQ04Energy

open Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: EDGE-COUNT ADDITIVITY AND THE WEIGHTED-AVERAGE IDENTITY
-- ═══════════════════════════════════════════════════════════════════

/-- Helper: `|A|·|B|·d(A,B)` equals the raw edge count between `A` and `B`. -/
private theorem card_mul_edgeDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (A.card : ℚ) * B.card * edgeDensity G A B =
    ↑((A.product B).filter (fun p => G.Adj p.1 p.2)).card := by
  unfold edgeDensity
  split_ifs with h
  · rw [mul_zero]; symm
    rw [Nat.cast_eq_zero, Finset.card_eq_zero]
    rcases mul_eq_zero.mp h with ha | hb
    · have hA := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp ha)
      ext x; simp [hA, Finset.not_mem_empty]
    · have hB := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hb)
      ext x; simp [Finset.product, hB, Finset.not_mem_empty]
  · have hne : (↑A.card : ℚ) * ↑B.card ≠ 0 := h
    rw [mul_div_cancel₀ _ hne]

/-- Helper: edge counts to `B` are additive over a disjoint split of the `A`-side. -/
private theorem edge_count_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂) :
    (((A₁ ∪ A₂).product B).filter (fun p => G.Adj p.1 p.2)).card =
    ((A₁.product B).filter (fun p => G.Adj p.1 p.2)).card +
    ((A₂.product B).filter (fun p => G.Adj p.1 p.2)).card := by
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

/-- **Weighted-average identity.**  For a disjoint split `A₁, A₂` of the `A`-side,
    the edge-count-weighted densities against a fixed `B` add:
    `|A₁∪A₂|·|B|·d(A₁∪A₂,B) = |A₁|·|B|·d(A₁,B) + |A₂|·|B|·d(A₂,B)`.
    Equivalently, `d(A₁∪A₂,B)` is the `|A₁|:|A₂|`-weighted mean of the two
    sub-densities.  This is the exact algebraic content that turns the abstract
    Cauchy–Schwarz split lemmas into an energy statement about `edgeDensity`. -/
theorem edgeDensity_union_mul (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂) :
    (↑(A₁ ∪ A₂).card : ℚ) * ↑B.card * edgeDensity G (A₁ ∪ A₂) B =
    ↑A₁.card * ↑B.card * edgeDensity G A₁ B +
    ↑A₂.card * ↑B.card * edgeDensity G A₂ B := by
  have h₁ := card_mul_edgeDensity G A₁ B
  have h₂ := card_mul_edgeDensity G A₂ B
  have h₃ := card_mul_edgeDensity G (A₁ ∪ A₂) B
  have he : (↑(((A₁ ∪ A₂).product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ) =
      ↑((A₁.product B).filter (fun p => G.Adj p.1 p.2)).card +
      ↑((A₂.product B).filter (fun p => G.Adj p.1 p.2)).card := by
    exact_mod_cast edge_count_union G A₁ A₂ B hA
  rw [h₃, h₁, h₂]; exact he

-- ═══════════════════════════════════════════════════════════════════
-- PART II: NORMALIZED PAIR ENERGY AND ITS REFINEMENT BEHAVIOUR
-- ═══════════════════════════════════════════════════════════════════

/-- The normalized energy contribution of one ordered pair `(A, B)` to
    `partitionEnergy`: `(|A|·|B|/n²)·d(A,B)²`, where `n = |V|`.  Summing
    `pairEnergy G P Q` over all `(P,Q) ∈ parts ×ˢ parts` reproduces
    `partitionEnergy G parts`. -/
noncomputable def pairEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℚ :=
  (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 * (edgeDensity G A B) ^ 2

/-- Factoring helper: pull the common `|B|/n²` weight out of a pair-energy term.
    Purely arithmetic in `B.card` — no graph structure is involved. -/
private theorem pairEnergy_factor (B : Finset V) (a d : ℚ) :
    a * (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 * d =
    (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 * (a * d) := by
  ring

/-- **One-sided refinement monotonicity.**  Splitting the `A`-side of a pair into
    disjoint `A₁, A₂` never decreases its normalized energy contribution:
    `pairEnergy G (A₁ ∪ A₂) B ≤ pairEnergy G A₁ B + pairEnergy G A₂ B`.
    This is `density_sq_convex` transported to the normalized units of
    `partitionEnergy`. -/
theorem pairEnergy_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂) :
    pairEnergy G (A₁ ∪ A₂) B ≤ pairEnergy G A₁ B + pairEnergy G A₂ B := by
  have hconv := density_sq_convex G A₁ A₂ B hA
  -- `density_sq_convex` states the coefficient as `↑(A₁.card + A₂.card)`; normalize
  -- it to `↑A₁.card + ↑A₂.card` so it matches `hcard` below.
  push_cast at hconv
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  have hw : (0 : ℚ) ≤ (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
  have key := mul_le_mul_of_nonneg_left hconv hw
  unfold pairEnergy
  rw [hcard, pairEnergy_factor, pairEnergy_factor, pairEnergy_factor, ← mul_add]
  exact key

/-- **Quantitative energy increment (Cauchy–Schwarz boost).**  If the two halves
    of a disjoint split have densities differing by at least `δ`, then refining
    the pair raises its normalized energy contribution by at least
    `(|A₁|·|A₂|/(|A₁|+|A₂|))·(|B|/n²)·δ²`.  This positive gain, together with the
    `[0,1]` bound on `partitionEnergy`, is what forces the AFKS refinement loop to
    terminate. -/
theorem pairEnergy_split_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂)
    (hn₁ : 0 < (A₁.card : ℚ)) (hn₂ : 0 < (A₂.card : ℚ)) (hB : 0 < (B.card : ℚ))
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hdev : |edgeDensity G A₁ B - edgeDensity G A₂ B| ≥ δ) :
    pairEnergy G (A₁ ∪ A₂) B +
        (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) *
          ((B.card : ℚ) / (Fintype.card V : ℚ) ^ 2) * δ ^ 2 ≤
      pairEnergy G A₁ B + pairEnergy G A₂ B := by
  have hsum_pos : (0 : ℚ) < (A₁.card : ℚ) + A₂.card := by linarith
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  -- weighted average of the sub-densities
  have hmul := edgeDensity_union_mul G A₁ A₂ B hA
  rw [hcard] at hmul
  have hBne : (B.card : ℚ) ≠ 0 := ne_of_gt hB
  have havg : ((A₁.card : ℚ) + A₂.card) * edgeDensity G (A₁ ∪ A₂) B =
      (A₁.card : ℚ) * edgeDensity G A₁ B + (A₂.card : ℚ) * edgeDensity G A₂ B :=
    mul_left_cancel₀ hBne (by linear_combination hmul)
  have hd_eq : edgeDensity G (A₁ ∪ A₂) B =
      ((A₁.card : ℚ) * edgeDensity G A₁ B + (A₂.card : ℚ) * edgeDensity G A₂ B) /
        ((A₁.card : ℚ) + A₂.card) := by
    rw [eq_div_iff hsum_pos.ne']; linear_combination havg
  have hid := split_energy_identity (A₁.card : ℚ) (A₂.card : ℚ)
    (edgeDensity G A₁ B) (edgeDensity G A₂ B) hsum_pos.ne'
  have hbound := split_energy_excess_bound (A₁.card : ℚ) (A₂.card : ℚ)
    (edgeDensity G A₁ B) (edgeDensity G A₂ B) δ hn₁ hn₂ hδ hdev
  -- the unnormalized excess is ≥ the δ² lower bound
  have hexcess :
      (A₁.card : ℚ) * A₂.card * δ ^ 2 / ((A₁.card : ℚ) + A₂.card) ≤
      (A₁.card : ℚ) * (edgeDensity G A₁ B) ^ 2 +
        (A₂.card : ℚ) * (edgeDensity G A₂ B) ^ 2 -
        ((A₁.card : ℚ) + A₂.card) * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 := by
    rw [hd_eq, hid]; linarith [hbound]
  -- normalize by |B|/n² ≥ 0
  have hw : (0 : ℚ) ≤ (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
  unfold pairEnergy
  rw [hcard]
  -- factor both sides through the common weight |B|/n², reducing to `hexcess`
  have hgL :
      (↑A₁.card + ↑A₂.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 *
          (edgeDensity G (A₁ ∪ A₂) B) ^ 2 +
        (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) *
          ((B.card : ℚ) / (Fintype.card V : ℚ) ^ 2) * δ ^ 2 =
      (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 *
        (((A₁.card : ℚ) + A₂.card) * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 +
          (A₁.card : ℚ) * A₂.card * δ ^ 2 / ((A₁.card : ℚ) + A₂.card)) := by
    ring
  have hgR :
      (A₁.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 * (edgeDensity G A₁ B) ^ 2 +
        (A₂.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 * (edgeDensity G A₂ B) ^ 2 =
      (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 *
        ((A₁.card : ℚ) * (edgeDensity G A₁ B) ^ 2 +
          (A₂.card : ℚ) * (edgeDensity G A₂ B) ^ 2) := by
    ring
  rw [hgL, hgR]
  apply mul_le_mul_of_nonneg_left _ hw
  linarith [hexcess]

/-- **Row form of the energy increment.**  Splitting the `A`-side of a pair into
    disjoint `A₁, A₂` and summing the energy contribution over an arbitrary family
    `Bs` of `B`-parts never decreases the total: the monotonicity holds row-by-row
    and hence after summation.  This is the shape in which the increment is applied
    when refining one part against all the others simultaneously. -/
theorem pairEnergy_row_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ : Finset V) (hA : Disjoint A₁ A₂) (Bs : Finset (Finset V)) :
    (Bs.sum fun B => pairEnergy G (A₁ ∪ A₂) B) ≤
      Bs.sum fun B => pairEnergy G A₁ B + pairEnergy G A₂ B := by
  apply Finset.sum_le_sum
  intro B _
  exact pairEnergy_split_mono G A₁ A₂ B hA

end Szemeredi.RegularityOQ04Energy
