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

-- ═══════════════════════════════════════════════════════════════════
-- PART III: SYMMETRY AND THE COLUMN / DIAGONAL REFINEMENT INCREMENTS
-- ═══════════════════════════════════════════════════════════════════

/-- Edge counts are symmetric in the two sides: since `G.Adj` is symmetric,
    the swap `(a, b) ↦ (b, a)` is a bijection between the adjacent pairs of
    `A ×ˢ B` and those of `B ×ˢ A`.  Proved by rewriting each filtered card as
    a double sum of indicator terms and commuting the sums. -/
private theorem edge_count_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    ((A.product B).filter (fun p => G.Adj p.1 p.2)).card =
    ((B.product A).filter (fun p => G.Adj p.1 p.2)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_product, Finset.sum_product]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun a _ => ?_))
  by_cases hab : G.Adj a b
  · simp [hab, G.symm hab]
  · have hba : ¬ G.Adj b a := fun h => hab (G.symm h)
    simp [hab, hba]

/-- **Symmetry of edge density.**  `d(A, B) = d(B, A)`.  A self-contained proof
    via `edge_count_comm` and `card_mul_edgeDensity`; avoids importing the heavy
    `SzemerediCoreOQ01` companion. -/
theorem edgeDensity_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgeDensity G A B = edgeDensity G B A := by
  by_cases h : (A.card : ℚ) * B.card = 0
  · unfold edgeDensity
    rw [dif_pos h, dif_pos (by rw [mul_comm]; exact h)]
  · have h1 := card_mul_edgeDensity G A B
    have h2 := card_mul_edgeDensity G B A
    have hc : (↑((A.product B).filter (fun p => G.Adj p.1 p.2)).card : ℚ)
            = ↑((B.product A).filter (fun p => G.Adj p.1 p.2)).card := by
      exact_mod_cast edge_count_comm G A B
    have hkey : (A.card : ℚ) * B.card * edgeDensity G A B =
        (A.card : ℚ) * B.card * edgeDensity G B A := by
      rw [h1]; rw [show (A.card : ℚ) * B.card = (B.card : ℚ) * A.card from mul_comm _ _, h2]
      exact hc
    exact mul_left_cancel₀ h hkey

/-- **Symmetry of pair energy.**  `pairEnergy G A B = pairEnergy G B A`.  Immediate
    from `edgeDensity_comm` and commutativity of the size weight. -/
theorem pairEnergy_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    pairEnergy G A B = pairEnergy G B A := by
  unfold pairEnergy
  rw [edgeDensity_comm G A B]; ring

/-- **Column refinement monotonicity.**  Splitting the `B`-side of a pair into
    disjoint `B₁, B₂` never decreases its normalized energy contribution.  This is
    the transpose of `pairEnergy_split_mono`, obtained for free from `pairEnergy_comm`
    plus the row (A-side) statement. -/
theorem pairEnergy_col_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ B₂ : Finset V) (hB : Disjoint B₁ B₂) :
    pairEnergy G A (B₁ ∪ B₂) ≤ pairEnergy G A B₁ + pairEnergy G A B₂ := by
  rw [pairEnergy_comm G A (B₁ ∪ B₂), pairEnergy_comm G A B₁, pairEnergy_comm G A B₂]
  exact pairEnergy_split_mono G B₁ B₂ A hB

/-- **Diagonal (double-convexity) increment.**  Splitting *both* sides of the
    diagonal pair `(A, A)` — the case where a part is refined against itself —
    never decreases the total energy over the resulting `2 × 2` block:
    `pairEnergy G A A ≤ Σ_{i,j∈{1,2}} pairEnergy G Aᵢ Aⱼ` where `A = A₁ ∪ A₂`.
    Obtained by applying the row split once and then the column split to each half
    (Cauchy–Schwarz in both coordinates). -/
theorem pairEnergy_diag_split_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ : Finset V) (hA : Disjoint A₁ A₂) :
    pairEnergy G (A₁ ∪ A₂) (A₁ ∪ A₂) ≤
      pairEnergy G A₁ A₁ + pairEnergy G A₁ A₂ +
      pairEnergy G A₂ A₁ + pairEnergy G A₂ A₂ := by
  have hrow := pairEnergy_split_mono G A₁ A₂ (A₁ ∪ A₂) hA
  have hc1 := pairEnergy_col_split_mono G A₁ A₁ A₂ hA
  have hc2 := pairEnergy_col_split_mono G A₂ A₁ A₂ hA
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: WHOLE-PARTITION REFINEMENT MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- The energy accumulated between a family `S` of "row" parts and a family `T` of
    "column" parts: `Σ_{P∈S, Q∈T} pairEnergy G P Q`.  With `S = T = parts` this is
    exactly `partitionEnergy` (below), and its bilinearity over disjoint unions is
    what lets the local pairwise increments assemble into a whole-partition
    statement. -/
private noncomputable def blockEnergy (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset (Finset V)) : ℚ :=
  S.sum (fun P => T.sum (fun Q => pairEnergy G P Q))

/-- `partitionEnergy` is `blockEnergy` of the partition against itself (for
    nonempty vertex sets, where the `1/n²` normaliser is meaningful). -/
private theorem partitionEnergy_eq_block (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (hn : (Fintype.card V : ℚ) ≠ 0) :
    partitionEnergy G parts = blockEnergy G parts parts := by
  dsimp only [partitionEnergy]
  rw [if_neg hn, Finset.sum_product]
  rfl

/-- Additivity of `blockEnergy` in the row family over a disjoint union. -/
private theorem blockEnergy_union_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (S₁ S₂ T : Finset (Finset V)) (h : Disjoint S₁ S₂) :
    blockEnergy G (S₁ ∪ S₂) T = blockEnergy G S₁ T + blockEnergy G S₂ T := by
  unfold blockEnergy
  rw [Finset.sum_union h]

/-- Additivity of `blockEnergy` in the column family over a disjoint union. -/
private theorem blockEnergy_union_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T₁ T₂ : Finset (Finset V)) (h : Disjoint T₁ T₂) :
    blockEnergy G S (T₁ ∪ T₂) = blockEnergy G S T₁ + blockEnergy G S T₂ := by
  unfold blockEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_union h]

/-- A single row family reduces to a plain sum of pair energies. -/
private theorem blockEnergy_singleton_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (T : Finset (Finset V)) :
    blockEnergy G {A} T = T.sum (fun Q => pairEnergy G A Q) := by
  unfold blockEnergy
  rw [Finset.sum_singleton]

/-- A single column family reduces to a plain sum of pair energies. -/
private theorem blockEnergy_singleton_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Finset V)) (B : Finset V) :
    blockEnergy G S {B} = S.sum (fun P => pairEnergy G P B) := by
  unfold blockEnergy
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.sum_singleton]

/-- A singleton-against-singleton block is a single pair energy. -/
private theorem blockEnergy_pair (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    blockEnergy G {A} {B} = pairEnergy G A B := by
  unfold blockEnergy
  rw [Finset.sum_singleton, Finset.sum_singleton]

/-- **Whole-partition refinement monotonicity.**  Replacing one part `A` of a
    partition by a disjoint split `A = A₁ ∪ A₂` never decreases the size-weighted
    `partitionEnergy`.  This is the increment half of the Alon–Fischer–Krivelevich–
    Szegedy strong regularity lemma, assembled from the three local increments:
    the `A × (rest)` **row** monotonicity, the `(rest) × A` **column** monotonicity,
    and the diagonal `(A, A)` **double-convexity** — the term where `A` is refined
    against itself.  Together with `partitionEnergy_le_one`, the strict form of this
    inequality forces the AFKS refinement loop to terminate. -/
theorem partitionEnergy_refine_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (A A₁ A₂ : Finset V)
    (hA : A ∈ parts) (hunion : A₁ ∪ A₂ = A) (hdisj : Disjoint A₁ A₂)
    (h1r : A₁ ∉ parts.erase A) (h2r : A₂ ∉ parts.erase A) (h12 : A₁ ≠ A₂) :
    partitionEnergy G parts ≤
      partitionEnergy G (insert A₁ (insert A₂ (parts.erase A))) := by
  set rest := parts.erase A with hrest
  by_cases hn : (Fintype.card V : ℚ) = 0
  · simp [partitionEnergy, hn]
  -- normalized (nonempty) case: pass to `blockEnergy`
  rw [partitionEnergy_eq_block G parts hn, partitionEnergy_eq_block G _ hn]
  -- set-level rewrites turning inserts into disjoint unions
  have hAr : A ∉ rest := by rw [hrest]; exact Finset.not_mem_erase A parts
  have hd_A_rest : Disjoint ({A} : Finset (Finset V)) rest :=
    Finset.disjoint_singleton_left.mpr hAr
  have h12d : Disjoint ({A₁} : Finset (Finset V)) {A₂} :=
    Finset.disjoint_singleton.mpr h12
  have htp : Disjoint (({A₁} : Finset (Finset V)) ∪ {A₂}) rest := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_singleton_left.mpr h1r, Finset.disjoint_singleton_left.mpr h2r⟩
  have hparts_eq : parts = ({A} : Finset (Finset V)) ∪ rest := by
    rw [hrest, ← Finset.insert_eq]; exact (Finset.insert_erase hA).symm
  have hnew_eq : insert A₁ (insert A₂ rest) =
      (({A₁} : Finset (Finset V)) ∪ {A₂}) ∪ rest := by
    rw [Finset.insert_eq A₁, Finset.insert_eq A₂, Finset.union_assoc]
  rw [hparts_eq, hnew_eq]
  -- expand both diagonal blockEnergies into the four sub-blocks
  rw [blockEnergy_union_left G {A} rest (({A} : Finset (Finset V)) ∪ rest) hd_A_rest,
      blockEnergy_union_right G {A} {A} rest hd_A_rest,
      blockEnergy_union_right G rest {A} rest hd_A_rest,
      blockEnergy_union_left G (({A₁} : Finset (Finset V)) ∪ {A₂}) rest
        ((({A₁} : Finset (Finset V)) ∪ {A₂}) ∪ rest) htp,
      blockEnergy_union_right G (({A₁} : Finset (Finset V)) ∪ {A₂})
        (({A₁} : Finset (Finset V)) ∪ {A₂}) rest htp,
      blockEnergy_union_right G rest (({A₁} : Finset (Finset V)) ∪ {A₂}) rest htp]
  -- the three local increments
  have hdiag : blockEnergy G {A} {A} ≤
      blockEnergy G (({A₁} : Finset (Finset V)) ∪ {A₂}) (({A₁} : Finset (Finset V)) ∪ {A₂}) := by
    rw [blockEnergy_pair,
        blockEnergy_union_left G {A₁} {A₂} (({A₁} : Finset (Finset V)) ∪ {A₂}) h12d,
        blockEnergy_union_right G {A₁} {A₁} {A₂} h12d,
        blockEnergy_union_right G {A₂} {A₁} {A₂} h12d,
        blockEnergy_pair, blockEnergy_pair, blockEnergy_pair, blockEnergy_pair, ← hunion]
    have := pairEnergy_diag_split_mono G A₁ A₂ hdisj
    linarith
  have hrow : blockEnergy G {A} rest ≤
      blockEnergy G (({A₁} : Finset (Finset V)) ∪ {A₂}) rest := by
    rw [blockEnergy_union_left G {A₁} {A₂} rest h12d,
        blockEnergy_singleton_left, blockEnergy_singleton_left, blockEnergy_singleton_left,
        ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro R _
    rw [← hunion]
    exact pairEnergy_split_mono G A₁ A₂ R hdisj
  have hcol : blockEnergy G rest {A} ≤
      blockEnergy G rest (({A₁} : Finset (Finset V)) ∪ {A₂}) := by
    rw [blockEnergy_union_right G rest {A₁} {A₂} h12d,
        blockEnergy_singleton_right, blockEnergy_singleton_right, blockEnergy_singleton_right,
        ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro R _
    rw [← hunion]
    exact pairEnergy_col_split_mono G R A₁ A₂ hdisj
  linarith [hdiag, hrow, hcol]

end Szemeredi.RegularityOQ04Energy
