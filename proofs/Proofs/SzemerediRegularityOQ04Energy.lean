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

/-- **Quantitative row form of the energy increment.**  If a distinguished part
    `B₀ ∈ Bs` witnesses a density deviation `|d(A₁,B₀) − d(A₂,B₀)| ≥ δ` between the
    two halves, then splitting the `A`-side and summing the energy contribution over
    the whole row raises the total by at least the single-pair gain at `B₀`.  Every
    other row term contributes a nonnegative increment (`pairEnergy_split_mono`), so
    the definite gain at `B₀` survives to the summed statement.  This is the shape in
    which one irregular partner drives the whole-partition energy jump. -/
theorem pairEnergy_row_split_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ : Finset V) (hA : Disjoint A₁ A₂) (Bs : Finset (Finset V))
    (B₀ : Finset V) (hB₀ : B₀ ∈ Bs)
    (hn₁ : 0 < (A₁.card : ℚ)) (hn₂ : 0 < (A₂.card : ℚ)) (hB : 0 < (B₀.card : ℚ))
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hdev : |edgeDensity G A₁ B₀ - edgeDensity G A₂ B₀| ≥ δ) :
    (Bs.sum fun B => pairEnergy G (A₁ ∪ A₂) B) +
        (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) *
          ((B₀.card : ℚ) / (Fintype.card V : ℚ) ^ 2) * δ ^ 2 ≤
      Bs.sum fun B => pairEnergy G A₁ B + pairEnergy G A₂ B := by
  -- Work with the per-term surplus `g B = (pairEnergy A₁ B + pairEnergy A₂ B) − pairEnergy (A₁∪A₂) B`.
  have hnn : ∀ B ∈ Bs, (0 : ℚ) ≤
      (pairEnergy G A₁ B + pairEnergy G A₂ B) - pairEnergy G (A₁ ∪ A₂) B := by
    intro B _
    linarith [pairEnergy_split_mono G A₁ A₂ B hA]
  -- At `B₀` the surplus is at least the Cauchy–Schwarz gain.
  have hgain : (A₁.card : ℚ) * A₂.card / ((A₁.card : ℚ) + A₂.card) *
        ((B₀.card : ℚ) / (Fintype.card V : ℚ) ^ 2) * δ ^ 2 ≤
      (pairEnergy G A₁ B₀ + pairEnergy G A₂ B₀) - pairEnergy G (A₁ ∪ A₂) B₀ := by
    linarith [pairEnergy_split_gain G A₁ A₂ B₀ hA hn₁ hn₂ hB δ hδ hdev]
  -- One term of a sum of nonnegatives is bounded by the whole sum.
  have hsingle := Finset.single_le_sum hnn hB₀
  rw [Finset.sum_sub_distrib] at hsingle
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE VARIANCE ATOM BOUND (n-cell energy excess)
-- ═══════════════════════════════════════════════════════════════════

/-- **Weighted-mean square identity (n cells).**  For nonnegative weights `w` on a
    finite index set `s`, the size-weighted second moment about the weighted mean
    `μ = (Σ wᵢxᵢ)/(Σ wᵢ)` splits as
    `Σ wᵢ(xᵢ − μ)² = Σ wᵢxᵢ² − (Σ wᵢ)·μ²`.
    This is the Finset generalization of `split_energy_identity` (the two-cell
    case): the excess of the second moment over the mean-squared is exactly the
    weighted variance.  The only hypothesis is `Σ wᵢ ≠ 0` (so `μ` is well defined). -/
theorem weighted_variance_identity {ι : Type*} (s : Finset ι) (w x : ι → ℚ)
    (hW : (∑ i ∈ s, w i) ≠ 0) :
    (∑ i ∈ s, w i * (x i - (∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j)) ^ 2) =
      (∑ i ∈ s, w i * x i ^ 2) -
        (∑ i ∈ s, w i) * ((∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j)) ^ 2 := by
  set μ : ℚ := (∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j) with hμ_def
  -- `μ` is the honest weighted mean: `(Σ wⱼ)·μ = Σ wⱼxⱼ`.
  have hμ : (∑ i ∈ s, w i) * μ = ∑ i ∈ s, w i * x i := by
    rw [hμ_def]; field_simp
  -- Expand the variance sum termwise, then collect the three sub-sums.
  have hexp : (∑ i ∈ s, w i * (x i - μ) ^ 2) =
      (∑ i ∈ s, w i * x i ^ 2) - 2 * μ * (∑ i ∈ s, w i * x i) +
        μ ^ 2 * (∑ i ∈ s, w i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hexp, ← hμ]; ring

/-- **The variance atom bound.**  If a single cell `i₀` carries weight at least
    `w₀ ≥ 0` and its value `x i₀` deviates from the weighted mean by at least
    `d ≥ 0`, then the weighted second-moment excess dominates `w₀·d²`:
    `Σ wᵢxᵢ² − (Σ wᵢ)·μ² ≥ w₀·d²`.

    This is the analytic core of the AFKS energy increment beyond the two-cell
    Cauchy–Schwarz `split_energy_excess_bound`.  When an ε-irregular pair is
    refined *simultaneously* on both coordinates into a family of sub-cells, the
    witness sub-cell is one atom of the resulting weighted distribution of
    densities whose deviation from the mean is bounded below; this lemma converts
    that single-atom deviation into a definite energy gain, with no reliance on
    triangle inequalities through mixed densities. -/
theorem variance_atom_bound {ι : Type*} (s : Finset ι) (w x : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hW : (∑ i ∈ s, w i) ≠ 0)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (w₀ d : ℚ) (hw₀ : 0 ≤ w₀) (hd : 0 ≤ d)
    (hwlb : w₀ ≤ w i₀)
    (hdev : d ≤ |x i₀ - (∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j)|) :
    w₀ * d ^ 2 ≤
      (∑ i ∈ s, w i * x i ^ 2) -
        (∑ i ∈ s, w i) * ((∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j)) ^ 2 := by
  set μ : ℚ := (∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j) with hμ_def
  -- Every variance term is nonnegative, so the whole sum dominates the `i₀` term.
  have hnn : ∀ i ∈ s, (0 : ℚ) ≤ w i * (x i - μ) ^ 2 :=
    fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hsingle : w i₀ * (x i₀ - μ) ^ 2 ≤ ∑ i ∈ s, w i * (x i - μ) ^ 2 :=
    Finset.single_le_sum hnn hi₀
  -- The `i₀` term itself dominates `w₀·d²`.
  have hsq : d ^ 2 ≤ (x i₀ - μ) ^ 2 := by
    calc d ^ 2 ≤ |x i₀ - μ| ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg (x i₀ - μ)]) hdev
      _ = (x i₀ - μ) ^ 2 := sq_abs _
  have hatom : w₀ * d ^ 2 ≤ w i₀ * (x i₀ - μ) ^ 2 := by
    calc w₀ * d ^ 2 ≤ w i₀ * d ^ 2 := mul_le_mul_of_nonneg_right hwlb (sq_nonneg d)
      _ ≤ w i₀ * (x i₀ - μ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (le_trans hw₀ hwlb)
  -- Combine with the variance identity.
  have hvar := weighted_variance_identity s w x hW
  rw [← hμ_def] at hvar
  linarith [hsingle, hatom, hvar]

/-- **Atom gain in mean-identity form.**  The directly consumable increment form of
    `variance_atom_bound`: instead of the internal weighted mean `(Σwx)/(Σw)`, it
    takes an *external* candidate mean `μ` together with the *mean identity*
    `Σ wᵢxᵢ = (Σ wᵢ)·μ` as a hypothesis, and concludes

      `(Σ wᵢ)·μ² + w₀·d² ≤ Σ wᵢxᵢ²`.

    This is exactly the shape a block-refinement energy increment needs: the
    coarse energy of a pair is `(Σ wᵢ)·μ²` with `μ = d(A,B)` the whole density and
    `Σ wᵢ = |A||B|/n²`; the refined energy is `Σ wᵢxᵢ²` over the sub-cells; and the
    mean identity is the *law of total density* `Σ|Aᵢ||Bⱼ|d(Aᵢ,Bⱼ) = |A||B|d(A,B)`.
    Discharging that identity turns a single deviating sub-cell into a definite
    energy gain `w₀·d²`, with no division and no reference to the internal mean. -/
theorem weighted_second_moment_atom_gain {ι : Type*} (s : Finset ι) (w x : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (μ : ℚ)
    (hmean : (∑ i ∈ s, w i * x i) = (∑ i ∈ s, w i) * μ)
    (i₀ : ι) (hi₀ : i₀ ∈ s) (w₀ d : ℚ) (hw₀ : 0 ≤ w₀) (hd : 0 ≤ d)
    (hwlb : w₀ ≤ w i₀) (hdev : d ≤ |x i₀ - μ|) :
    (∑ i ∈ s, w i) * μ ^ 2 + w₀ * d ^ 2 ≤ ∑ i ∈ s, w i * x i ^ 2 := by
  rcases eq_or_ne (∑ i ∈ s, w i) 0 with hW | hW
  · -- Total weight zero ⇒ every weight vanishes; both sides collapse to `0`.
    have hall : ∀ i ∈ s, w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW
    have hw0 : w₀ = 0 := le_antisymm (hall i₀ hi₀ ▸ hwlb) hw₀
    have hrhs : (∑ i ∈ s, w i * x i ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hall i hi]; ring)
    rw [hW, hw0, hrhs]; simp
  · -- Nonzero total weight ⇒ `μ` is the honest weighted mean; apply the atom bound.
    have hμ : μ = (∑ j ∈ s, w j * x j) / (∑ j ∈ s, w j) := by
      rw [hmean, eq_div_iff hW]; ring
    have hkey := variance_atom_bound s w x hw hW i₀ hi₀ w₀ d hw₀ hd hwlb
      (hμ ▸ hdev)
    rw [← hμ] at hkey
    linarith [hkey]

end Szemeredi.RegularityOQ04Energy
