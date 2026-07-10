/-
  Szemerédi Regularity Lemma — OQ-04: wiring the irregularity witness to the
  energy-increment hypothesis of the strong (AFKS) regularity lemma.

  The companion files supply the two structural halves of the AFKS iteration:

  * `SzemerediRegularityOQ04Energy` proves the *quantitative energy increment*
    `pairEnergy_split_gain` — refining a part into two halves whose densities to a
    fixed set `B` differ by at least `δ` raises the normalized energy by at least
    `(|A₁||A₂|/(|A₁|+|A₂|))·(|B|/n²)·δ²`.
  * `SzemerediRegularityOQ04Bridge` cashes that out to `partitionEnergy` and to the
    explicit `N ≤ 2n²/ε²` iteration count.

  Both consume a hypothesis of the shape `|d(A₁,B₀) − d(A₂,B₀)| ≥ δ`: a density
  gap *between the two halves of a split part*, measured against a common third
  set.  What the classical iteration actually produces (`exists_irregular_witness`,
  `SzemerediRegularity`) is different: subsets `A' ⊆ A`, `B' ⊆ B` whose *own*
  density `d(A',B')` deviates from the *pair* density `d(A,B)` by more than `ε`.
  Nothing previously connected the two shapes — the increment machinery sat
  disconnected from the only source of irregularity.

  This file supplies that missing bridge, fully machine-checked:

  * `edgeDensity_whole_between` — the convexity fact that `d(A₁∪A₂,B)` is the
    `|A₁|:|A₂|`-weighted mean of `d(A₁,B)` and `d(A₂,B)`, hence lies between them:
    `|d(A₁,B) − d(A₁∪A₂,B)| ≤ |d(A₁,B) − d(A₂,B)|`.  The whole is never farther
    from a half than the two halves are from each other.
  * `irregular_witness_split_gap` — the bridge: a witness deviation
    `|d(A',B') − d(A,B)| > ε` is dominated by the sum of two genuine
    *between-halves* gaps, one on each coordinate:
    `|d(A',B') − d(A∖A',B')| + |d(A,B') − d(A,B∖B')| > ε`.
  * `irregular_witness_split_gap_disjunction` — the consumable corollary: at least
    one coordinate carries a between-halves gap `> ε/2`, i.e. exactly the `hdev`
    hypothesis of `pairEnergy_split_gain`, on either the `A`-split (against `B'`)
    or the `B`-split (against `A`).

  The proof is a triangle inequality `|d(A',B')−d(A,B)| ≤ |d(A',B')−d(A,B')| +
  |d(A,B')−d(A,B)|` with each term collapsed onto a between-halves gap by
  `edgeDensity_whole_between` (the intermediate `d(A,B')` is the whole against a
  fixed side, hence sandwiched between the two halves' densities).

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Szemerédi (1978); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Energy
import Proofs.SzemerediRegularityOQ01

namespace Szemeredi.RegularityOQ04Witness

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE WHOLE LIES BETWEEN THE HALVES (DENSITY CONVEXITY)
-- ═══════════════════════════════════════════════════════════════════

/-- **The union density is a weighted mean of the halves.**  For a disjoint split
    `A₁, A₂` of the first argument, against a fixed nonempty `B`, the whole density
    `d(A₁∪A₂,B)` is the `|A₁|:|A₂|`-weighted average of `d(A₁,B)` and `d(A₂,B)`,
    hence never farther from a half than the two halves are from each other:

    `|d(A₁,B) − d(A₁∪A₂,B)| ≤ |d(A₁,B) − d(A₂,B)|`.

    This is what upgrades a *whole-vs-half* density gap into a *half-vs-half* gap of
    at least the same size — the shape the energy-increment lemma consumes. -/
theorem edgeDensity_whole_between (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hdisj : Disjoint A₁ A₂)
    (hB : 0 < (B.card : ℚ)) (hsum : 0 < (A₁.card : ℚ) + A₂.card) :
    |edgeDensity G A₁ B - edgeDensity G (A₁ ∪ A₂) B| ≤
      |edgeDensity G A₁ B - edgeDensity G A₂ B| := by
  have hBne : (B.card : ℚ) ≠ 0 := ne_of_gt hB
  -- Weighted-average identity, with the `|B|` factor cancelled.
  have hmul := edgeDensity_union_mul G A₁ A₂ B hdisj
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hdisj]; push_cast; ring
  rw [hcard] at hmul
  have hcan : ((A₁.card : ℚ) + A₂.card) * edgeDensity G (A₁ ∪ A₂) B =
      (A₁.card : ℚ) * edgeDensity G A₁ B + (A₂.card : ℚ) * edgeDensity G A₂ B :=
    mul_left_cancel₀ hBne (by linear_combination hmul)
  -- Solve for the whole-vs-half discrepancy: `(a₁+a₂)(g₁-gu) = a₂(g₁-g₂)`.
  have hcancel : ((A₁.card : ℚ) + A₂.card) *
        (edgeDensity G A₁ B - edgeDensity G (A₁ ∪ A₂) B) =
      (A₂.card : ℚ) * (edgeDensity G A₁ B - edgeDensity G A₂ B) := by
    linear_combination -hcan
  have ha₁ : 0 ≤ (A₁.card : ℚ) := by positivity
  have ha₂ : 0 ≤ (A₂.card : ℚ) := by positivity
  -- Abbreviate; `set` now folds the goal, `hcancel`, `hsum`, `ha₁`, `ha₂`.
  set g₁ := edgeDensity G A₁ B
  set g₂ := edgeDensity G A₂ B
  set gu := edgeDensity G (A₁ ∪ A₂) B
  set a₁ := (A₁.card : ℚ)
  set a₂ := (A₂.card : ℚ)
  -- Take absolute values: `(a₁+a₂)·|g₁-gu| = a₂·|g₁-g₂|`.
  have h1 : (a₁ + a₂) * |g₁ - gu| = a₂ * |g₁ - g₂| := by
    have hcong := congrArg abs hcancel
    rwa [abs_mul, abs_mul, abs_of_pos hsum, abs_of_nonneg ha₂] at hcong
  -- Since `a₂ ≤ a₁ + a₂`, the right side is `≤ (a₁+a₂)·|g₁-g₂|`.
  have h2 : a₂ * |g₁ - g₂| ≤ (a₁ + a₂) * |g₁ - g₂| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have h3 : (a₁ + a₂) * |g₁ - gu| ≤ (a₁ + a₂) * |g₁ - g₂| := by rw [h1]; exact h2
  exact le_of_mul_le_mul_left h3 hsum

/-- Second-argument form: the whole `d(A, B₁∪B₂)` lies between the two halves
    `d(A,B₁)` and `d(A,B₂)`.  Obtained from `edgeDensity_whole_between` by symmetry
    of `edgeDensity`. -/
theorem edgeDensity_whole_between_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ B₂ : Finset V) (hdisj : Disjoint B₁ B₂)
    (hA : 0 < (A.card : ℚ)) (hsum : 0 < (B₁.card : ℚ) + B₂.card) :
    |edgeDensity G A B₁ - edgeDensity G A (B₁ ∪ B₂)| ≤
      |edgeDensity G A B₁ - edgeDensity G A B₂| := by
  have h := edgeDensity_whole_between G B₁ B₂ A hdisj hA hsum
  rwa [Szemeredi.Regularity.OQ01.edgeDensity_comm G B₁ A,
    Szemeredi.Regularity.OQ01.edgeDensity_comm G (B₁ ∪ B₂) A,
    Szemeredi.Regularity.OQ01.edgeDensity_comm G B₂ A] at h

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE BRIDGE — WITNESS DEVIATION ⟹ BETWEEN-HALVES GAPS
-- ═══════════════════════════════════════════════════════════════════

/-- **The irregularity-witness bridge.**  Let `A' ⊆ A`, `B' ⊆ B` be an
    irregularity witness: their density `d(A',B')` deviates from the pair density
    `d(A,B)` by more than `ε`.  Then that deviation is dominated by the sum of two
    genuine *between-halves* density gaps — one from splitting `A` into `A', A∖A'`
    (measured against the fixed set `B'`), one from splitting `B` into `B', B∖B'`
    (measured against the fixed set `A`):

    `|d(A',B') − d(A∖A',B')| + |d(A,B') − d(A,B∖B')| > ε`.

    Proof: triangle-inequality through the intermediate density `d(A,B')`, then
    collapse each leg with `edgeDensity_whole_between` — `d(A,B') = d(A'∪(A∖A'),B')`
    is sandwiched between `d(A',B')` and `d(A∖A',B')`, and `d(A,B) =
    d(A,B'∪(B∖B'))` between `d(A,B')` and `d(A,B∖B')`.  This turns the abstract
    witness of `exists_irregular_witness` into the concrete half-vs-half gap that
    `pairEnergy_split_gain` requires. -/
theorem irregular_witness_split_gap (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (A B A' B' : Finset V) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hA : 0 < (A.card : ℚ)) (hB : 0 < (B.card : ℚ)) (hB'pos : 0 < (B'.card : ℚ))
    (hdev : |edgeDensity G A' B' - edgeDensity G A B| > ε) :
    |edgeDensity G A' B' - edgeDensity G (A \ A') B'| +
        |edgeDensity G A B' - edgeDensity G A (B \ B')| > ε := by
  -- `A' ⊔ (A ∖ A') = A` and `B' ⊔ (B ∖ B') = B`.
  have hAunion : A' ∪ (A \ A') = A := Finset.union_sdiff_of_subset hA'
  have hBunion : B' ∪ (B \ B') = B := Finset.union_sdiff_of_subset hB'
  have hAdisj : Disjoint A' (A \ A') := Finset.disjoint_sdiff
  have hBdisj : Disjoint B' (B \ B') := Finset.disjoint_sdiff
  -- Size of the `A`-side halves sums to `|A| > 0`; likewise on the `B`-side.
  have hAsum : 0 < (A'.card : ℚ) + (A \ A').card := by
    have : (A'.card : ℚ) + ((A \ A').card : ℚ) = (A.card : ℚ) := by
      rw [add_comm]; exact_mod_cast Finset.card_sdiff_add_card_eq_card hA'
    rw [this]; exact hA
  have hBsum : 0 < (B'.card : ℚ) + (B \ B').card := by
    have : (B'.card : ℚ) + ((B \ B').card : ℚ) = (B.card : ℚ) := by
      rw [add_comm]; exact_mod_cast Finset.card_sdiff_add_card_eq_card hB'
    rw [this]; exact hB
  -- A-leg: `|d(A',B') − d(A,B')| ≤ |d(A',B') − d(A∖A',B')|`.
  have hAleg : |edgeDensity G A' B' - edgeDensity G A B'| ≤
      |edgeDensity G A' B' - edgeDensity G (A \ A') B'| := by
    have h := edgeDensity_whole_between G A' (A \ A') B' hAdisj hB'pos hAsum
    rwa [hAunion] at h
  -- B-leg: `|d(A,B') − d(A,B)| ≤ |d(A,B') − d(A,B∖B')|`.
  have hBleg : |edgeDensity G A B' - edgeDensity G A B| ≤
      |edgeDensity G A B' - edgeDensity G A (B \ B')| := by
    have h := edgeDensity_whole_between_right G A B' (B \ B') hBdisj hA hBsum
    rwa [hBunion] at h
  -- Triangle inequality through the intermediate density `d(A, B')`.
  have htri : |edgeDensity G A' B' - edgeDensity G A B| ≤
      |edgeDensity G A' B' - edgeDensity G A B'| +
        |edgeDensity G A B' - edgeDensity G A B| := by
    have := abs_sub_le (edgeDensity G A' B') (edgeDensity G A B') (edgeDensity G A B)
    linarith
  linarith

/-- **Consumable disjunction.**  From the witness deviation `> ε`, at least one
    coordinate carries a between-halves density gap `> ε/2`: either splitting the
    `A`-side against the fixed set `B'`, or splitting the `B`-side against the fixed
    set `A`.  Each disjunct is *exactly* the `hdev` hypothesis of
    `pairEnergy_split_gain` (with `δ = ε/2`), so this closes the loop from
    `exists_irregular_witness` to a definite `partitionEnergy` increment. -/
theorem irregular_witness_split_gap_disjunction (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (ε : ℚ) (A B A' B' : Finset V) (hA' : A' ⊆ A) (hB' : B' ⊆ B)
    (hA : 0 < (A.card : ℚ)) (hB : 0 < (B.card : ℚ)) (hB'pos : 0 < (B'.card : ℚ))
    (hdev : |edgeDensity G A' B' - edgeDensity G A B| > ε) :
    |edgeDensity G A' B' - edgeDensity G (A \ A') B'| > ε / 2 ∨
      |edgeDensity G A B' - edgeDensity G A (B \ B')| > ε / 2 := by
  have hsum := irregular_witness_split_gap G ε A B A' B' hA' hB' hA hB hB'pos hdev
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE WHOLE DENSITY LIES IN THE CLOSED HALVES-INTERVAL
-- ═══════════════════════════════════════════════════════════════════

/-- **Convex-combination betweenness.**  The whole density `d(A₁∪A₂, B)` is the
    `|A₁|:|A₂|`-weighted mean of the two half densities, hence lies in the closed
    interval bounded by them:

    `min (d(A₁,B)) (d(A₂,B)) ≤ d(A₁∪A₂,B) ≤ max (d(A₁,B)) (d(A₂,B))`.

    This is the literal "lies between" content backing the distance bound
    `edgeDensity_whole_between`: refining a part can never push its density outside
    the range already spanned by the two halves. -/
theorem edgeDensity_whole_mem_Icc (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hdisj : Disjoint A₁ A₂)
    (hB : 0 < (B.card : ℚ)) (hsum : 0 < (A₁.card : ℚ) + A₂.card) :
    min (edgeDensity G A₁ B) (edgeDensity G A₂ B) ≤ edgeDensity G (A₁ ∪ A₂) B ∧
      edgeDensity G (A₁ ∪ A₂) B ≤ max (edgeDensity G A₁ B) (edgeDensity G A₂ B) := by
  have hBne : (B.card : ℚ) ≠ 0 := ne_of_gt hB
  have hmul := edgeDensity_union_mul G A₁ A₂ B hdisj
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hdisj]; push_cast; ring
  rw [hcard] at hmul
  have hcan : ((A₁.card : ℚ) + A₂.card) * edgeDensity G (A₁ ∪ A₂) B =
      (A₁.card : ℚ) * edgeDensity G A₁ B + (A₂.card : ℚ) * edgeDensity G A₂ B :=
    mul_left_cancel₀ hBne (by linear_combination hmul)
  have ha₁ : 0 ≤ (A₁.card : ℚ) := by positivity
  have ha₂ : 0 ≤ (A₂.card : ℚ) := by positivity
  set g₁ := edgeDensity G A₁ B
  set g₂ := edgeDensity G A₂ B
  set gu := edgeDensity G (A₁ ∪ A₂) B
  set a₁ := (A₁.card : ℚ)
  set a₂ := (A₂.card : ℚ)
  refine ⟨?_, ?_⟩
  · -- lower bound: `min` is dominated by the convex combination.
    have h1 : a₁ * min g₁ g₂ ≤ a₁ * g₁ := mul_le_mul_of_nonneg_left (min_le_left _ _) ha₁
    have h2 : a₂ * min g₁ g₂ ≤ a₂ * g₂ := mul_le_mul_of_nonneg_left (min_le_right _ _) ha₂
    have hlb : (a₁ + a₂) * min g₁ g₂ ≤ (a₁ + a₂) * gu := by rw [hcan]; nlinarith [h1, h2]
    exact le_of_mul_le_mul_left hlb hsum
  · -- upper bound: the convex combination is dominated by `max`.
    have h1 : a₁ * g₁ ≤ a₁ * max g₁ g₂ := mul_le_mul_of_nonneg_left (le_max_left _ _) ha₁
    have h2 : a₂ * g₂ ≤ a₂ * max g₁ g₂ := mul_le_mul_of_nonneg_left (le_max_right _ _) ha₂
    have hub : (a₁ + a₂) * gu ≤ (a₁ + a₂) * max g₁ g₂ := by rw [hcan]; nlinarith [h1, h2]
    exact le_of_mul_le_mul_left hub hsum

/-- Second-argument form of `edgeDensity_whole_mem_Icc`: the whole density
    `d(A, B₁∪B₂)` lies in the closed interval spanned by `d(A,B₁)` and `d(A,B₂)`.
    Obtained by symmetry of `edgeDensity`. -/
theorem edgeDensity_whole_mem_Icc_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B₁ B₂ : Finset V) (hdisj : Disjoint B₁ B₂)
    (hA : 0 < (A.card : ℚ)) (hsum : 0 < (B₁.card : ℚ) + B₂.card) :
    min (edgeDensity G A B₁) (edgeDensity G A B₂) ≤ edgeDensity G A (B₁ ∪ B₂) ∧
      edgeDensity G A (B₁ ∪ B₂) ≤ max (edgeDensity G A B₁) (edgeDensity G A B₂) := by
  have h := edgeDensity_whole_mem_Icc G B₁ B₂ A hdisj hA hsum
  rwa [Szemeredi.Regularity.OQ01.edgeDensity_comm G B₁ A,
    Szemeredi.Regularity.OQ01.edgeDensity_comm G (B₁ ∪ B₂) A,
    Szemeredi.Regularity.OQ01.edgeDensity_comm G B₂ A] at h

end Szemeredi.RegularityOQ04Witness
