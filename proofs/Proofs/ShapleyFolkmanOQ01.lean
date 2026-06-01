/-
  Shapley–Folkman OQ-01: literal infinite-dim extension is vacuous;
  finite-dim tightness counter-example shows the `Module.finrank` bound is sharp.

  Companion file to `proofs/Proofs/ShapleyFolkman.lean` (parent, verified).
  See `research/problems/shapley-folkman-oq-01/` (S1–S4 PREP chain) for full design.

  Open question (seeker-stated): can `[FiniteDimensional ℝ E]` be dropped from
  `shapley_folkman` by replacing `Module.finrank ℝ E` with a suitable infinite-dim
  dimension notion?

  Negative answer (S1 OBSERVE PR #18345 + S1b PREP PR #18414): NO. In Lean's
  convention `Module.finrank ℝ E = 0` for any non-finite-dim `ℝ`-module, so the
  literal bound collapses to "0 excess indices", vacuously false for a non-convex
  Minkowski sum. The correct infinite-dim analogs are Aumann (1965) set-valued
  integrals and Lyapunov (1940) vector-measure convexity — neither in Mathlib.

  This file (Approach C, narrowest negative result): in `EuclideanSpace ℝ (Fin N)`
  with `S i = {0, e_i}` and `x = (1/2) • ∑ e_i`, every `Decomposition` of `x` has
  `excessIndices.card = N`. This shows the parent bound `card ≤ Module.finrank ℝ E`
  is sharp (achieved with equality) for any N, so no smaller bound — and in
  particular no infinite-dim extension that bounds the excess count by a fixed
  finite number — can hold.

  Status: S2-A ACT-1 scaffold. Three named results, all proofs `sorry`-stubbed,
  pending Lake build verification. See README in `research/problems/...` for the
  proof skeleton (S3 PREP §3.1 helper, S3 PREP §4 coordinate-eval route).
-/

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Proofs.ShapleyFolkman

set_option linter.unusedVariables false

namespace ShapleyFolkmanOQ01

open Set Finset Pointwise ShapleyFolkman

-- Mirror the parent's local-instance hack so `Decomposition.excessIndices`
-- unfolds cleanly via `simp [Decomposition.excessIndices]` inside this file.
-- See S4 PREP §3 / §7.3 for justification.
attribute [local instance] Classical.propDecidable

/-- Pair-convex-hull parameter extraction (S3 PREP §3.1 + S3b PREP §3.3 corrections).

    From `y ∈ convexHull ℝ {0, e_i}` extract `t ∈ [0, 1]` with `y = t • e_i`.
    The load-bearing helper for the tightness theorem below: applied N times
    to a decomposition `D` gives a function `t : Fin N → ℝ` such that
    `D.point i = t i • EuclideanSpace.single i 1` for every `i`.

    **Mathlib v4.26.0 chain**:
    - `Mathlib/Analysis/Convex/Hull.lean:124` — `convexHull_pair`.
    - `Mathlib/Analysis/Convex/Segment.lean:50` — `def segment` (existential unpack).
-/
lemma convexHull_pair_zero_basis_extract
    {N : ℕ} {i : Fin N} {y : EuclideanSpace ℝ (Fin N)}
    (hy : y ∈ convexHull ℝ
            ({0, EuclideanSpace.single i 1} : Set (EuclideanSpace ℝ (Fin N)))) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ y = t • EuclideanSpace.single i 1 := by
  rw [convexHull_pair] at hy
  -- hy : y ∈ segment ℝ (0 : EuclideanSpace ℝ (Fin N)) (EuclideanSpace.single i 1)
  rcases hy with ⟨a, b, ha, hb, hab, heq⟩
  -- a, b : ℝ; ha : 0 ≤ a; hb : 0 ≤ b; hab : a + b = 1;
  -- heq : a • 0 + b • EuclideanSpace.single i 1 = y
  refine ⟨b, ⟨hb, ?_⟩, ?_⟩
  · -- b ≤ 1 from a + b = 1 and 0 ≤ a
    linarith
  · -- y = b • EuclideanSpace.single i 1
    rw [smul_zero, zero_add] at heq
    exact heq.symm

/-- The counter-example point lies in the convex hull of the Minkowski sum.

    `x = (1/2) • 0 + (1/2) • (∑ e_i)` is the midpoint of two points in `∑ S_i`:
    the all-zeros vector (via `0 ∈ S_i` for every `i`) and the all-ones-in-axes
    vector `∑ e_i` (via `e_i ∈ S_i` for every `i`).

    S2b PREP §2 verifies this numerically at `N = 1, 2, 3, 4`.

    Build-pending: proof structure is straightforward (`Set.add_mem_finset_sum`
    twice + `convex_combo_mem` for the midpoint), but exact Mathlib lemma names
    need build-time confirmation.
-/
theorem mem_convexHull_finset_sum (N : ℕ) :
    ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) :
        EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ
          (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
              Set (EuclideanSpace ℝ (Fin N)))) := by
  -- Step 1: 0 ∈ ∑ S_i, witness g i = 0 ∈ S_i = {0, e_i}.
  have h0 : (0 : EuclideanSpace ℝ (Fin N)) ∈
      (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
          Set (EuclideanSpace ℝ (Fin N)))) := by
    have hzero : (0 : EuclideanSpace ℝ (Fin N))
        = ∑ i : Fin N, (0 : EuclideanSpace ℝ (Fin N)) := by simp
    rw [hzero]
    exact Set.finset_sum_mem_finset_sum (Finset.univ) _ _
      (fun i _ => by simp)
  -- Step 2: ∑ e_i ∈ ∑ S_i, witness g i = e_i ∈ S_i = {0, e_i}.
  have hsum : (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) ∈
      (∑ i : Fin N, ({0, EuclideanSpace.single i 1} :
          Set (EuclideanSpace ℝ (Fin N)))) :=
    Set.finset_sum_mem_finset_sum (Finset.univ) _ _
      (fun i _ => by
        right
        rfl)
  -- Step 3: rewrite x as midpoint of 0 and ∑ e_i.
  have hmid :
      ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)))
        = (1 / 2 : ℝ) • (0 : EuclideanSpace ℝ (Fin N))
          + (1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) := by
    rw [smul_zero, zero_add]
  rw [hmid]
  -- Step 4: apply convexity of the convex hull.
  exact (convex_convexHull ℝ _)
    (subset_convexHull ℝ _ h0)
    (subset_convexHull ℝ _ hsum)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

/-- **Tightness of Shapley–Folkman in `EuclideanSpace ℝ (Fin N)`**.

    For the counter-example construction `S i = {0, e_i}` and
    `x = (1/2) • ∑ e_i`, every `Decomposition` of `x` has full excess:
    `excessIndices.card = N`.

    Combined with the parent `shapley_folkman` bound `card ≤ Module.finrank ℝ E`
    (which equals `N` here via `finrank_euclideanSpace_fin`), this shows the
    parent's bound is **sharp** for every `N`. In particular, no infinite-dim
    extension that bounds excess by a fixed finite number can hold: as `N → ∞`,
    the required excess count grows without bound.

    Proof strategy (S3 PREP §4, S4 PREP §3.2):
    1. Apply `convexHull_pair_zero_basis_extract` for each `i` to get
       `t : Fin N → ℝ` with `t i ∈ [0,1]` and `D.point i = t i • e_i`.
    2. Evaluate `D.sum_eq` at coordinate `j` via `EuclideanSpace.single_apply`:
       LHS becomes `t j`, RHS becomes `1/2`. So `t j = 1/2` for every `j`.
    3. Show `(1/2) • e_j ∉ S j = {0, e_j}`:
       - `(1/2) • e_j ≠ 0`: `smul_ne_zero` + `single_eq_zero_iff` + `1 ≠ 0`.
       - `(1/2) • e_j ≠ e_j`: coordinate-eval at `j` gives `1/2 = 1`, false.
    4. So `D.excessIndices = Finset.univ`, `card = N`.

    Build-pending: see S3 PREP and S3b PREP for the verbatim Mathlib citations.
-/
theorem tight_excess_count (N : ℕ) :
    ∀ (D : ShapleyFolkman.Decomposition
            (fun i : Fin N =>
              ({0, EuclideanSpace.single i 1} :
                  Set (EuclideanSpace ℝ (Fin N))))
            (Finset.univ : Finset (Fin N))
            ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) :
                EuclideanSpace ℝ (Fin N))),
      D.excessIndices.card = N := by
  intro D
  -- Step 1: For each i, extract t i ∈ [0, 1] with D.point i = (t i) • e_i.
  have h_pt : ∀ i : Fin N,
      ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1
        ∧ D.point i = s • EuclideanSpace.single i 1 := by
    intro i
    exact convexHull_pair_zero_basis_extract (D.mem_convexHull i (Finset.mem_univ i))
  -- Step 2: Materialise t : Fin N → ℝ via choose.
  choose t ht_in ht_eq using h_pt
  -- Step 3: Rewrite D.sum_eq under the sum binder using ht_eq.
  have h_sum : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                : EuclideanSpace ℝ (Fin N))
        = (1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) := by
    have hk := D.sum_eq
    simp_rw [ht_eq] at hk
    exact hk
  -- Step 4: Coordinate-evaluate at j to force t j = 1/2.
  have h_tj : ∀ j : Fin N, t j = 1 / 2 := by
    intro j
    have h_eval : (∑ i : Fin N, t i • EuclideanSpace.single i (1 : ℝ)
                      : EuclideanSpace ℝ (Fin N)) j
                  = ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) j :=
      congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h_sum
    simp [Finset.sum_apply, PiLp.smul_apply, Pi.single_apply,
          mul_ite, mul_one, mul_zero,
          Finset.mem_univ] at h_eval
    linarith
  -- Step 5: Every j ∈ excessIndices (i.e., D.point j = (1/2) • e_j ∉ {0, e_j}).
  have h_excess : ∀ j : Fin N, j ∈ D.excessIndices := by
    intro j
    simp only [ShapleyFolkman.Decomposition.excessIndices, Finset.mem_filter,
               Finset.mem_univ, true_and]
    rw [ht_eq j, h_tj j]
    intro h_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem
    rcases h_mem with h0 | h1
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h0
      simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
    · have hcoord := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v j) h1
      simp [PiLp.smul_apply, EuclideanSpace.single_apply] at hcoord
  -- Step 6: excessIndices = univ, so card = N.
  rw [show D.excessIndices = Finset.univ from
      Finset.eq_univ_iff_forall.mpr h_excess,
      Finset.card_univ, Fintype.card_fin]

/-- **Sharpness corollary** (S2-A ACT-3). For the tightness configuration
    `S i = {0, e_i}` and `x = (1/2) • ∑ e_i` in `EuclideanSpace ℝ (Fin N)`,
    every `ShapleyFolkman.Decomposition` of `x` achieves
    `excessIndices.card = Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N`.

    Combined with the parent `shapley_folkman` upper bound
    `card ≤ Module.finrank ℝ E`, this shows the parent's bound is sharp:
    cannot be reduced to a smaller universal bound, since this concrete
    `EuclideanSpace ℝ (Fin N)` example forces equality with the dimension.

    This is the direct corollary of `tight_excess_count` modulo
    `finrank_euclideanSpace_fin` (which evaluates the `EuclideanSpace`
    finrank to `N`). -/
theorem tight_excess_eq_finrank (N : ℕ)
    (D : ShapleyFolkman.Decomposition
            (fun i : Fin N =>
              ({0, EuclideanSpace.single i 1} :
                  Set (EuclideanSpace ℝ (Fin N))))
            (Finset.univ : Finset (Fin N))
            ((1 / 2 : ℝ) • (∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) :
                EuclideanSpace ℝ (Fin N))) :
    D.excessIndices.card =
        Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) := by
  rw [tight_excess_count N D, finrank_euclideanSpace_fin]

end ShapleyFolkmanOQ01
