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

  Status: built out across S2–S20. The Approach-C result is fully assembled —
  `no_universal_shapley_folkman_bound` (capstone), `exists_tight_decomposition`,
  `tight_excess_count`/`tight_excess_eq_finrank`, plus the `Decomposition.map`
  transport core — with **no `sorry`** remaining in any proof body. Build
  verification is pending a Docker `lake` build (Docker daemon down per the
  2026-06-13 blackout); see `research/problems/...` state.md for the per-session
  bearer-pinning and fallback registers.
-/

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Lp.lpSpace
import Proofs.ShapleyFolkman

set_option linter.unusedVariables false

namespace ShapleyFolkman

attribute [local instance] Classical.propDecidable

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- **Transport a decomposition along a linear map** `f : E →ₗ[ℝ] F`.

    The image summands `f (D.point i)` decompose `f x` over the image families
    `fun i => f '' S i`. Each field follows from linearity:
    membership via `LinearMap.image_convexHull`, the off-support vanishing via
    `map_zero`, and the sum constraint via `map_sum`.

    This is the reusable engine behind cross-ambient Shapley–Folkman transfer.
    It is what lets the finite-dimensional tightness witnesses of this file be
    pushed forward along an embedding `EuclideanSpace ℝ (Fin N) →ₗ[ℝ] ℓ²`
    (the S2-B₂ lift; see `research/problems/shapley-folkman-oq-01/`). -/
noncomputable def Decomposition.map {ι : Type*} {S : ι → Set E} {t : Finset ι}
    {x : E} (D : Decomposition S t x) (f : E →ₗ[ℝ] F) :
    Decomposition (fun i => f '' S i) t (f x) where
  point i := f (D.point i)
  mem_convexHull i hi := by
    show f (D.point i) ∈ convexHull ℝ (f '' S i)
    rw [← LinearMap.image_convexHull]
    exact Set.mem_image_of_mem f (D.mem_convexHull i hi)
  point_eq_zero i hi := by rw [D.point_eq_zero i hi, map_zero]
  sum_eq := by rw [← map_sum]; exact congrArg f D.sum_eq

@[simp]
lemma Decomposition.map_point {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (D : Decomposition S t x) (f : E →ₗ[ℝ] F) (i : ι) :
    (D.map f).point i = f (D.point i) := rfl

/-- **An injective linear map preserves the excess-index set.**

    Because `f` is injective, `f (D.point i) ∈ f '' S i ↔ D.point i ∈ S i`
    (`Function.Injective.mem_set_image`), so the filtered index sets coincide.
    Injectivity is exactly the hypothesis that lets the *negative* (tightness)
    result transfer along an embedding: the excess count cannot collapse under
    the image. -/
lemma Decomposition.map_excessIndices_of_injective {ι : Type*} {S : ι → Set E}
    {t : Finset ι} {x : E} (D : Decomposition S t x) {f : E →ₗ[ℝ] F}
    (hf : Function.Injective f) :
    (D.map f).excessIndices = D.excessIndices := by
  simp only [Decomposition.excessIndices, Decomposition.map_point]
  exact Finset.filter_congr fun i _ => by rw [hf.mem_set_image]

/-- Cardinality form of `map_excessIndices_of_injective`: the directly usable
    statement for transferring tightness bounds across an embedding. -/
lemma Decomposition.map_excessIndices_card_of_injective {ι : Type*} {S : ι → Set E}
    {t : Finset ι} {x : E} (D : Decomposition S t x) {f : E →ₗ[ℝ] F}
    (hf : Function.Injective f) :
    (D.map f).excessIndices.card = D.excessIndices.card := by
  rw [D.map_excessIndices_of_injective hf]

end ShapleyFolkman

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

    `x = (1/2) • 0 + (1/2) • (∑ e_i)` is the midpoint of two points ∈ `∑ S_i`:
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
    `S i = {0, e_i}` and `x = (1/2) • ∑ e_i` ∈ `EuclideanSpace ℝ (Fin N)`,
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

/-- **S2-A ACT-4 helper**. The midpoint `(1/2) • e_i` lies in the convex
    hull of `{0, e_i}`. This is the per-`i` membership statement needed
    by `midpointDecomp.mem_convexHull` below.

    Proof: `(1/2) • e_i = (1/2) • 0 + (1/2) • e_i` is a convex combination
    of `0 ∈ {0, e_i}` and `e_i ∈ {0, e_i}` with weights `(1/2, 1/2)`.
    Discharged by the same `convex_convexHull` + `subset_convexHull` chain
    used by `mem_convexHull_finset_sum`. -/
lemma midpoint_mem_convexHull_pair_zero_basis {N : ℕ} (i : Fin N) :
    ((1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) :
        EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ
          ({0, EuclideanSpace.single i 1} :
              Set (EuclideanSpace ℝ (Fin N))) := by
  have h0 : (0 : EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N))) :=
    subset_convexHull ℝ _ (by simp)
  have he : (EuclideanSpace.single i (1 : ℝ) :
                EuclideanSpace ℝ (Fin N))
      ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N))) :=
    subset_convexHull ℝ _ (by simp)
  have hmid :
      ((1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) :
          EuclideanSpace ℝ (Fin N))
        = (1 / 2 : ℝ) • (0 : EuclideanSpace ℝ (Fin N))
          + (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
    rw [smul_zero, zero_add]
  rw [hmid]
  exact (convex_convexHull ℝ _) h0 he
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

/-- **S2-A ACT-4 construction**. The natural midpoint decomposition of
    `(1/2) • ∑ e_i` ∈ `EuclideanSpace ℝ (Fin N)`: each summand
    `point i = (1/2) • e_i` is in `convexHull ℝ {0, e_i}` (via
    `midpoint_mem_convexHull_pair_zero_basis`) and the summands add up
    to the target.

    This is the existence witness for the S2-A ACT-3 sharpness corollary's
    parameterised statement. -/
noncomputable def midpointDecomp (N : ℕ) :
    ShapleyFolkman.Decomposition
      (fun i : Fin N =>
        ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N))))
      (Finset.univ : Finset (Fin N))
      ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ)) where
  point i := (1 / 2 : ℝ) • EuclideanSpace.single i (1 : ℝ)
  mem_convexHull i _ := midpoint_mem_convexHull_pair_zero_basis i
  point_eq_zero i hi := absurd (Finset.mem_univ i) hi
  sum_eq := by
    rw [← Finset.smul_sum]

/-- **S2-A ACT-4 main result** (existence form of the sharpness corollary).
    Combines `midpointDecomp` (existence witness) with the
    `tight_excess_eq_finrank` corollary (S2-A ACT-3) to assert that the
    parent `shapley_folkman` upper bound `card ≤ Module.finrank ℝ E` is
    achieved with equality by an explicit decomposition.

    Together with `tight_excess_count` (universal: every decomposition has
    `card = N`), this completes the S2-A line of the OQ01 work: the parent
    bound is sharp on this concrete example, both **achievable** (this
    theorem) and **unavoidable** (`tight_excess_count`). -/
theorem exists_tight_decomposition (N : ℕ) :
    ∃ D : ShapleyFolkman.Decomposition
            (fun i : Fin N =>
              ({0, EuclideanSpace.single i 1} :
                  Set (EuclideanSpace ℝ (Fin N))))
            (Finset.univ : Finset (Fin N))
            ((1 / 2 : ℝ) • ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) :
                EuclideanSpace ℝ (Fin N)),
      D.excessIndices.card =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) :=
  ⟨midpointDecomp N, tight_excess_eq_finrank N (midpointDecomp N)⟩

/-- **S2-B₁ — No universal Shapley–Folkman bound across ambient spaces.**
    For every candidate bound `K : ℕ`, there is an ambient (here
    `EuclideanSpace ℝ (Fin (K+1))`), a finite family
    `S : Fin (K+1) → Set _`, and a target point `x` such that **every**
    `Decomposition` of `x` has `excessIndices.card > K`.

    This is the truncation-lift refutation: a single `Nat` bound `K`
    fails on the dimension `K+1` example. Combined with the parent
    `shapley_folkman` (where the actual bound is `Module.finrank ℝ E`),
    this shows the dimension dependence in the bound is unavoidable:
    no bound replacement that ignores ambient dimension can survive
    even within finite-dim ambients of growing dimension.

    Companion to `tight_excess_eq_finrank` (S2-A ACT-3, parameterised
    sharpness): together they characterise the parent bound as
    `card = Module.finrank ℝ E` on the tight midpoint family. -/
theorem no_universal_shapley_folkman_bound :
    ∀ K : ℕ,
      ∃ (D : ShapleyFolkman.Decomposition
              (fun i : Fin (K + 1) =>
                ({0, EuclideanSpace.single i 1} :
                    Set (EuclideanSpace ℝ (Fin (K + 1)))))
              (Finset.univ : Finset (Fin (K + 1)))
              ((1 / 2 : ℝ)
                • ∑ i : Fin (K + 1), EuclideanSpace.single i (1 : ℝ) :
                    EuclideanSpace ℝ (Fin (K + 1)))),
        D.excessIndices.card > K := by
  intro K
  refine ⟨midpointDecomp (K + 1), ?_⟩
  rw [tight_excess_count (K + 1) (midpointDecomp (K + 1))]
  exact Nat.lt_succ_self K

/-! ### S2-D — the genuine `ℓ²` infinite-dimensional lift

    The results above live in `EuclideanSpace ℝ (Fin N)`, which is
    finite-dimensional; they show the parent `Module.finrank` bound is *sharp*
    but stay inside finite dimensions. This section carries the tightness family
    into the honest infinite-dimensional Hilbert space `ℓ² = lp (fun _ : ℕ => ℝ) 2`
    via an injective linear embedding `ιN : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] ℓ²`
    and the `Decomposition.map` transport core, producing a *literal* family of
    subsets of `ℓ²` whose Shapley–Folkman excess count is unbounded. Since
    `Module.finrank ℝ ℓ² = 0`, this refutes the literal `card ≤ finrank` parent
    bound in `ℓ²` and confirms the negative answer to OQ-01: the finite-dimensional
    hypothesis cannot be dropped. -/

/-- **The embedding** `EuclideanSpace ℝ (Fin N) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2`.

    A finite sum of single-coordinate injections: coordinate `i : Fin N` of the
    input is placed at coordinate `i.val : ℕ` of the `ℓ²` output via `lp.lsingle`. -/
noncomputable def ιN (N : ℕ) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 where
  toFun v := ∑ i : Fin N, lp.lsingle 2 (i.val) (v i)
  map_add' v w := by
    simp only [PiLp.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [PiLp.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

/-- Coordinate `j.val` of `ιN N v` is exactly `v j`: distinct `Fin N` indices
    land at distinct `ℕ` coordinates, so the single-coordinate injections do not
    interfere. -/
lemma ιN_apply_coord (N : ℕ) (v : EuclideanSpace ℝ (Fin N)) (j : Fin N) :
    (ιN N v : ℕ → ℝ) j.val = v j := by
  have hcoe : (ιN N v : ℕ → ℝ)
      = ∑ i : Fin N, (Pi.single (i.val) (v i) : ℕ → ℝ) := by
    simp only [ιN, LinearMap.coe_mk, AddHom.coe_mk, lp.coeFn_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← lp.coeFn_single 2 (i.val) (v i)]
  rw [hcoe, Finset.sum_apply]
  simp only [Pi.single_apply, Fin.val_eq_val]
  exact Fintype.sum_ite_eq j (fun i => v i)

/-- `ιN N` is injective (it preserves every coordinate). -/
lemma ιN_injective (N : ℕ) : Function.Injective (ιN N) := by
  intro v w h
  ext j
  have hj := congrArg (fun y : lp (fun _ : ℕ => ℝ) 2 => (y : ℕ → ℝ) (j.val)) h
  simpa only [ιN_apply_coord] using hj

/-- **S2-D — Shapley–Folkman excess is unbounded in `ℓ²`.**
    For every candidate bound `K : ℕ` there is a finite family of subsets of the
    genuine infinite-dimensional Hilbert space `lp (fun _ : ℕ => ℝ) 2` (the images
    under `ιN` of the finite-dimensional tightness family) and a target point whose
    every `Decomposition` has `excessIndices.card > K`.

    This is the honest infinite-dimensional negative result: the excess count is
    unbounded in `ℓ²`, lifted from the `Fin N` tightness (`tight_excess_count`) via
    the injective embedding `ιN` and the `Decomposition.map` transport core
    (injectivity preserves the excess set, `map_excessIndices_card_of_injective`).
    Because `Module.finrank ℝ (lp (fun _ : ℕ => ℝ) 2) = 0`, no `card ≤ finrank`
    bound can hold here — the finite-dimensionality hypothesis of `shapley_folkman`
    is essential and cannot be replaced by any fixed finite bound. -/
theorem shapley_folkman_excess_unbounded_in_lp :
    ∀ K : ℕ, ∃ (N : ℕ)
      (D : ShapleyFolkman.Decomposition
             (fun i : Fin N =>
               (ιN N) '' ({0, EuclideanSpace.single i 1} :
                   Set (EuclideanSpace ℝ (Fin N))))
             (Finset.univ : Finset (Fin N))
             ((ιN N) ((1 / 2 : ℝ) •
                 ∑ i : Fin N, EuclideanSpace.single i (1 : ℝ) :
                   EuclideanSpace ℝ (Fin N)))),
      D.excessIndices.card > K := by
  intro K
  refine ⟨K + 1, (midpointDecomp (K + 1)).map (ιN (K + 1)), ?_⟩
  rw [ShapleyFolkman.Decomposition.map_excessIndices_card_of_injective
        (midpointDecomp (K + 1)) (ιN_injective (K + 1)),
      tight_excess_count (K + 1) (midpointDecomp (K + 1))]
  exact Nat.lt_succ_self K

end ShapleyFolkmanOQ01
