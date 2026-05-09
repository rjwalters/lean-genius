/-
# Kakutani from Brouwer via Approximate Selections

This file outlines the proof of Kakutani's fixed point theorem from
Brouwer's fixed point theorem using approximate continuous selections.

**Proof Strategy**:
1. For each n, construct a continuous 1/n-approximate selection f_n of F
2. Apply Brouwer's FPT: ∃ x_n with f_n(x_n) = x_n
3. By compactness of S: extract convergent subsequence x_{n_k} → x*
4. Use upper hemicontinuity to show x* ∈ F(x*)

**Status**: AXIOMATIZED (2 axioms)
- Axiom 1: Brouwer's FPT in Euclidean space
- Axiom 2: Cellina–Browder graph-approximate selections exist for UHC
  maps with convex values
- Proved: Sequential compactness (from Mathlib's IsCompact.isSeqCompact)
- Proved: The combination argument (Kakutani from the two axioms via the helper)
- Proved: The limit-argument helper (approx_fixedpoint_implies_fixedpoint)

**Why graph-approximate selections (vs pointwise / simplicial approximation)?**
The simplicial approach avoids approximate selections altogether but
requires triangulation infrastructure not currently in Mathlib. The
selection approach requires only `Mathlib.Topology.PartitionOfUnity`,
but a subtle point (made precise in S6) is that under USC + convex
values one obtains only the *graph* approximate selection (Cellina 1969,
Browder 1968), NOT the pointwise selection: the strictly stronger
pointwise form is mathematically false in general. This file therefore
states the axiom in graph form and threads a triangle-inequality step
through `kakutani_from_brouwer` to recover the diagonal-distance
witness expected by `approx_fixedpoint_implies_fixedpoint`.

**References**:
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem.
  Duke Math. J. 8, 457-459.
- Cellina, A. (1969). Approximation of set valued functions and fixed
  point theorems. Ann. Mat. Pura Appl. 82, 17-24.

Parent: SchauderFixedPointOQ03.lean (Kakutani framework)
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Set Filter Topology Metric

namespace KakutaniFromBrouwer

-- ============================================================
-- Part I: Definitions (imported from parent)
-- ============================================================

/-- A set-valued map (correspondence). -/
def SetValuedMap (X Y : Type*) := X → Set Y

/-- Fixed point of a set-valued map: x ∈ F(x). -/
def IsFixedPoint {X : Type*} (F : SetValuedMap X X) (x : X) : Prop :=
  x ∈ F x

/-- Upper hemicontinuity: {x | F(x) ⊆ V} is open for every open V. -/
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}

-- ============================================================
-- Part II: Key Axioms
-- ============================================================

/-- **Axiom 1: Brouwer's Fixed Point Theorem on the Closed Unit Ball**

    Every continuous self-map of the closed unit ball in
    `EuclideanSpace ℝ (Fin n)` has a fixed point.

    **S11.A strict-weakening (2026-05-09):** This axiom replaces the
    previous `axiom brouwer_fpt` (which asserted the FPT for *any*
    nonempty compact convex `S`). Following S10's reconnaissance
    (Brouwer FPT is absent from Mathlib4 — neither unit-ball nor
    general-compact-convex form is present at the pinned rev or on
    master; see `s10-mathlib-v426-lookup3-resolved.md`), this
    iteration adopts S10's recommended **Option A**:

    * Strict-weakening on the Brouwer side: assume only the unit-ball
      form (a smaller mathematical commitment, identical axiom
      *count*).
    * The general-compact-convex form is recovered in-house as
      `theorem brouwer_fpt` via the nearest-point retraction reduction
      (S8 design + S11.B helper), pulling the obstruction to a single
      Mathlib API surface (`exists_norm_eq_iInf_of_complete_convex` plus
      its variational-inequality continuity refinement).

    **Mathlib status (S10):** Absent. `docs/100.yaml` entry for
    "Brouwer Fixed Point Theorem" points to an external Lean 3
    implementation; `docs/1000.yaml` flags it as `comment: "in Lean 3"`.
    No Lean file in `Mathlib/Topology/...` or `Mathlib/Analysis/...` at
    the pinned rev contains the topological Brouwer FPT (the three
    `Brouwer` hits across all `.lean` files are in
    `Mathlib/Order/Heyting/...` — Heyting-algebra Brouwer, not the FPT). -/
axiom brouwer_unit_ball {n : ℕ}
    (f : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
       → ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) :
    ∃ x, f x = x

/-- **LOOKUP-2 helper (S11.B work item, currently `sorry`-stubbed):**
    Nearest-point retraction onto a nonempty compact convex set in
    `EuclideanSpace ℝ (Fin n)`, packaged as a continuous map that is the
    identity on the set.

    **Proof (S14, researcher-9, 2026-05-09):** existence of the nearest
    point comes from `exists_norm_eq_iInf_of_complete_convex`
    (`Mathlib.Analysis.InnerProductSpace.Projection.Minimal`) using
    `IsCompact.isComplete` to discharge completeness; continuity (in
    fact 1-Lipschitz) is the standard variational-inequality + Cauchy-
    Schwarz argument via `norm_eq_iInf_iff_real_inner_le_zero` and
    `abs_real_inner_le_norm`; idempotency on `↥S` follows from the
    same variational inequality applied at `u = x ∈ S` with witness
    `w = x` (the uniqueness clause is implicit in this case). -/
lemma exists_continuous_proj_convex {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
      Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x := by
  -- S11.B (researcher-9, S14, 2026-05-09): nearest-point retraction
  -- onto a compact convex S in EuclideanSpace ℝ (Fin n).
  -- Compact ⇒ complete (in any metric space), so we can invoke
  -- `exists_norm_eq_iInf_of_complete_convex`.
  have hS_complete : IsComplete S := hS_compact.isComplete
  -- np : E → E picks a nearest point in S for every u.
  set np : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u =>
    (exists_norm_eq_iInf_of_complete_convex hS_ne hS_complete hS_convex u).choose
    with hnp_def
  have np_mem : ∀ u : EuclideanSpace ℝ (Fin n), np u ∈ S := fun u =>
    (exists_norm_eq_iInf_of_complete_convex hS_ne hS_complete hS_convex u).choose_spec.1
  have np_min : ∀ u : EuclideanSpace ℝ (Fin n),
      ‖u - np u‖ = ⨅ w : ↥S, ‖u - (w : EuclideanSpace ℝ (Fin n))‖ := fun u =>
    (exists_norm_eq_iInf_of_complete_convex hS_ne hS_complete hS_convex u).choose_spec.2
  -- Variational inequality (vi): for every w ∈ S, ⟨u - np u, w - np u⟩_ℝ ≤ 0.
  have np_vi : ∀ u : EuclideanSpace ℝ (Fin n), ∀ w ∈ S,
      ⟪u - np u, w - np u⟫_ℝ ≤ 0 := by
    intro u w hw
    exact (norm_eq_iInf_iff_real_inner_le_zero hS_convex (np_mem u)).mp (np_min u) w hw
  -- Idempotency: np x = x for x ∈ S. Apply vi at u = x, w = x ∈ S.
  have np_id : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ S → np x = x := by
    intro x hx
    have h1 : ⟪x - np x, x - np x⟫_ℝ ≤ 0 := np_vi x x hx
    have h2 : ⟪x - np x, x - np x⟫_ℝ = ‖x - np x‖ * ‖x - np x‖ :=
      real_inner_self_eq_norm_mul_norm _
    have h3 : ‖x - np x‖ * ‖x - np x‖ ≤ 0 := h2 ▸ h1
    have h4 : ‖x - np x‖ * ‖x - np x‖ = 0 :=
      le_antisymm h3 (mul_self_nonneg _)
    have h5 : ‖x - np x‖ = 0 := by
      rcases mul_self_eq_zero.mp h4 with h
      exact h
    have h6 : x - np x = 0 := norm_eq_zero.mp h5
    exact (sub_eq_zero.mp h6).symm
  -- 1-Lipschitz: ‖np x - np y‖ ≤ ‖x - y‖.
  -- Standard variational + Cauchy-Schwarz argument.
  -- VI at x with w = np y ∈ S: ⟨x - np x, np y - np x⟩ ≤ 0
  -- VI at y with w = np x ∈ S: ⟨y - np y, np x - np y⟩ ≤ 0
  -- Sum the two (with sign flip on the second) to get
  --   ⟨x - y, np y - np x⟩ + ‖np y - np x‖² ≤ 0
  -- so ‖np y - np x‖² ≤ -⟨x - y, np y - np x⟩ ≤ ‖x - y‖ · ‖np y - np x‖.
  have np_lip : ∀ x y : EuclideanSpace ℝ (Fin n),
      ‖np x - np y‖ ≤ ‖x - y‖ := by
    intro x y
    set p : EuclideanSpace ℝ (Fin n) := np x with hp_def
    set q : EuclideanSpace ℝ (Fin n) := np y with hq_def
    have h1 : ⟪x - p, q - p⟫_ℝ ≤ 0 := np_vi x q (np_mem y)
    have h2 : ⟪y - q, p - q⟫_ℝ ≤ 0 := np_vi y p (np_mem x)
    -- Convert h2 to ⟨q - y, q - p⟩ ≤ 0 via two sign flips:
    --   ⟨y - q, p - q⟩ = ⟨y - q, -(q - p)⟩ = -⟨y - q, q - p⟩
    --   so ⟨y - q, q - p⟩ ≥ 0, and ⟨q - y, q - p⟩ = -⟨y - q, q - p⟩ ≤ 0.
    have hpq_neg : p - q = -(q - p) := by ring
    have h2' : ⟪y - q, q - p⟫_ℝ ≥ 0 := by
      have hflip : ⟪y - q, p - q⟫_ℝ = -⟪y - q, q - p⟫_ℝ := by
        rw [hpq_neg, inner_neg_right]
      linarith [hflip ▸ h2]
    have h3 : ⟪q - y, q - p⟫_ℝ ≤ 0 := by
      have : ⟪q - y, q - p⟫_ℝ = -⟪y - q, q - p⟫_ℝ := by
        rw [show q - y = -(y - q) from by ring, inner_neg_left]
      linarith [this ▸ h2']
    -- Sum h1 and h3: ⟨(x - p) + (q - y), q - p⟩ ≤ 0.
    have hsum_inner : ⟪(x - p) + (q - y), q - p⟫_ℝ ≤ 0 := by
      rw [inner_add_left]; linarith
    -- (x - p) + (q - y) = (x - y) + (q - p), so:
    --   ⟨(x - y) + (q - p), q - p⟩ = ⟨x - y, q - p⟩ + ⟨q - p, q - p⟩ ≤ 0
    have heq : (x - p) + (q - y) = (x - y) + (q - p) := by ring
    rw [heq, inner_add_left] at hsum_inner
    -- ⟨q - p, q - p⟩ = ‖q - p‖²
    have hself : ⟪q - p, q - p⟫_ℝ = ‖q - p‖ * ‖q - p‖ :=
      real_inner_self_eq_norm_mul_norm _
    -- ‖q - p‖² ≤ -⟨x - y, q - p⟩
    have h_sq_bound : ‖q - p‖ * ‖q - p‖ ≤ -⟪x - y, q - p⟫_ℝ := by
      linarith [hsum_inner, hself]
    -- Cauchy-Schwarz: -⟨x - y, q - p⟩ ≤ |⟨x - y, q - p⟩| ≤ ‖x - y‖ · ‖q - p‖.
    have h_cs : -⟪x - y, q - p⟫_ℝ ≤ ‖x - y‖ * ‖q - p‖ :=
      le_trans (neg_le_abs _) (abs_real_inner_le_norm _ _)
    have h_chain : ‖q - p‖ * ‖q - p‖ ≤ ‖x - y‖ * ‖q - p‖ :=
      le_trans h_sq_bound h_cs
    -- ‖p - q‖ = ‖q - p‖ via norm_neg + ring.
    have h_norm_eq : ‖p - q‖ = ‖q - p‖ := by
      rw [show p - q = -(q - p) from by ring, norm_neg]
    rw [h_norm_eq]
    -- Goal: ‖q - p‖ ≤ ‖x - y‖. Case-split on ‖q - p‖ = 0 vs > 0.
    rcases eq_or_lt_of_le (norm_nonneg (q - p)) with hzero | hpos
    · -- 0 = ‖q - p‖
      rw [← hzero]; exact norm_nonneg _
    · -- 0 < ‖q - p‖: divide h_chain by ‖q - p‖.
      exact le_of_mul_le_mul_right h_chain hpos
  -- Continuity from 1-Lipschitz, via metric ε-δ.
  have np_cont : Continuous np := by
    rw [Metric.continuous_iff]
    intro u ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    rw [dist_eq_norm] at hy ⊢
    exact lt_of_le_of_lt (np_lip y u) hy
  -- Package as ↥S-valued retraction.
  refine ⟨fun u => ⟨np u, np_mem u⟩, ?_, ?_⟩
  · -- Continuity of the ↥S-valued projection.
    exact np_cont.subtype_mk np_mem
  · -- Idempotency: r x = x for x : ↥S.
    intro x
    apply Subtype.ext
    exact np_id (x : EuclideanSpace ℝ (Fin n)) x.property

/-- **Theorem 1 (was Axiom 1): Brouwer's FPT on a compact convex subset.**

    Derived from `axiom brouwer_unit_ball` via the nearest-point
    retraction reduction. Net axiom dependence on the Brouwer side is
    strictly weakened from "general compact convex `S`" to "closed unit
    ball only" (S11.A, 2026-05-09; see
    `s10-mathlib-v426-lookup3-resolved.md` Option A).

    **S11.A.body landed (S13, researcher-10, 2026-05-09; see
    `s11-strict-weakening-spec.md` and `s12-s11a-body-step6-refinement.md`).**
    **S11.B landed (S14, researcher-9, 2026-05-09):** the
    `exists_continuous_proj_convex` helper is now proven from
    `exists_norm_eq_iInf_of_complete_convex` plus the variational-
    inequality + Cauchy-Schwarz argument. As a result this theorem is
    end-to-end sorry-free, and the only assumption on the Brouwer side
    is the closed-unit-ball axiom `brouwer_unit_ball`.

    **Proof structure:**

    1. Since `S` is compact, it is bounded
       (`IsCompact.isBounded`); pick `R > 0` with
       `S ⊆ Metric.closedBall 0 R` via `Bornology.IsBounded.subset_closedBall_lt`.
    2. Build the nearest-point retraction `r : E → ↥S` from
       `exists_continuous_proj_convex` (LOOKUP-2 helper, S11.B; proved
       in S14, 2026-05-09).
    3. Compose `F : ↥(closedBall 0 R) → ↥(closedBall 0 R)` via
       `b ↦ ⟨f (r b), …⟩`, well-defined since `f (r b) ∈ ↥S ⊆ closedBall 0 R`;
       continuity from `continuous_subtype_val`/`Continuous.subtype_mk`.
    4. Rescale closed balls *elementwise* (Option b: no `Homeomorph` needed):
       `σ x := R • x` carries `closedBall 0 1` to `closedBall 0 R`, with
       inverse `τ b := R⁻¹ • b`; both are continuous via
       `continuous_const_smul`. Apply `brouwer_unit_ball` to
       `G := τ ∘ F ∘ σ` to get `y` with `G y = y`. Multiplying by `R`
       and using `mul_inv_cancel₀ + one_smul` yields the coordinate
       identity `(F (σ y) : E) = (σ y : E)`.
    5. (S12 refinement.) Lift `σ y` from `↥(closedBall 0 R)` to `↥S` by
       observing `(σ y : E) = (F (σ y) : E) = (f (r (σ y : E)) : E) ∈ S`,
       then invoking the helper's idempotency clause to identify
       `r (σ y : E) = ⟨(σ y : E), …⟩` in `↥S`. The `↥S` candidate
       fixed point is `r (σ y : E)`; the equation `f (r (σ y : E)) =
       r (σ y : E)` follows from the coord chain
       `(F (σ y) : E) = (σ y : E) = (r (σ y : E) : E)` and `Subtype.ext`. -/
theorem brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- S11.A.body (researcher-10, S13, 2026-05-09): retraction reduction body
  -- per s11-strict-weakening-spec.md + s12-s11a-body-step6-refinement.md.
  -- Step 1: bound S by closedBall 0 R for some R > 0 (LOOKUP-1, S9-confirmed).
  have hS_bounded : Bornology.IsBounded S := hS_compact.isBounded
  obtain ⟨R, hR_pos, hSR⟩ :=
    hS_bounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hRinv_pos : 0 < R⁻¹ := inv_pos.mpr hR_pos
  -- Step 2: continuous nearest-point retraction r : E → ↥S (LOOKUP-2 helper, S11.B).
  obtain ⟨r, hr_cont, hr_id⟩ :=
    exists_continuous_proj_convex S hS_ne hS_compact hS_convex
  -- Step 3: F : ↥(closedBall 0 R) → ↥(closedBall 0 R), b ↦ ⟨f (r b), _⟩.
  have hF_coord_cont :
      Continuous fun b : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) =>
        (f (r ((b : EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n)) :=
    continuous_subtype_val.comp
      (hf.comp (hr_cont.comp continuous_subtype_val))
  have hF_in_B : ∀ b : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R),
      (f (r ((b : EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n))
        ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
    fun b => hSR (f (r ((b : EuclideanSpace ℝ (Fin n))))).property
  let F : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    fun b => ⟨(f (r ((b : EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n)),
              hF_in_B b⟩
  have hF_cont : Continuous F := hF_coord_cont.subtype_mk hF_in_B
  -- Step 4: rescale closedBall 0 R ↔ closedBall 0 1 elementwise (Option b).
  -- σ : ↥(closedBall 0 1) → ↥(closedBall 0 R), x ↦ R • x.
  have hσ_in_B : ∀ x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      R • ((x : EuclideanSpace ℝ (Fin n)))
        ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x
    rw [Metric.mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg hR_pos.le]
    have hx_le : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
      have hx := x.property
      rwa [Metric.mem_closedBall_zero_iff] at hx
    calc R * ‖(x : EuclideanSpace ℝ (Fin n))‖
        ≤ R * 1 := mul_le_mul_of_nonneg_left hx_le hR_pos.le
      _ = R := by ring
  let σ : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    fun x => ⟨R • (x : EuclideanSpace ℝ (Fin n)), hσ_in_B x⟩
  have hσ_cont : Continuous σ :=
    ((continuous_const_smul R).comp continuous_subtype_val).subtype_mk hσ_in_B
  -- τ : ↥(closedBall 0 R) → ↥(closedBall 0 1), b ↦ R⁻¹ • b.
  have hτ_in_U : ∀ b : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R),
      R⁻¹ • ((b : EuclideanSpace ℝ (Fin n)))
        ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro b
    rw [Metric.mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg hRinv_pos.le]
    have hb_le : ‖(b : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
      have hb := b.property
      rwa [Metric.mem_closedBall_zero_iff] at hb
    calc R⁻¹ * ‖(b : EuclideanSpace ℝ (Fin n))‖
        ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hb_le hRinv_pos.le
      _ = 1 := inv_mul_cancel₀ hR_ne
  let τ : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    fun b => ⟨R⁻¹ • (b : EuclideanSpace ℝ (Fin n)), hτ_in_U b⟩
  have hτ_cont : Continuous τ :=
    ((continuous_const_smul R⁻¹).comp continuous_subtype_val).subtype_mk hτ_in_U
  -- G := τ ∘ F ∘ σ : ↥(closedBall 0 1) → ↥(closedBall 0 1).
  let G : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := τ ∘ F ∘ σ
  have hG_cont : Continuous G := hτ_cont.comp (hF_cont.comp hσ_cont)
  -- Apply the unit-ball axiom.
  obtain ⟨y, hy⟩ := brouwer_unit_ball G hG_cont
  -- Step 5: extract (F (σ y) : E) = (σ y : E) from G y = y.
  -- hy : G y = y, so (G y : E) = (y : E), and (G y : E) = R⁻¹ • (F (σ y) : E).
  have hτFσy_coord :
      R⁻¹ • ((F (σ y) :
          ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) =
      ((y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
          EuclideanSpace ℝ (Fin n)) :=
    congrArg Subtype.val hy
  -- Multiply by R: (F (σ y) : E) = R • (y : E) = (σ y : E).
  have hFσy_eq_σy :
      ((F (σ y) :
          ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) =
      ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) := by
    have step1 : R • R⁻¹ •
        ((F (σ y) :
            ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
              EuclideanSpace ℝ (Fin n)) =
        R • ((y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
              EuclideanSpace ℝ (Fin n)) := by
      rw [hτFσy_coord]
    rw [smul_smul, mul_inv_cancel₀ hR_ne, one_smul] at step1
    -- step1 : (F (σ y) : E) = R • (y : E); (σ y : E) = R • (y : E) by `let σ`.
    exact step1
  -- Step 6: lift `σ y` from ↥B to ↥S, then derive the ↥S fixed point.
  -- (σ y : E) ∈ S because (σ y : E) = (F (σ y) : E) = (f (r (σ y : E)) : E),
  -- and f's codomain is ↥S.
  have hσy_in_S :
      ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) ∈ S := by
    rw [← hFσy_eq_σy]
    show (f (r (((σ y :
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n)) ∈ S
    exact (f (r (((σ y :
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n))))).property
  -- Lift σ y to ↥S and use idempotency r ((x : E)) = x for x : ↥S.
  let x' : ↥S :=
    ⟨((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
          EuclideanSpace ℝ (Fin n)), hσy_in_S⟩
  have hx'_coord : ((x' : ↥S) : EuclideanSpace ℝ (Fin n)) =
      ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
          EuclideanSpace ℝ (Fin n)) := rfl
  have hr_x' : r ((x' : EuclideanSpace ℝ (Fin n))) = x' := hr_id x'
  have hr_σy : r (((σ y :
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
        EuclideanSpace ℝ (Fin n))) = x' := by
    rw [← hx'_coord]; exact hr_x'
  -- Candidate fixed point: r (σ y : E) ∈ ↥S.
  refine ⟨r (((σ y :
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
        EuclideanSpace ℝ (Fin n))), ?_⟩
  -- Reduce to coord equality, then chain through hFσy_eq_σy + hr_σy + hx'_coord.
  apply Subtype.ext
  -- Goal: (f (r (σ y : E)) : E) = (r (σ y : E) : E)
  -- LHS = (F (σ y) : E) by `let F`-unfolding; = (σ y : E) by hFσy_eq_σy.
  -- RHS = (x' : E) via hr_σy; = (σ y : E) by hx'_coord.
  calc (f (r (((σ y :
              ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
                EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n))
      = ((F (σ y) : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
              EuclideanSpace ℝ (Fin n)) := rfl
    _ = ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
              EuclideanSpace ℝ (Fin n)) := hFσy_eq_σy
    _ = ((x' : ↥S) : EuclideanSpace ℝ (Fin n)) := hx'_coord.symm
    _ = (r (((σ y :
              ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
                EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n)) := by
              rw [hr_σy]

/-- A continuous `f : S → S` is an ε-graph-approximate selection of `F`
    if for every `x` there is a nearby point `x'` (within `ε`) and a point
    `y ∈ F(x')` with `dist (f x) y < ε` — i.e. the graph of `f` lies inside
    the `ε`-fattening of the graph of `F`.

    This is the Cellina–Browder form of approximate selection: it is the
    strongest form provable for upper-hemicontinuous maps with nonempty
    convex values (S6 analysis: the strictly stronger pointwise form
    `∀ x, ∃ y ∈ F x, dist (f x) y < ε` is FALSE under USC + convex values
    alone — a 1-D counterexample with `F(0) = [0,1]`, `F(t>0) = {0}`,
    `F(t<0) = {1}` admits no continuous pointwise (1/3)-selection by
    continuity at `0`). -/
def IsGraphApproxSelection {X : Type*} [PseudoMetricSpace X]
    (F : SetValuedMap X X) (f : X → X) (ε : ℝ) : Prop :=
  ∀ x, ∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε

/-- **Axiom 2: Cellina–Browder Graph-Approximate Continuous Selections**

    For a compact convex `S`, an UHC map `F : S → 2^S` with nonempty
    convex values, and any `ε > 0`, there exists a continuous
    `f : S → S` whose graph lies in the `ε`-fattening of `graph(F)`.

    **Why the graph form (not the pointwise form):** S6 mathematical
    analysis (`s6-axiom-counterexample.md`) shows the pointwise form
    `IsApproxSelection F f ε` is FALSE under USC + convex values alone.
    The graph form is the standard Cellina–Browder selection theorem
    (Cellina 1969; Browder 1968; Aubin–Frankowska, *Set-Valued Analysis*
    §9.2) and suffices to derive Kakutani's theorem (see
    `kakutani_from_brouwer` below; the helper passes a `2ε`-bound
    through `approx_fixedpoint_implies_fixedpoint`).

    **Proof sketch (PartitionOfUnity construction):**
    1. For each `x ∈ S`, pick `y_x ∈ F(x)` and use UHC to choose an open
       `U_x ∋ x` with `F(U_x) ⊆ ε`-thickening of `F(x)`.
    2. Compactness extracts a finite subcover `U_{x_1}, …, U_{x_k}`.
    3. Subordinate partition of unity `{φ_i}` with `supp φ_i ⊆ U_{x_i}`.
    4. Define `f(x) := Σ φ_i(x) · y_{x_i}`. Convexity of `S` gives `f x ∈ S`.
    5. Graph bound: at any `x`, pick `i` with `φ_i(x) > 0`; then
       `x ∈ U_{x_i}` and `(x_i, y_{x_i})` lies in the graph of `F`,
       certifying graph-distance `< ε`. (The pointwise form would require
       step 5 to bound `dist(f(x), F(x))` directly, which fails — see S6.)

    Formalizing this in Lean requires `Mathlib.Topology.PartitionOfUnity`
    plus the Cellina averaging argument; it is a standard but non-trivial
    Mathlib-level task and is not yet in scope here. -/
axiom approx_selection_exists {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => (f x : ↥S)) ε

/-- **Sequential Compactness in Metric Spaces**

    In a compact metric space, every sequence has a convergent subsequence.
    Proved from Mathlib's `IsCompact.isSeqCompact` (PseudoMetricSpace is
    first-countable). Was previously stated as an axiom; now derived. -/
theorem seq_compact_of_compact {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S) (x : ℕ → X) (hx : ∀ n, x n ∈ S) :
    ∃ (a : X) (φ : ℕ → ℕ), a ∈ S ∧ StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ_mono, hφ_tend⟩ := hS.isSeqCompact hx
  exact ⟨a, φ, ha, hφ_mono, hφ_tend⟩

-- ============================================================
-- Part III: Limit Argument (Helper Lemma)
-- ============================================================

/-- A continuous function with ε-approximate fixed point property
    for all ε > 0 has a true fixed point (when the target is closed).

    This captures the limit argument: if we can get "almost" fixed points
    for any precision, compactness gives a real one.

    **Proof outline**:
    1. Build sequences `xₙ ∈ S`, `yₙ ∈ F(xₙ)` with `dist(xₙ, yₙ) < 1/(n+1)`
       via choice on `happrox`.
    2. Compactness of `S` yields a subsequence `x_{φ(n)} → x*` with `x* ∈ S`.
    3. Since `dist(x_{φ(n)}, y_{φ(n)}) → 0`, the subsequence
       `y_{φ(n)} → x*` as well (triangle inequality).
    4. Suppose `x* ∉ F(x*)`. Case split on `(F x*).Nonempty`:
       - **Empty case**: take `V := ∅` (open superset of empty F(x*));
         UHC gives an open `U ∋ x*` with `F(U) ⊆ ∅`, hence eventually
         `F(x_{φ(n)}) = ∅`, contradicting `y_{φ(n)} ∈ F(x_{φ(n)})`.
       - **Nonempty case**: `δ := infDist x* (F x*) > 0` since `F(x*)` is
         closed and `x* ∉ F(x*)`. Take `V := Metric.thickening (δ/2) (F x*)`,
         an open superset of `F(x*)`. UHC gives an open `U ∋ x*` with
         `F(U) ⊆ V`. Eventually `x_{φ(n)} ∈ U`, hence `y_{φ(n)} ∈ V`, so
         `infDist y_{φ(n)} (F x*) < δ/2`. Triangle inequality:
         `infDist x* (F x*) ≤ dist x* y_{φ(n)} + infDist y_{φ(n)} (F x*) < δ`
         for `n` large, contradicting `δ = infDist x* (F x*)`. -/
theorem approx_fixedpoint_implies_fixedpoint
    {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S)
    (F : SetValuedMap X X) (hF_closed : ∀ x ∈ S, IsClosed (F x))
    (hF_uhc : IsUpperHemicontinuous F)
    (happrox : ∀ ε > 0, ∃ x ∈ S, ∃ y ∈ F x, dist x y < ε) :
    ∃ x ∈ S, IsFixedPoint F x := by
  -- Step 1: build sequences via choice
  choose xseq hxseq_S yseq hyseq_F hxy_dist using
    fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (by positivity)
  -- Step 2: extract convergent subsequence
  obtain ⟨x_star, φ, hx_star_S, hφ_mono, hφ_tend⟩ :=
    seq_compact_of_compact S hS xseq hxseq_S
  refine ⟨x_star, hx_star_S, ?_⟩
  -- Step 3: yseq ∘ φ → x_star
  have h_one_div_to_zero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h_xy_to_zero :
      Tendsto (fun n => dist (xseq n) (yseq n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg)
      (fun n => le_of_lt (hxy_dist n)) h_one_div_to_zero
  have h_xy_phi_to_zero :
      Tendsto (fun n => dist (xseq (φ n)) (yseq (φ n))) atTop (𝓝 0) :=
    h_xy_to_zero.comp hφ_mono.tendsto_atTop
  have h_x_phi_dist_to_zero :
      Tendsto (fun n => dist (xseq (φ n)) x_star) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hφ_tend
  have hyφ_tend : Tendsto (fun n => yseq (φ n)) atTop (𝓝 x_star) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h_yx_phi : Tendsto (fun n => dist (yseq (φ n)) (xseq (φ n)))
        atTop (𝓝 0) := by
      simpa [dist_comm] using h_xy_phi_to_zero
    have h_sum :
        Tendsto (fun n => dist (yseq (φ n)) (xseq (φ n)) +
            dist (xseq (φ n)) x_star) atTop (𝓝 0) := by
      simpa using h_yx_phi.add h_x_phi_dist_to_zero
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle (yseq (φ n)) (xseq (φ n)) x_star) h_sum
  -- Step 4: derive contradiction from x_star ∉ F x_star
  by_contra hne
  have hF_closed_xstar : IsClosed (F x_star) := hF_closed _ hx_star_S
  by_cases hF_xstar_ne : (F x_star).Nonempty
  · -- Nonempty case: thickening contradiction
    set δ : ℝ := Metric.infDist x_star (F x_star) with hδ_def
    have hδ_pos : 0 < δ := by
      have h_not_mem_closure : x_star ∉ closure (F x_star) := by
        rwa [hF_closed_xstar.closure_eq]
      have h_ne_zero : Metric.infDist x_star (F x_star) ≠ 0 := by
        intro h
        exact h_not_mem_closure
          ((Metric.mem_closure_iff_infDist_zero hF_xstar_ne).mpr h)
      exact lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h_ne_zero)
    have hδ_half_pos : 0 < δ / 2 := by linarith
    -- Define V as the union of (δ/2)-balls around F x_star (open neighborhood of F x_star)
    let V : Set X := ⋃ y ∈ F x_star, Metric.ball y (δ / 2)
    have hV_open : IsOpen V := isOpen_biUnion (fun _ _ => Metric.isOpen_ball)
    have hF_in_V : F x_star ⊆ V := by
      intro y hy
      exact Set.mem_biUnion hy (Metric.mem_ball_self hδ_half_pos)
    let U : Set X := {z | F z ⊆ V}
    have hU_open : IsOpen U := hF_uhc V hV_open
    have hxstar_U : x_star ∈ U := hF_in_V
    -- Eventually xseq (φ n) ∈ U
    have h_eventually_U : ∀ᶠ n in atTop, xseq (φ n) ∈ U :=
      hφ_tend.eventually (hU_open.mem_nhds hxstar_U)
    -- Eventually dist x_star (yseq (φ n)) < δ/2
    have h_dist_yφ : Tendsto (fun n => dist x_star (yseq (φ n)))
        atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hyφ_tend
      simpa [dist_comm] using h
    have h_eventually_dist :
        ∀ᶠ n in atTop, dist x_star (yseq (φ n)) < δ / 2 :=
      h_dist_yφ.eventually (Iio_mem_nhds hδ_half_pos)
    -- Combine to get the contradiction
    obtain ⟨n, hn_U, hn_dist⟩ :=
      (h_eventually_U.and h_eventually_dist).exists
    -- yseq (φ n) ∈ V, so ∃ z ∈ F x_star, dist (yseq (φ n)) z < δ/2
    have h_yseq_in_V : yseq (φ n) ∈ V := hn_U (hyseq_F (φ n))
    obtain ⟨z, hz_F, hz_ball⟩ := Set.mem_iUnion₂.mp h_yseq_in_V
    rw [Metric.mem_ball] at hz_ball
    -- δ = infDist x_star (F x_star) ≤ dist x_star z (since z ∈ F x_star)
    have h_delta_le_dist : δ ≤ dist x_star z := by
      have hi := Metric.infDist_le_dist_of_mem (x := x_star) hz_F
      linarith [hδ_def]
    -- triangle inequality on dist x_star z
    have h_tri : dist x_star z ≤ dist x_star (yseq (φ n)) + dist (yseq (φ n)) z :=
      dist_triangle _ _ _
    have hcontra : δ < δ := by
      calc δ ≤ dist x_star z := h_delta_le_dist
        _ ≤ dist x_star (yseq (φ n)) + dist (yseq (φ n)) z := h_tri
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    exact lt_irrefl _ hcontra
  · -- Empty case
    rw [Set.not_nonempty_iff_eq_empty] at hF_xstar_ne
    let U : Set X := {z | F z ⊆ (∅ : Set X)}
    have hU_open : IsOpen U := hF_uhc ∅ isOpen_empty
    have hxstar_U : x_star ∈ U := by
      show F x_star ⊆ ∅
      rw [hF_xstar_ne]
    have h_eventually_U : ∀ᶠ n in atTop, xseq (φ n) ∈ U :=
      hφ_tend.eventually (hU_open.mem_nhds hxstar_U)
    obtain ⟨n, hn⟩ := h_eventually_U.exists
    -- F (xseq (φ n)) ⊆ ∅, but yseq (φ n) ∈ F (xseq (φ n))
    exact (hn (hyseq_F (φ n))).elim

-- ============================================================
-- Part IV: The Proof of Kakutani from Brouwer
-- ============================================================

/-- **Kakutani's FPT from Brouwer + Cellina–Browder Graph Selections**

    Proof sketch (filled body below):
    1. For each `ε > 0`, call `approx_selection_exists` with `ε/2` to get
       a continuous `(ε/2)`-graph-approximate selection `f` of `F`.
    2. Apply `brouwer_fpt` to `f` on `S` to get `x₀` with `f(x₀) = x₀`.
    3. The graph-form property at `x₀` gives `(x', y)` with
       `dist(x₀, x') < ε/2`, `y ∈ F(x')`, `dist(f(x₀), y) < ε/2`.
       Since `f(x₀) = x₀`, the triangle inequality
       `dist(x', y) ≤ dist(x', x₀) + dist(x₀, f x₀) + dist(f x₀, y)
                    < ε/2 + 0 + ε/2 = ε`
       provides the diagonal-distance witness.
    4. Hand the family of `ε`-witnesses to
       `approx_fixedpoint_implies_fixedpoint`, which uses sequential
       compactness + closedness + UHC of `F` to extract a genuine fixed
       point. -/
theorem kakutani_from_brouwer {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F) :
    ∃ x : ↥S, IsFixedPoint F x := by
  -- The subtype ↥S inherits a PseudoMetricSpace from EuclideanSpace.
  -- Compactness of ↥S follows from compactness of S in the ambient space.
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hUniv : IsCompact (Set.univ : Set ↥S) := isCompact_univ
  have hF_closed' : ∀ x ∈ (Set.univ : Set ↥S), IsClosed (F x) :=
    fun x _ => hF_closed x
  have happrox_total :
      ∀ ε > 0, ∃ x ∈ (Set.univ : Set ↥S), ∃ y ∈ F x, dist x y < ε := by
    intro ε hε
    -- Call the graph-selection axiom with ε/2; the triangle-inequality step
    -- below converts the (ε/2, ε/2) graph witness into an ε-diagonal witness.
    have hε_half : 0 < ε / 2 := by linarith
    obtain ⟨f, hf_cont, hf_approx⟩ :=
      approx_selection_exists S hS_ne hS_compact hS_convex F
        hF_ne hF_convex hF_uhc (ε / 2) hε_half
    obtain ⟨x0, hx0⟩ := brouwer_fpt S hS_ne hS_compact hS_convex f hf_cont
    -- Graph-form witness at `x = x0`:
    --   dist x0 x' < ε/2,  y ∈ F x',  dist (f x0) y < ε/2.
    obtain ⟨x', y, hxx', hy_F, hy_dist⟩ := hf_approx x0
    -- Beta-reduce the `(fun x => (f x : ↥S)) x0` form sitting inside `hy_dist`.
    have hy_dist' : dist (f x0) y < ε / 2 := hy_dist
    refine ⟨x', Set.mem_univ _, y, hy_F, ?_⟩
    -- Triangle: dist x' y ≤ dist x' x0 + dist x0 (f x0) + dist (f x0) y.
    -- f x0 = x0 forces dist x0 (f x0) = 0, so the bound is < ε/2 + ε/2 = ε.
    have hxx0 : dist x' x0 < ε / 2 := by
      rw [dist_comm]; exact hxx'
    have h_tri1 : dist x' y ≤ dist x' x0 + dist x0 y := dist_triangle _ _ _
    have h_tri2 : dist x0 y ≤ dist x0 (f x0) + dist (f x0) y := dist_triangle _ _ _
    have h_zero : dist x0 (f x0) = 0 := by rw [hx0]; exact dist_self _
    linarith
  obtain ⟨x_star, _, hfp⟩ :=
    approx_fixedpoint_implies_fixedpoint (Set.univ : Set ↥S) hUniv F
      hF_closed' hF_uhc happrox_total
  exact ⟨x_star, hfp⟩

/-
## Part V: Why This Matters

The proof of Kakutani from Brouwer via graph-approximate selections
demonstrates the power of three fundamental principles:
1. **Brouwer's FPT** (topological): continuous self-maps of compact convex sets have fixed points
2. **Cellina–Browder graph selections** (geometric): UHC maps with convex
   values admit continuous functions whose graph lies in any prescribed
   neighborhood of the graph of `F`
3. **Compactness** (analytical): bounded sequences have convergent subsequences

The combination yields fixed points for set-valued maps — the cornerstone
of Nash equilibrium existence in game theory.

### Infrastructure Needed in Mathlib
- Brouwer's FPT for general compact convex sets (currently only for closed balls)
- Partition of unity construction for finite open covers in Euclidean space
  (powering the Cellina–Browder construction)

### Alternative Proof Paths
1. **Simplicial approximation**: Triangulate S, define PL approximations. Avoids
   partition of unity but needs triangulation machinery.
2. **Michael's selection theorem**: Stronger than needed here (gives exact continuous
   selections for lower hemicontinuous maps with convex values).

### Why not a pointwise approximate selection?
Under USC + convex values, the pointwise form
`∀ x, ∃ y ∈ F x, dist (f x) y < ε` is provably false in general (S6
analysis: 1-D counterexample with `F(0) = [0,1]`, `F(t > 0) = {0}`,
`F(t < 0) = {1}` admits no continuous pointwise (1/3)-selection by an
IVT argument at `0`). The graph form is the strongest selection
provable from USC alone, and is what Mathlib's `PartitionOfUnity`
infrastructure can produce via the Cellina averaging argument.

## Summary

### Axioms (2)
1. `brouwer_unit_ball` — Brouwer's FPT on the closed unit ball in
   `EuclideanSpace ℝ (Fin n)` (S11.A strict-weakening, 2026-05-09).
   Strictly weaker than the previous `axiom brouwer_fpt` (general
   compact convex `S`); the general form is now derived as
   `theorem brouwer_fpt` via in-house retraction reduction.
2. `approx_selection_exists` — UHC + convex values → continuous
   `ε`-graph-approximate selections (Cellina–Browder form).

### Theorems (proved + transitional)
- `seq_compact_of_compact` — Sequential compactness in compact metric
  spaces (was an axiom; now derived from Mathlib).
- `approx_fixedpoint_implies_fixedpoint` — Limit argument for
  approximate fixed points.
- `kakutani_from_brouwer` — The main reduction: Kakutani from the two
  axioms (uses the graph form via a triangle-inequality
  `ε ↦ 2·(ε/2) = ε` step).
- `brouwer_fpt` — Brouwer's FPT for general compact convex `S`,
  derived from `axiom brouwer_unit_ball` via the elementwise rescaling
  retraction reduction (S11.A.body landed S13, researcher-10,
  2026-05-09). End-to-end sorry-free as of S14 (researcher-9,
  2026-05-09): the helper `exists_continuous_proj_convex` is now
  proven, so the only Brouwer-side assumption is the closed-unit-ball
  axiom.
- `exists_continuous_proj_convex` — Continuous nearest-point retraction
  onto a compact convex set, used by the `brouwer_fpt` body. **Proven
  in S14 (researcher-9, 2026-05-09)** via
  `exists_norm_eq_iInf_of_complete_convex` (existence) +
  `norm_eq_iInf_iff_real_inner_le_zero` (variational inequality) +
  `abs_real_inner_le_norm` (Cauchy-Schwarz, for the 1-Lipschitz step).

### Path to Full Verification
1. ~~**S11.B**: prove `exists_continuous_proj_convex` from
   `Mathlib.Analysis.InnerProductSpace.Projection` API.~~ **Done in
   S14 (researcher-9, 2026-05-09).** `theorem brouwer_fpt` is now
   end-to-end sorry-free. The only remaining Brouwer-side assumption
   is the closed-unit-ball axiom `brouwer_unit_ball`.
2. **S15+ (current frontier)**: prove `approx_selection_exists` (graph
   form) using `PartitionOfUnity` plus the Cellina averaging argument.
3. **(Optional, far future)**: in-house Brouwer FPT proof to eliminate
   `brouwer_unit_ball` (Option B from S10's note).
-/

#check @brouwer_unit_ball
#check @brouwer_fpt
#check @exists_continuous_proj_convex
#check @approx_selection_exists
#check @approx_fixedpoint_implies_fixedpoint
#check @kakutani_from_brouwer

end KakutaniFromBrouwer
