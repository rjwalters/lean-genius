/-
  The Class-Number / Siegel-Zero Equivalence, Made Tight
  (Dirichlet OQ-01-OQ-01-OQ-04)

  Open question from DirichletsTheoremOQ01OQ01 (openQuestions[3]):
    "Can the class-number / Siegel-zero equivalence (via Goldfeld–Gross–Zagier)
     be made tight, giving an unconditional polynomial-log lower bound on h(-D)
     that would resolve the depth of Siegel zeros?"

  Background. For the imaginary quadratic field ℚ(√-D), Dirichlet's analytic
  class number formula states
        h(-D) = κ · √D · L(1, χ_{-D}),   κ = w/(2π) > 0,
  where w is the number of roots of unity. Thus the class number h(-D) and the
  special L-value L(1, χ_{-D}) carry the *same* information, up to the explicit
  factor κ√D. A "Siegel zero" of χ_{-D} is a real zero β close to 1; by the mean
  value theorem the L-value is squeezed by the depth (1-β):
        m·(1-β) ≤ L(1,χ) ≤ M·(1-β).

  This file makes the equivalence precise and *tight* at the abstract level,
  WITHOUT introducing any axioms:

  - The class number formula is carried as an explicit hypothesis `h = κ √D · L`.
  - `classNumber_ge_iff_Lvalue_ge`: a class-number lower bound `κ√D·B ≤ h` is
    *equivalent* (iff, with the identical constant κ√D — no log losses) to the
    L-value lower bound `B ≤ L`. This is the sense in which the equivalence is
    tight: nothing is lost passing between the two worlds.
  - `classNumber_lower_bounds_zero_depth` / `zero_depth_lower_bounds_classNumber`:
    a two-way bridge, via the MVT comparison, between class-number lower bounds
    and Siegel-zero shallowness `B ≤ M(1-β)`.
  - `ggz_lower_bound_transported`: the effective Goldfeld–Gross–Zagier bound
    `c·g ≤ h` transports verbatim to an effective L-value bound; improving the
    shape g(D) from log-power to √D-power is exactly what would resolve the depth
    of Siegel zeros.

  What stays OPEN (the actual content of the question) is supplying the
  unconditional lower bound `B` of polynomial-log shape — that is the deep
  analytic input (zero-density / GGZ improvements) not in reach here. Here `B`
  is a free parameter; we prove the equivalences it must satisfy.

  Self-contained: imports only Mathlib (real analysis). 0 axioms, 0 sorries —
  every theorem is conditional on its explicitly stated hypotheses.

  References:
  - Goldfeld, "The class number of quadratic fields and the conjectures of Birch
    and Swinnerton-Dyer" (1976)
  - Gross & Zagier, "Heegner points and derivatives of L-series" (1986)
  - Davenport, "Multiplicative Number Theory" (2000), §14, §21–22
-/

import Mathlib

namespace DirichletSiegelClassNumber

open Real

-- ═══════════════════════════════════════════════════════════════════════
-- PART I: THE TIGHT CLASS-NUMBER ⇔ L-VALUE EQUIVALENCE
-- ═══════════════════════════════════════════════════════════════════════

/-- **Tight class-number ⇔ L-value equivalence.** Under Dirichlet's class number
    formula `h = κ √D · L` with `κ, D > 0`, a class-number lower bound and the
    corresponding L-value lower bound are *equivalent with the identical constant*
    `κ√D` — no logarithmic loss in either direction. This is the precise sense in
    which the Goldfeld–Gross–Zagier equivalence is tight. -/
theorem classNumber_ge_iff_Lvalue_ge
    {κ D h L B : ℝ} (hκ : 0 < κ) (hD : 0 < D)
    (hform : h = κ * Real.sqrt D * L) :
    κ * Real.sqrt D * B ≤ h ↔ B ≤ L := by
  have hpos : 0 < κ * Real.sqrt D := mul_pos hκ (Real.sqrt_pos.mpr hD)
  rw [hform]
  exact ⟨fun hh => le_of_mul_le_mul_left hh hpos,
         fun hh => mul_le_mul_of_nonneg_left hh hpos.le⟩

/-- The same equivalence for strict lower bounds. -/
theorem classNumber_gt_iff_Lvalue_gt
    {κ D h L B : ℝ} (hκ : 0 < κ) (hD : 0 < D)
    (hform : h = κ * Real.sqrt D * L) :
    κ * Real.sqrt D * B < h ↔ B < L := by
  have hpos : 0 < κ * Real.sqrt D := mul_pos hκ (Real.sqrt_pos.mpr hD)
  rw [hform]
  exact ⟨fun hh => lt_of_mul_lt_mul_left hh hpos.le,
         fun hh => by nlinarith [hpos]⟩

-- ═══════════════════════════════════════════════════════════════════════
-- PART II: THE MEAN-VALUE BRIDGE TO SIEGEL-ZERO DEPTH
-- ═══════════════════════════════════════════════════════════════════════

/-- **Deep Siegel zero ⇒ small L-value.** If the MVT comparison `L ≤ M(1-β)`
    holds (`M ≥ 0`) and the zero is deep (`1-β ≤ δ`), then `L ≤ M·δ`. -/
theorem Lvalue_le_of_deep_zero
    {L M β δ : ℝ} (hM : 0 ≤ M)
    (hMVT : L ≤ M * (1 - β)) (hdepth : 1 - β ≤ δ) :
    L ≤ M * δ :=
  hMVT.trans (mul_le_mul_of_nonneg_left hdepth hM)

/-- **L-value lower bound ⇒ Siegel zero is shallow** (no division form).
    If `L ≤ M(1-β)` and `B ≤ L`, then `B ≤ M(1-β)`: an L-value floor pushes the
    zero away from 1. -/
theorem zero_depth_ge_of_Lvalue_ge
    {L M β B : ℝ} (hMVT : L ≤ M * (1 - β)) (hL : B ≤ L) :
    B ≤ M * (1 - β) :=
  hL.trans hMVT

/-- Explicit depth bound: with `M > 0`, the previous bound rearranges to
    `B / M ≤ 1 - β`. -/
theorem zero_depth_lower_explicit
    {L M β B : ℝ} (hM : 0 < M)
    (hMVT : L ≤ M * (1 - β)) (hL : B ≤ L) :
    B / M ≤ 1 - β := by
  have hBle : B ≤ M * (1 - β) := hL.trans hMVT
  rw [div_le_iff₀ hM]
  nlinarith

-- ═══════════════════════════════════════════════════════════════════════
-- PART III: THE TWO-WAY CLASS-NUMBER ⇔ SIEGEL-DEPTH BRIDGE
-- ═══════════════════════════════════════════════════════════════════════

/-- **Class-number lower bound ⇒ Siegel zero shallow.** Combining the tight
    equivalence with the MVT upper comparison: a class-number floor `κ√D·B ≤ h`
    forces `B ≤ M(1-β)`. Resolving Siegel-zero depth is therefore *at least as
    hard* as an unconditional class-number lower bound. -/
theorem classNumber_lower_bounds_zero_depth
    {κ D h L M β B : ℝ} (hκ : 0 < κ) (hD : 0 < D)
    (hform : h = κ * Real.sqrt D * L) (hMVT : L ≤ M * (1 - β))
    (hclass : κ * Real.sqrt D * B ≤ h) :
    B ≤ M * (1 - β) :=
  ((classNumber_ge_iff_Lvalue_ge hκ hD hform).mp hclass).trans hMVT

/-- **Siegel zero depth ⇒ class-number lower bound.** With the MVT *lower*
    comparison `m(1-β) ≤ L`, a depth bound `B ≤ m(1-β)` yields the class-number
    floor `κ√D·B ≤ h`. Together with the previous theorem, the class-number
    lower bound and the Siegel-zero depth bound are equivalent. -/
theorem zero_depth_lower_bounds_classNumber
    {κ D h L m β B : ℝ} (hκ : 0 < κ) (hD : 0 < D)
    (hform : h = κ * Real.sqrt D * L) (hMVT : m * (1 - β) ≤ L)
    (hdepth : B ≤ m * (1 - β)) :
    κ * Real.sqrt D * B ≤ h :=
  (classNumber_ge_iff_Lvalue_ge hκ hD hform).mpr (hdepth.trans hMVT)

-- ═══════════════════════════════════════════════════════════════════════
-- PART IV: GOLDFELD–GROSS–ZAGIER, TRANSPORTED
-- ═══════════════════════════════════════════════════════════════════════

/-- **GGZ transported.** The effective class-number lower bound `c·g ≤ h`
    (Goldfeld–Gross–Zagier, with `g` a power of `log D`) is, via the class number
    formula, exactly the effective L-value bound `c·g ≤ κ√D·L`. Improving the
    shape `g` from a log-power to a √D-power is precisely what would resolve the
    depth of Siegel zeros. -/
theorem ggz_lower_bound_transported
    {κ D h L c g : ℝ} (hform : h = κ * Real.sqrt D * L) (hggz : c * g ≤ h) :
    c * g ≤ κ * Real.sqrt D * L := by
  rwa [← hform]

/-- Combining GGZ with the tight equivalence (κ, D > 0): the effective bound
    `c·g ≤ h` gives the L-value floor `c·g ≤ κ√D·L`, and hence — via the MVT
    comparison — the Siegel-zero shallowness bound `c·g ≤ κ√D·M(1-β)`. -/
theorem ggz_bounds_zero_depth
    {κ D h L M β c g : ℝ} (hκ : 0 < κ) (hD : 0 < D)
    (hform : h = κ * Real.sqrt D * L) (hMVT : L ≤ M * (1 - β))
    (hggz : c * g ≤ h) :
    c * g ≤ κ * Real.sqrt D * (M * (1 - β)) := by
  have hpos : 0 ≤ κ * Real.sqrt D := (mul_pos hκ (Real.sqrt_pos.mpr hD)).le
  calc c * g ≤ κ * Real.sqrt D * L := by rwa [← hform]
    _ ≤ κ * Real.sqrt D * (M * (1 - β)) := mul_le_mul_of_nonneg_left hMVT hpos

-- ═══════════════════════════════════════════════════════════════════════
-- PART V: SANITY CHECKS
-- ═══════════════════════════════════════════════════════════════════════

-- The class number is positive exactly when the L-value is (given the formula).
example {κ D h L : ℝ} (hκ : 0 < κ) (hD : 0 < D)
    (hform : h = κ * Real.sqrt D * L) : 0 < h ↔ 0 < L := by
  have := classNumber_gt_iff_Lvalue_gt (B := 0) hκ hD hform
  simpa using this

-- A concrete instance of the tight equivalence: κ = 1, D = 4 (√4 = 2).
example {h L B : ℝ} (hform : h = 1 * Real.sqrt 4 * L) :
    1 * Real.sqrt 4 * B ≤ h ↔ B ≤ L :=
  classNumber_ge_iff_Lvalue_ge (by norm_num) (by norm_num) hform

end DirichletSiegelClassNumber
