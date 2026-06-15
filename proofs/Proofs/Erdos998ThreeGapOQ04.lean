/-
  The Three-Gap / Three-Distance (Steinhaus) Theorem — Formal Statement and Path
  (erdos-998-oq-04)

  ## Background

  Erdős Problem #998 (Kesten's equidistribution theorem) is built on the orbit
  structure of an irrational rotation `m ↦ {mα}` on the circle `[0,1)`.  The
  *three-distance theorem* (Steinhaus conjecture; proved by Sós, Surányi, and
  Świerczkowski) describes that orbit structure exactly:

    **For every irrational `α` and every `N ≥ 1`, the `N` points
    `{0, {α}, {2α}, …, {(N-1)α}}` cut the circle into `N` arcs whose lengths
    take at most THREE distinct values; moreover, when three values occur, the
    largest is the sum of the other two.**

  The parent file `Erdos998Problem.lean` only mentions this theorem in a prose
  docstring (Part V).  This file gives the first *formal Lean statement* of the
  theorem together with the elementary structural infrastructure, isolating the
  remaining combinatorial core.

  ## Mathlib status (June 2026)

  Mathlib4 does **not** contain the three-gap theorem.  A Coq formalization
  (van Ravenstein's proof) exists, but no Lean version.  The theorem is purely
  finite/order-theoretic — no measure theory or analysis is needed — so it is a
  natural Mathlib-style target built from `Int.fract`, `Finset`, and the linear
  order on `ℝ`.

  ## What is proved here vs. left open

  PROVED (elementary, robust):
    * `orbit_mem_Ico`     — every orbit point lies in `[0,1)`
    * `zero_mem_orbit`    — `0` is always an orbit point (the `i = 0` term)
    * `orbit_nonempty`    — the orbit is nonempty for `N ≥ 1`
    * `forwardGap_nonneg` — every forward gap length is `≥ 0`
    * `orbit_card`        — for irrational `α` the orbit has exactly `N` points
                            (injectivity of `i ↦ {iα}` via `Int.fract_eq_fract`
                            and `Irrational.int_mul`)

  ISOLATED (the genuine content — see the proof-path comments and knowledge.md):
    * `three_gap`         — at most three distinct gap lengths  [HARD core]
    * `three_gap_additive`— the additive relation among the three lengths

  ## Status: build-pending (worktree `.lake` circular-symlink OOM this cycle);
  Mathlib bearers name-checked against the pinned rev 2df2f01 / v4.26.0.
-/
import Mathlib

namespace Erdos998ThreeGap

open Finset

/-- The orbit of the rotation by `α` after `N` steps, viewed as a finite subset
    of `[0,1)`: the fractional parts `{0, {α}, {2α}, …, {(N-1)α}}`. -/
noncomputable def orbit (α : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.range N).image (fun i => Int.fract ((i : ℝ) * α))

/-- Every orbit point lies in the half-open unit interval `[0,1)`. -/
theorem orbit_mem_Ico {α : ℝ} {N : ℕ} {x : ℝ} (hx : x ∈ orbit α N) :
    0 ≤ x ∧ x < 1 := by
  simp only [orbit, Finset.mem_image] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- `0` is always an orbit point, contributed by the `i = 0` term. -/
theorem zero_mem_orbit (α : ℝ) {N : ℕ} (hN : 0 < N) : (0 : ℝ) ∈ orbit α N := by
  simp only [orbit, Finset.mem_image, Finset.mem_range]
  exact ⟨0, hN, by simp⟩

/-- The orbit is nonempty whenever `N ≥ 1`. -/
theorem orbit_nonempty (α : ℝ) {N : ℕ} (hN : 0 < N) : (orbit α N).Nonempty :=
  ⟨0, zero_mem_orbit α hN⟩

/-- The forward gap of an orbit point `x`: the shortest *positive cyclic*
    distance `{y - x}` from `x` to another orbit point `y`.  Cyclic distance is
    measured by `Int.fract (y - x) ∈ [0,1)`, so the minimum over `y ≠ x` is the
    length of the arc immediately clockwise-to-counterclockwise of `x`.  Defined
    totally via `dite`; the junk value `0` is only hit on the (excluded) empty
    case `N ≤ 1`. -/
noncomputable def forwardGap (α : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  if h : ((orbit α N).erase x).Nonempty then
    ((orbit α N).erase x).inf' h (fun y => Int.fract (y - x))
  else 0

/-- The finite set of distinct gap lengths produced by the `N`-point orbit. -/
noncomputable def gapLengths (α : ℝ) (N : ℕ) : Finset ℝ :=
  (orbit α N).image (forwardGap α N)

/-- Every forward gap length is nonnegative (each cyclic distance `{y - x}` is
    `≥ 0`, and so is their minimum; the junk branch is `0`). -/
theorem forwardGap_nonneg (α : ℝ) (N : ℕ) (x : ℝ) : 0 ≤ forwardGap α N x := by
  unfold forwardGap
  split
  · rename_i h
    exact Finset.le_inf' h _ (fun y _ => Int.fract_nonneg _)
  · exact le_refl 0

/-- For irrational `α` the map `i ↦ {iα}` is injective on `ℕ`, hence the orbit
    has exactly `N` distinct points.

    PROOF PATH (injectivity): if `{iα} = {jα}` then by `Int.fract_eq_fract`
    there is `z : ℤ` with `iα - jα = z`, i.e. `(i - j) · α = z`.  If `i ≠ j`
    then `(i - j : ℝ) ≠ 0`, so `α = z / (i - j)` is rational, contradicting
    `hα : Irrational α`.  Cardinality then follows from
    `Finset.card_image_of_injective` and `Finset.card_range`. -/
theorem orbit_card {α : ℝ} (hα : Irrational α) (N : ℕ) :
    (orbit α N).card = N := by
  have hinj : Set.InjOn (fun i : ℕ => Int.fract ((i : ℝ) * α)) ↑(Finset.range N) := by
    intro i _ j _ hij
    simp only at hij
    by_contra hne
    rw [Int.fract_eq_fract] at hij
    obtain ⟨z, hz⟩ := hij
    have hm : ((i : ℤ) - (j : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    have key : (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) * α = (z : ℝ) := by
      push_cast
      rw [sub_mul]
      exact hz
    have hirr : Irrational ((((i : ℤ) - (j : ℤ) : ℤ) : ℝ) * α) := hα.int_mul hm
    rw [key] at hirr
    exact (not_irrational_int z) hirr
  rw [orbit, Finset.card_image_of_injOn hinj, Finset.card_range]

/-- **The Three-Gap (Three-Distance / Steinhaus) Theorem.**

    For every irrational `α` and every `N ≥ 1`, the `N` arc lengths cut out of
    the circle by the orbit `{0, {α}, …, {(N-1)α}}` take at most three distinct
    values.

    PROOF PATH (van Ravenstein / Sós, elementary):

    1. Let `p` be the least index in `1 ≤ p < N` minimizing the *forward* return
       `{pα}` (the smallest clockwise gap at the point `0`), and `q` the least
       index minimizing the *backward* return `1 - {qα}`.  These two "first
       return" indices are the Steinhaus generators.

    2. CLASSIFICATION OF GAPS.  Walk the points in circular order.  Each point
       `{iα}` is the left endpoint of exactly one gap, and its forward neighbour
       is obtained by adding either `p` or `q` to the index `i` (whichever keeps
       the result in `[0, N)` after the rotation).  Concretely the forward
       neighbour of `{iα}` is `{(i+p)α}` if `i + p < N`, else `{(i - q)α}` /
       wrap.  Hence every gap length is one of:
         • `{pα}`              (a "short" gap, count `N - p`),
         • `1 - {qα}`          (a "short" gap, count `N - q`),
         • `{pα} + 1 - {qα}`   (the "long" gap, count `p + q - N`).
       This already gives ≤ 3 distinct values.

    3. The three counts sum to `N` (`(N-p) + (N-q) + (p+q-N) = N`), confirming
       the gap-count bookkeeping.

    KEY MATHLIB PIECES: `Int.fract`, `Int.fract_eq_fract`, `Finset.min'`/`inf'`,
    `Finset.exists_min_image`; the index arithmetic is `Nat`/`Finset.range`
    order theory only.  No new Mathlib infrastructure is required — only the
    case analysis above, which is the remaining work. -/
theorem three_gap (α : ℝ) (hα : Irrational α) {N : ℕ} (hN : 1 ≤ N) :
    (gapLengths α N).card ≤ 3 := by
  sorry

/-- **Additive structure of the three gaps.**  When three distinct gap lengths
    occur, one of them is the sum of the other two (hence equal to the largest).
    This is immediate from the classification in `three_gap`: the long gap
    `{pα} + (1 - {qα})` is the sum of the two short gaps `{pα}` and `1 - {qα}`. -/
theorem three_gap_additive (α : ℝ) (hα : Irrational α) {N : ℕ} (hN : 1 ≤ N)
    (h3 : (gapLengths α N).card = 3) :
    ∃ a b c : ℝ, a ∈ gapLengths α N ∧ b ∈ gapLengths α N ∧ c ∈ gapLengths α N ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a + b = c := by
  sorry

end Erdos998ThreeGap
