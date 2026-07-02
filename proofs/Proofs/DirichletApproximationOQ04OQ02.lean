/-
  Inhomogeneous Kronecker Approximation: Minimality of the Irrational Rotation
  (research problem: dirichlet-approximation-theorem-oq-04-oq-02)

  The parent entry `dirichlet-approximation-theorem-oq-04` proves the *homogeneous* form of
  Kronecker's density theorem: for a real number `a`, the integer multiples `{n • a : n ∈ ℤ}`,
  viewed on the circle `ℝ/ℤ = AddCircle 1`, are dense iff `a` is irrational, and consequently the
  fractional parts `{n·a}` accumulate at the single point `0` (the multiples come arbitrarily
  close to *integers*).

  This entry upgrades that to the *inhomogeneous* theorem — the genuine one-dimensional case of
  Kronecker's approximation theorem, and equivalently the statement that an irrational rotation of
  the circle is **minimal** (every orbit is dense, not just the orbit of `0`):

  **Topological form (minimality).**  For irrational `a` and *any* base point `b : AddCircle 1`,
  the shifted orbit is still dense:

        DenseRange (fun n : ℤ => (n • a : AddCircle 1) + b).

  This is strictly stronger than `oq-04`, which is the special case `b = 0`.  It says the closure
  of every orbit is the whole circle, i.e. the rotation `x ↦ x + a` has no proper closed invariant
  subset — it is minimal.

  **Diophantine form (inhomogeneous approximation).**  For irrational `a`, *any* target real
  number `β`, and every `ε > 0` there is an integer `n` whose multiple `n·a` approximates `β`
  modulo `1`:

        ∃ n : ℤ,  |n·a − β − round (n·a − β)|  <  ε.

  Here `|x − round x|` is the distance from `x` to the nearest integer, i.e. the circle-norm
  `‖(x : AddCircle 1)‖` (`AddCircle.norm_eq` at period `1`).  The homogeneous `oq-04` corollary is
  the case `β = 0`; the inhomogeneous statement says the fractional parts `{n·a}` are dense in the
  whole interval, not merely accumulating at `0`.

  **Proof idea.**  Both statements descend from the homogeneous density
  `DenseRange (fun n : ℤ => (n • a : AddCircle 1))` proved in `oq-04`.
  * Minimality: translation `x ↦ x + b` on the circle is a continuous surjection, so it has dense
    range; composing a dense-range map with it (via `DenseRange.comp`) keeps the range dense.
  * Approximation: a dense set meets every ball, in particular the `ε`-ball around the point
    `(β : AddCircle 1)`; reading the resulting circle-distance back as distance-to-nearest-integer
    gives the bound.

  No new axioms; everything reduces to the `oq-04` density statement and Mathlib's `AddCircle` API.
-/
import Mathlib

open Metric

namespace DirichletApproximationOQ04OQ02

/-- **Homogeneous Kronecker density** (imported from `oq-04`).  The integer multiples of an
irrational `a`, taken on the circle `ℝ/ℤ = AddCircle 1`, are dense.  This is the period-`1` case of
`AddCircle.denseRange_zsmul_coe_iff` (`a / 1 = a`). -/
theorem denseRange_zsmul_of_irrational {a : ℝ} (ha : Irrational a) :
    DenseRange (fun n : ℤ => (↑(n • a) : AddCircle (1 : ℝ))) := by
  have h := AddCircle.denseRange_zsmul_coe_iff (a := a) (p := (1 : ℝ))
  rw [div_one] at h
  exact h.mpr ha

/-- **Minimality of the irrational rotation.**  For irrational `a` and *any* base point
`b : AddCircle 1`, the shifted orbit `{n • a + b : n ∈ ℤ}` is dense.  Equivalently, the rotation
`x ↦ x + a` of the circle is minimal: every orbit is dense, not just the orbit of `0`
(which is `oq-04`, the case `b = 0`). -/
theorem denseRange_zsmul_add_of_irrational {a : ℝ} (ha : Irrational a) (b : AddCircle (1 : ℝ)) :
    DenseRange (fun n : ℤ => (↑(n • a) : AddCircle (1 : ℝ)) + b) := by
  -- Translation `x ↦ x + b` is a continuous surjection, hence has dense range.
  have hsurj : Function.Surjective (fun x : AddCircle (1 : ℝ) => x + b) :=
    fun y => ⟨y - b, by simp⟩
  have hgdense : DenseRange (fun x : AddCircle (1 : ℝ) => x + b) := hsurj.denseRange
  have hgcont : Continuous (fun x : AddCircle (1 : ℝ) => x + b) := by fun_prop
  -- Compose the dense homogeneous orbit with the translation.
  have := hgdense.comp (denseRange_zsmul_of_irrational ha) hgcont
  simpa [Function.comp] using this

/-- **Inhomogeneous Kronecker / Dirichlet approximation.**  If `a` is irrational then its integer
multiples approximate *every* real number `β` modulo `1`: for every `ε > 0` there is an integer `n`
with `|n·a − β − round (n·a − β)| < ε`.  The quantity `|x − round x|` is the distance from `x` to
the nearest integer, equivalently the circle-norm `‖(x : AddCircle 1)‖`.  The homogeneous `oq-04`
corollary is the special case `β = 0`. -/
theorem exists_int_zsmul_sub_round_lt {a : ℝ} (ha : Irrational a) (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℤ, |(n : ℝ) * a - β - round ((n : ℝ) * a - β)| < ε := by
  -- The homogeneous orbit is dense on the circle.
  have hd : DenseRange (fun n : ℤ => (↑(n • a) : AddCircle (1 : ℝ))) :=
    denseRange_zsmul_of_irrational ha
  -- The `ε`-ball around the target point `(β : AddCircle 1)` is open and nonempty.
  have hUopen : IsOpen (ball (↑β : AddCircle (1 : ℝ)) ε) := isOpen_ball
  have hUne : (ball (↑β : AddCircle (1 : ℝ)) ε).Nonempty := ⟨_, mem_ball_self hε⟩
  -- Density meets the ball: some `k • a` lands within `ε` of `β`.
  obtain ⟨k, hk⟩ := hd.exists_mem_open hUopen hUne
  -- Turn the circle-distance into the circle-norm of `↑(k·a − β)`.
  have hdist : ‖(↑((k : ℝ) * a - β) : AddCircle (1 : ℝ))‖ < ε := by
    have hmem := hk
    simp only [mem_ball, dist_eq_norm] at hmem
    rwa [zsmul_eq_mul, ← AddCircle.coe_sub] at hmem
  refine ⟨k, ?_⟩
  -- Read the circle-norm back as distance to the nearest integer.
  have key : ‖(↑((k : ℝ) * a - β) : AddCircle (1 : ℝ))‖
      = |(k : ℝ) * a - β - round ((k : ℝ) * a - β)| := by
    rw [AddCircle.norm_eq, inv_one, one_mul, mul_one]
  rwa [key] at hdist

end DirichletApproximationOQ04OQ02
