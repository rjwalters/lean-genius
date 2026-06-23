/-
  Kronecker's Density Theorem: Integer Multiples of an Irrational are Dense mod 1
  (research problem: dirichlet-approximation-theorem-oq-04)

  The parent entry `dirichlet-approximation-theorem` and its open-question siblings study the
  EXISTENCE and COUNTING of good rational approximations p/q to a real number (oq-01 counts the
  ~1/q² good approximations; oq-03 re-derives Dirichlet's bound via Minkowski's geometry of
  numbers; oq-05 proves the dual sharpness statement for the golden ratio).  This file proves the
  TOPOLOGICAL precursor of equidistribution that underlies all of them:

  **Main result (Kronecker / Weyl, qualitative form).**  For a real number `a`, the integer
  multiples `{n • a : n ∈ ℤ}`, viewed on the circle `ℝ/ℤ = AddCircle 1`, are *dense* iff `a` is
  irrational:

        DenseRange (fun n : ℤ => (n • a : AddCircle 1))  ↔  Irrational a.

  Equivalently: an irrational rotation of the circle has every orbit dense (it is *minimal*),
  while a rational `a = p/q` produces a finite, evenly-spaced orbit of `q` points.

  **Diophantine corollary (homogeneous one-sided approximation).**  Density at the point `0`
  gives the homogeneous form of Dirichlet's approximation theorem: for irrational `a` and every
  `ε > 0` there is a *positive integer* `n` whose multiple `n·a` lands within `ε` of an integer,

        ∃ n > 0,  |n·a − round (n·a)|  <  ε.

  Here `|x − round x|` is exactly the distance from `x` to the nearest integer, i.e. the norm of
  `x` on the circle `AddCircle 1` (`AddCircle.norm_eq` specialised to period `1`).  This is the
  statement that the fractional parts `{n·a}` accumulate at `0`, the qualitative seed of Weyl's
  equidistribution theorem.

  **Proof idea.**  The density iff is the period-`1` specialisation of Mathlib's
  `AddCircle.denseRange_zsmul_coe_iff` (multiples of `a` are dense on the circle of length `p` iff
  `a/p` is irrational), using `a/1 = a`.  For the corollary we feed density a small *punctured*
  ball `B(0,ε) ∖ {0}` (nonempty because the circle contains genuine nonzero points arbitrarily
  close to `0`): density meets it at some `k • a` with `0 < ‖k•a‖ < ε`, forcing `k ≠ 0`.  Taking
  `n = |k|` and reading the circle norm back as distance-to-nearest-integer gives the bound.

  No new axioms; everything reduces to Mathlib's `AddCircle` API.
-/
import Mathlib

open Metric

namespace DirichletApproximationOQ04

/-- **Kronecker's density theorem.**  The integer multiples of `a`, taken on the circle
`ℝ/ℤ = AddCircle 1`, are dense if and only if `a` is irrational.  This is the period-`1` case of
`AddCircle.denseRange_zsmul_coe_iff` (`a / 1 = a`). -/
theorem denseRange_iff_irrational (a : ℝ) :
    DenseRange (fun n : ℤ => (↑(n • a) : AddCircle (1 : ℝ))) ↔ Irrational a := by
  have h := AddCircle.denseRange_zsmul_coe_iff (a := a) (p := (1 : ℝ))
  rwa [div_one] at h

/-- **Homogeneous Dirichlet / Kronecker approximation.**  If `a` is irrational then its integer
multiples come arbitrarily close to integers: for every `ε > 0` there is a positive integer `n`
with `|n·a − round (n·a)| < ε`.  The quantity `|x − round x|` is the distance from `x` to the
nearest integer, equivalently the circle-norm `‖(x : AddCircle 1)‖`. -/
theorem exists_pos_nat_mul_sub_round_lt {a : ℝ} (ha : Irrational a) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ |(n : ℝ) * a - round ((n : ℝ) * a)| < ε := by
  -- The orbit of `a` is dense on the circle.
  have hd : DenseRange (fun n : ℤ => (↑(n • a) : AddCircle (1 : ℝ))) :=
    (denseRange_iff_irrational a).mpr ha
  -- A small, genuinely nonzero point of the circle, sitting within `ε` of `0`.
  set δ : ℝ := min ε 1 / 2 with hδdef
  have hminpos : 0 < min ε 1 := lt_min hε one_pos
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδle : δ ≤ 1 / 2 := by rw [hδdef]; linarith [min_le_right ε 1]
  have hδlt : δ < ε := by rw [hδdef]; linarith [min_le_left ε 1]
  -- Its circle-norm equals `δ` because `0 ≤ δ ≤ 1/2`.
  have hδabs : |δ| ≤ |(1 : ℝ)| / 2 := by rw [abs_of_nonneg hδpos.le, abs_one]; linarith
  have hnormδ : ‖(↑δ : AddCircle (1 : ℝ))‖ = δ := by
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)).mpr hδabs,
      abs_of_nonneg hδpos.le]
  -- The punctured ball `B(0, ε) ∖ {0}` is open and nonempty.
  have hUopen : IsOpen ((ball (0 : AddCircle (1 : ℝ)) ε) \ {0}) :=
    isOpen_ball.sdiff isClosed_singleton
  have hδne : (↑δ : AddCircle (1 : ℝ)) ≠ 0 := by
    rw [← norm_ne_zero_iff, hnormδ]; exact ne_of_gt hδpos
  have hUne : ((ball (0 : AddCircle (1 : ℝ)) ε) \ {0}).Nonempty := by
    refine ⟨(↑δ : AddCircle (1 : ℝ)), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, hnormδ]; exact hδlt
    · simpa using hδne
  -- Density meets the punctured ball: some `k • a` is within `ε` of `0` but not `0`.
  obtain ⟨k, hk⟩ := hd.exists_mem_open hUopen hUne
  have hbound : ‖(↑((k : ℝ) * a) : AddCircle (1 : ℝ))‖ < ε := by
    have hmem := hk.1
    simp only [mem_ball, dist_zero_right] at hmem
    rwa [zsmul_eq_mul] at hmem
  have hkne : (↑(k • a) : AddCircle (1 : ℝ)) ≠ 0 := by simpa using hk.2
  have hk0 : k ≠ 0 := by rintro rfl; exact hkne (by simp)
  -- Take `n = |k| > 0` and read the circle-norm back as distance to the nearest integer.
  refine ⟨k.natAbs, Int.natAbs_pos.mpr hk0, ?_⟩
  have key : ‖(↑((k.natAbs : ℝ) * a) : AddCircle (1 : ℝ))‖
      = |(k.natAbs : ℝ) * a - round ((k.natAbs : ℝ) * a)| := by
    rw [AddCircle.norm_eq, inv_one, one_mul, mul_one]
  have hnorm_match : ‖(↑((k.natAbs : ℝ) * a) : AddCircle (1 : ℝ))‖
      = ‖(↑((k : ℝ) * a) : AddCircle (1 : ℝ))‖ := by
    rw [Nat.cast_natAbs]
    rcases abs_choice k with h | h
    · rw [h]
    · rw [h]
      push_cast
      rw [neg_mul, AddCircle.coe_neg, norm_neg]
  rw [← key, hnorm_match]
  exact hbound

end DirichletApproximationOQ04
