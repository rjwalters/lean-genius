/-
  # Norm-Euclidean `ℤ[√d]` for the imaginary quadratic family — a uniform treatment

  The parent gallery entries proved that the Gaussian integers `ℤ[i] = ℤ[√-1]` and
  the ring `ℤ[√-2]` are Euclidean domains, each through an ad-hoc rounding bound
  (`1/2` and `3/4` respectively). This file answers the third open question of the
  `ℤ[√-2]` entry:

    > Can the Euclidean-domain proof be generalised to a parameterised family
    > `Zsqrtd d` for `d ∈ {-1,-2,-3,-7,-11}` with a *uniform* bound?

  ## What we prove

  For an arbitrary negative `d` we analyse the "nearest-lattice-point" division of
  `Zsqrtd d`: given `x` and `y ≠ 0`, round each coordinate of `x · conj y / N(y)`
  to the nearest integer. The remainder `r = x − y·q` then satisfies the *single
  uniform inequality*

      `4 · N(r) · N(y) ≤ (1 − d) · N(y)²`                        (`four_mul_norm_rem_le`)

  for every negative `d`, i.e. `N(r) ≤ (1 − d)/4 · N(y)`. Hence whenever
  `-2 ≤ d < 0` — that is, exactly `d ∈ {-1, -2}` — the factor is
  `(1 − d)/4 ≤ 3/4 < 1`, so `N(r) < N(y)` (`norm_rem_lt`) and `ℤ[√d]` is
  **norm-Euclidean with one uniform bound**. We package this as a value
  `EuclideanDomain (ℤ√d)` depending only on the hypothesis `-2 ≤ d < 0`
  (`euclideanDomain`), recovering both classical rings at once
  (`euclideanDomainNegOne`, `euclideanDomainNegTwo`).

  ## Why the family stops at `d = -2` (honest scope)

  The open question lists `d ∈ {-1,-2,-3,-7,-11}`, but for `d = -3,-7,-11` the
  object `Zsqrtd d` is the **wrong ring**: there the ring of integers of `ℚ(√d)`
  is `ℤ[(1+√d)/2]`, not `ℤ[√d]`, and `ℤ[√-3]` is not even integrally closed (so
  cannot be a PID, let alone a Euclidean domain). Correspondingly the
  nearest-point factor `(1 − d)/4` is `≥ 1` precisely when `d ≤ -3`
  (`nearest_point_factor_ge_one_of_le_neg_three`), so the uniform `Zsqrtd`
  argument provably cannot extend. This is a genuine arithmetic obstruction, not a
  weakness of the proof: the correct uniform family for all five discriminants
  lives over the rings of integers `ℤ[ω]`, a different formalisation.

  Everything is fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Zsqrtd

namespace NormEuclideanZsqrtdFamily

variable {d : ℤ}

/-! ### A rational rounding bound

The only analytic ingredient: rounding `m/k` to the nearest integer keeps the
scaled error `m − q·k` within `±k/2`, equivalently `(2·(m − q·k))² ≤ k²`. -/

/-- Rounding `m / k` (with `k > 0`) to the nearest integer `q := round (m/k)` gives
`(2·(m − q·k))² ≤ k²`. -/
theorem sq_two_mul_sub_round_le (m k : ℤ) (hk : 0 < k) :
    (2 * (m - round ((m : ℚ) / (k : ℚ)) * k)) ^ 2 ≤ k ^ 2 := by
  have hk' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  set q : ℤ := round ((m : ℚ) / (k : ℚ)) with hq
  have hround : |(m : ℚ) / (k : ℚ) - q| ≤ 1 / 2 := abs_sub_round _
  have hfac : (m : ℚ) - (q : ℚ) * k = (k : ℚ) * ((m : ℚ) / k - q) := by
    field_simp
  have herr : |(m : ℚ) - (q : ℚ) * k| ≤ (k : ℚ) / 2 := by
    rw [hfac, abs_mul, abs_of_pos hk']
    have hmul := mul_le_mul_of_nonneg_left hround hk'.le
    calc (k : ℚ) * |(m : ℚ) / k - q| ≤ (k : ℚ) * (1 / 2) := hmul
      _ = (k : ℚ) / 2 := by ring
  -- the integer square inequality, obtained over ℚ then cast back
  have hsq : ((2 * (m - q * k) : ℤ) : ℚ) ^ 2 ≤ ((k : ℤ) : ℚ) ^ 2 := by
    push_cast
    set X : ℚ := (m : ℚ) - (q : ℚ) * k with hX
    have h2 : |2 * X| ≤ (k : ℚ) := by
      rw [abs_mul, abs_two]; nlinarith [herr]
    have hsqabs : (2 * X) ^ 2 ≤ (k : ℚ) ^ 2 := by
      have hmm := mul_self_le_mul_self (abs_nonneg (2 * X)) h2
      rw [← sq_abs (2 * X)]; nlinarith [hmm]
    have hgoal : (2 * ((m : ℚ) - (q : ℚ) * k)) ^ 2 ≤ (k : ℚ) ^ 2 := by rw [← hX]; exact hsqabs
    convert hgoal using 2
  exact_mod_cast hsq

/-! ### Nearest-lattice-point division -/

variable (d) in
/-- The nearest-lattice-point quotient: round each coordinate of `x · conj y / N(y)`
to the nearest integer. (When `y = 0`, `N(y) = 0` and this is `0`, the convention
required by `EuclideanDomain.quotient_zero`.) -/
noncomputable def quo (x y : ℤ√d) : ℤ√d :=
  ⟨round (((x * star y).re : ℚ) / (y.norm : ℚ)),
   round (((x * star y).im : ℚ) / (y.norm : ℚ))⟩

variable (d) in
/-- The nearest-lattice-point remainder `r = x − y·q`. -/
noncomputable def rem (x y : ℤ√d) : ℤ√d := x - y * quo d x y

theorem quo_re (x y : ℤ√d) :
    (quo d x y).re = round (((x * star y).re : ℚ) / (y.norm : ℚ)) := rfl

theorem quo_im (x y : ℤ√d) :
    (quo d x y).im = round (((x * star y).im : ℚ) / (y.norm : ℚ)) := rfl

@[simp] theorem quotient_mul_add_remainder (x y : ℤ√d) :
    y * quo d x y + rem d x y = x := by
  simp [rem]

theorem quo_zero (x : ℤ√d) : quo d x 0 = 0 := by
  ext <;> simp [quo]

/-- The real part of `(rem)·conj y` is the rounding error of the real coordinate. -/
theorem rem_mul_star_re (x y : ℤ√d) :
    (rem d x y * star y).re = (x * star y).re - (quo d x y).re * y.norm := by
  have hy : (y : ℤ√d) * star y = (y.norm : ℤ√d) := (norm_eq_mul_conj y).symm
  have key : rem d x y * star y = x * star y - quo d x y * (y.norm : ℤ√d) := by
    rw [rem, sub_mul]
    have hrw : (y * quo d x y) * star y = quo d x y * (y.norm : ℤ√d) := by
      rw [mul_comm y, mul_assoc, hy]
    rw [hrw]
  rw [key]
  simp only [re_sub, re_mul, re_intCast, im_intCast]
  ring

/-- The imaginary part of `(rem)·conj y` is the rounding error of the imag coordinate. -/
theorem rem_mul_star_im (x y : ℤ√d) :
    (rem d x y * star y).im = (x * star y).im - (quo d x y).im * y.norm := by
  have hy : (y : ℤ√d) * star y = (y.norm : ℤ√d) := (norm_eq_mul_conj y).symm
  have key : rem d x y * star y = x * star y - quo d x y * (y.norm : ℤ√d) := by
    rw [rem, sub_mul]
    have hrw : (y * quo d x y) * star y = quo d x y * (y.norm : ℤ√d) := by
      rw [mul_comm y, mul_assoc, hy]
    rw [hrw]
  rw [key]
  simp only [im_sub, im_mul, re_intCast, im_intCast]
  ring

/-! ### The uniform norm bound -/

/-- **The uniform remainder bound.** For *every* negative `d`, the
nearest-lattice-point remainder satisfies `4 · N(r) · N(y) ≤ (1 − d) · N(y)²`.
The factor `(1 − d)/4` is the single uniform constant; it is `< 1` exactly when
`-2 ≤ d`. -/
theorem four_mul_norm_rem_le (hd : d < 0) (x y : ℤ√d) :
    4 * ((rem d x y).norm * y.norm) ≤ (1 - d) * y.norm ^ 2 := by
  rcases lt_or_eq_of_le (norm_nonneg hd.le y) with hpos | h0
  · -- the generic case `0 < N(y)`
    set R := rem d x y * star y with hR
    have hRnorm : R.norm = (rem d x y).norm * y.norm := by rw [hR, norm_mul, norm_conj]
    have hbre : (2 * R.re) ^ 2 ≤ y.norm ^ 2 := by
      rw [hR, rem_mul_star_re, quo_re]; exact sq_two_mul_sub_round_le _ y.norm hpos
    have hbim : (2 * R.im) ^ 2 ≤ y.norm ^ 2 := by
      rw [hR, rem_mul_star_im, quo_im]; exact sq_two_mul_sub_round_le _ y.norm hpos
    have hRdef : R.norm = R.re * R.re - d * R.im * R.im := norm_def R
    have hfour : 4 * ((rem d x y).norm * y.norm) = (2 * R.re) ^ 2 - d * (2 * R.im) ^ 2 := by
      rw [← hRnorm, hRdef]; ring
    rw [hfour]
    nlinarith [hbre, hbim, hd.le, sq_nonneg (2 * R.im)]
  · -- degenerate case `N(y) = 0` (only when `y = 0`): both sides vanish
    rw [← h0]; simp

/-- **Uniform norm-Euclidean bound for `d ∈ {-1, -2}`.** When `-2 ≤ d < 0`, the
nearest-lattice-point remainder has strictly smaller norm. -/
theorem norm_rem_lt (hd : d < 0) (hd2 : -2 ≤ d) (x : ℤ√d) {y : ℤ√d} (hy : y ≠ 0) :
    (rem d x y).norm < y.norm := by
  have hpos : 0 < y.norm := by
    rcases lt_or_eq_of_le (norm_nonneg hd.le y) with h | h
    · exact h
    · exact absurd ((norm_eq_zero_iff hd y).mp h.symm) hy
  have hb := four_mul_norm_rem_le hd x y
  have hrn := norm_nonneg hd.le (rem d x y)
  nlinarith [hb, hpos, hrn, hd2, mul_pos hpos hpos]

/-- The Euclidean division statement: existence of a quotient and remainder with
strictly smaller norm. -/
theorem exists_quotient_remainder (hd : d < 0) (hd2 : -2 ≤ d) (x : ℤ√d) {y : ℤ√d}
    (hy : y ≠ 0) : ∃ q r : ℤ√d, x = y * q + r ∧ r.norm.natAbs < y.norm.natAbs := by
  refine ⟨quo d x y, rem d x y, (quotient_mul_add_remainder x y).symm, ?_⟩
  have h1 := norm_rem_lt hd hd2 x hy
  have h2 := norm_nonneg hd.le (rem d x y)
  have h3 := norm_nonneg hd.le y
  omega

/-! ### Packaging as a Euclidean domain -/

variable (d) in
/-- **`ℤ[√d]` is a Euclidean domain for every `-2 ≤ d < 0`**, with the *uniform*
nearest-lattice-point division and the norm `|N(·)|` as Euclidean size. Specialising
`d` to `-1` and `-2` recovers the Gaussian integers and `ℤ[√-2]` from a single proof. -/
noncomputable def euclideanDomain (hd : d < 0) (hd2 : -2 ≤ d) : EuclideanDomain (ℤ√d) :=
  { (inferInstance : CommRing (ℤ√d)), (inferInstance : Nontrivial (ℤ√d)) with
    quotient := quo d
    quotient_zero := quo_zero
    remainder := rem d
    quotient_mul_add_remainder_eq := fun a b => quotient_mul_add_remainder a b
    r := fun a b => a.norm.natAbs < b.norm.natAbs
    r_wellFounded := (measure fun z : ℤ√d => z.norm.natAbs).wf
    remainder_lt := fun a {b} hb => by
      have h1 := norm_rem_lt hd hd2 a hb
      have h2 := norm_nonneg hd.le (rem d a b)
      have h3 := norm_nonneg hd.le b
      omega
    mul_left_not_lt := fun a {b} hb => by
      intro hlt
      rw [norm_mul, Int.natAbs_mul] at hlt
      have hb' : b.norm ≠ 0 := fun h => hb ((norm_eq_zero_iff hd b).mp h)
      have hpos : 0 < b.norm.natAbs := by
        rw [Int.natAbs_pos]; exact hb'
      have hge : a.norm.natAbs ≤ a.norm.natAbs * b.norm.natAbs :=
        Nat.le_mul_of_pos_right _ hpos
      omega }

/-- The Gaussian integers `ℤ[i] = ℤ[√-1]` as the `d = -1` member of the family. -/
noncomputable def euclideanDomainNegOne : EuclideanDomain (ℤ√(-1)) :=
  euclideanDomain (-1) (by norm_num) (by norm_num)

/-- `ℤ[√-2]` as the `d = -2` member of the family. -/
noncomputable def euclideanDomainNegTwo : EuclideanDomain (ℤ√(-2)) :=
  euclideanDomain (-2) (by norm_num) (by norm_num)

/-! ### The obstruction at `d ≤ -3` -/

/-- **The uniform `Zsqrtd` argument provably stops at `d = -2`.** The
nearest-point factor `(1 − d)/4` reaches `1` exactly at `d = -3` and exceeds it
below, so the bound `N(r) < N(y)` is no longer forced. (Mathematically `ℤ[√d]` is
not the ring of integers for `d ≤ -3` squarefree, and `ℤ[√-3]` is not even a
Euclidean domain.) -/
theorem nearest_point_factor_ge_one_of_le_neg_three (hd : d ≤ -3) : 4 ≤ 1 - d := by
  omega

end NormEuclideanZsqrtdFamily
