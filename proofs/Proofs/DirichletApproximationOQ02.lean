/-
  Simultaneous Dirichlet Approximation Theorem  (Open Question OQ-02)

  Parent: `DirichletApproximation.lean` proves the classical one-dimensional
  statement: for any real α and integer Q ≥ 1 there exist integers p, q with
  1 ≤ q ≤ Q and |qα - p| < 1/Q.

  This file formalizes the **simultaneous** (k-dimensional) generalization:
  given reals α₁, …, α_k (packaged as α : Fin k → ℝ) and N ≥ 1, there is a
  single common denominator q with 1 ≤ q ≤ Nᵏ and integers p₁, …, p_k such that

        |q·α_i - p_i| < 1/N      for every coordinate i,

  equivalently  |α_i - p_i/q| < 1/(qN).

  The proof is the same pigeonhole argument lifted from the unit interval [0,1)
  to the unit cube [0,1)ᵏ:  consider the Nᵏ + 1 points
  (frac(j·α₁), …, frac(j·α_k))  for j = 0, …, Nᵏ inside the cube, partitioned
  into Nᵏ subcubes (N equal pieces per coordinate).  By pigeonhole two of the
  points share a subcube; their difference yields the common denominator q and
  the simultaneous bound, coordinate by coordinate.

  This makes the gallery's Dirichlet entry the base case (k = 1) of a reusable
  higher-dimensional result — the foundation of the geometry of numbers and
  Diophantine approximation in several variables.
-/
import Mathlib

namespace DirichletApproximationOQ02

open Int Finset

/-- Floor of two values agree implies the values differ by less than 1. -/
private lemma sub_lt_one_of_floor_eq {x y : ℝ} (_hxy : x ≥ y)
    (hfl : ⌊x⌋ = ⌊y⌋) : x - y < 1 := by
  have h1 : x < ↑⌊x⌋ + 1 := Int.lt_floor_add_one x
  have h2 : (↑⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  rw [hfl] at h1; linarith

/-- If two values in [0, N) have the same floor, they differ by less than 1. -/
private lemma interval_bound {x y : ℝ} {N : ℕ} (_hN : 0 < N)
    (_hx : 0 ≤ x) (_hx' : x < N) (_hy : 0 ≤ y) (_hy' : y < N)
    (hfl : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rcases le_or_gt x y with hxy | hxy
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    exact sub_lt_one_of_floor_eq hxy hfl.symm
  · rw [abs_of_pos (sub_pos.mpr hxy)]
    exact sub_lt_one_of_floor_eq hxy.le hfl

/-- Fractional part function: frac(x) = x - ⌊x⌋ -/
private noncomputable def frac (x : ℝ) : ℝ := x - ↑⌊x⌋

private lemma frac_nonneg (x : ℝ) : 0 ≤ frac x :=
  sub_nonneg.mpr (Int.floor_le x)

private lemma frac_lt_one (x : ℝ) : frac x < 1 := by
  unfold frac; linarith [Int.lt_floor_add_one x]

private lemma frac_eq (x : ℝ) : frac x = x - ↑⌊x⌋ := rfl

/-- The coordinatewise interval map sending an index j to the function
    l ↦ ⌊N · frac(j·α_l)⌋, assigning each of the Nᵏ + 1 lattice points to
    one of the Nᵏ subcubes of [0,1)ᵏ. -/
private noncomputable def intervalMapMulti {k : ℕ} (α : Fin k → ℝ) (N : ℕ)
    (hN : 0 < N) : Fin (N ^ k + 1) → (Fin k → Fin N) := fun j l =>
  ⟨Int.toNat ⌊↑N * frac (↑(j : ℕ) * α l)⌋, by
    have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
    have hfrac_nn : 0 ≤ frac (↑(j : ℕ) * α l) := frac_nonneg _
    have hprod_nn : 0 ≤ ↑N * frac (↑(j : ℕ) * α l) :=
      mul_nonneg (le_of_lt hN_pos) hfrac_nn
    have hprod_lt : ↑N * frac (↑(j : ℕ) * α l) < ↑N := by
      calc ↑N * frac (↑(j : ℕ) * α l) < ↑N * 1 :=
            mul_lt_mul_of_pos_left (frac_lt_one _) hN_pos
        _ = ↑N := mul_one _
    rw [Int.toNat_lt (Int.floor_nonneg.mpr hprod_nn)]
    exact_mod_cast Int.floor_lt.mpr hprod_lt⟩

/-- Core step: given two distinct lattice indices in the same subcube with the
    smaller one `j` strictly below `i`, build the common denominator and the
    simultaneous approximation. -/
private lemma simultaneous_aux {k : ℕ} (α : Fin k → ℝ) (N : ℕ) (hN : 0 < N)
    (i j : Fin (N ^ k + 1)) (hlt : (j : ℕ) < (i : ℕ))
    (hfij : intervalMapMulti α N hN i = intervalMapMulti α N hN j) :
    ∃ (p : Fin k → ℤ) (q : ℕ),
      1 ≤ q ∧ q ≤ N ^ k ∧ ∀ l, |↑q * α l - ↑(p l)| < 1 / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  set q := (i : ℕ) - (j : ℕ) with hq_def
  have hq_pos : 1 ≤ q := by omega
  have hq_le : q ≤ N ^ k := by
    have hi := i.isLt; have hj := j.isLt; omega
  refine ⟨fun l => ⌊(↑(i : ℕ) : ℝ) * α l⌋ - ⌊(↑(j : ℕ) : ℝ) * α l⌋, q,
    hq_pos, hq_le, ?_⟩
  intro l
  show |(↑q : ℝ) * α l - ↑(⌊(↑(i : ℕ) : ℝ) * α l⌋ - ⌊(↑(j : ℕ) : ℝ) * α l⌋)|
      < 1 / (N : ℝ)
  -- Key identity: q·α_l - (⌊i·α_l⌋ - ⌊j·α_l⌋) = frac(i·α_l) - frac(j·α_l)
  have hkey : (↑q : ℝ) * α l - ↑(⌊(↑(i : ℕ) : ℝ) * α l⌋ - ⌊(↑(j : ℕ) : ℝ) * α l⌋)
      = frac (↑(i : ℕ) * α l) - frac (↑(j : ℕ) * α l) := by
    simp only [frac_eq]
    rw [hq_def, Nat.cast_sub (le_of_lt hlt)]
    push_cast
    ring
  rw [hkey]
  -- Floor equality at coordinate l, extracted from the subcube collision.
  have hfl : ⌊↑N * frac (↑(i : ℕ) * α l)⌋ = ⌊↑N * frac (↑(j : ℕ) * α l)⌋ := by
    have hval := congr_arg (fun x : Fin N => (x : ℕ)) (congr_fun hfij l)
    simp only [intervalMapMulti] at hval
    have hi_nn : 0 ≤ ⌊↑N * frac (↑(i : ℕ) * α l)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hN_pos) (frac_nonneg _))
    have hj_nn : 0 ≤ ⌊↑N * frac (↑(j : ℕ) * α l)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg (le_of_lt hN_pos) (frac_nonneg _))
    have hi_cast : (⌊↑N * frac (↑(i : ℕ) * α l)⌋.toNat : ℤ)
        = ⌊↑N * frac (↑(i : ℕ) * α l)⌋ := Int.toNat_of_nonneg hi_nn
    have hj_cast : (⌊↑N * frac (↑(j : ℕ) * α l)⌋.toNat : ℤ)
        = ⌊↑N * frac (↑(j : ℕ) * α l)⌋ := Int.toNat_of_nonneg hj_nn
    linarith [show (⌊↑N * frac (↑(i : ℕ) * α l)⌋.toNat : ℤ) =
      (⌊↑N * frac (↑(j : ℕ) * α l)⌋.toNat : ℤ) from by exact_mod_cast hval]
  -- From the floor equality and both products in [0, N): difference < 1/N.
  have hi_prod_nn : 0 ≤ ↑N * frac (↑(i : ℕ) * α l) :=
    mul_nonneg (le_of_lt hN_pos) (frac_nonneg _)
  have hi_prod_lt : ↑N * frac (↑(i : ℕ) * α l) < ↑N :=
    (mul_lt_iff_lt_one_right hN_pos).mpr (frac_lt_one _)
  have hj_prod_nn : 0 ≤ ↑N * frac (↑(j : ℕ) * α l) :=
    mul_nonneg (le_of_lt hN_pos) (frac_nonneg _)
  have hj_prod_lt : ↑N * frac (↑(j : ℕ) * α l) < ↑N :=
    (mul_lt_iff_lt_one_right hN_pos).mpr (frac_lt_one _)
  have habs_prod : |↑N * frac (↑(i : ℕ) * α l) - ↑N * frac (↑(j : ℕ) * α l)| < 1 :=
    interval_bound hN hi_prod_nn hi_prod_lt hj_prod_nn hj_prod_lt hfl
  rw [show ↑N * frac (↑(i : ℕ) * α l) - ↑N * frac (↑(j : ℕ) * α l) =
      ↑N * (frac (↑(i : ℕ) * α l) - frac (↑(j : ℕ) * α l)) from by ring] at habs_prod
  rw [abs_mul, abs_of_pos hN_pos] at habs_prod
  rw [lt_div_iff₀ hN_pos]; linarith

/-- **Simultaneous Dirichlet Approximation Theorem.**
    For reals α : Fin k → ℝ and N ≥ 1 there is a common denominator q with
    1 ≤ q ≤ Nᵏ and integers p l such that |q·α l - p l| < 1/N for every l.

    Specializing to k = 1 recovers the classical one-dimensional theorem
    (with Q = N). -/
theorem dirichlet_simultaneous {k : ℕ} (α : Fin k → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ (p : Fin k → ℤ) (q : ℕ),
      1 ≤ q ∧ q ≤ N ^ k ∧ ∀ l, |↑q * α l - ↑(p l)| < 1 / (N : ℝ) := by
  -- Pigeonhole: Nᵏ + 1 lattice points, only Nᵏ subcubes.
  have hcard : Fintype.card (Fin k → Fin N) < Fintype.card (Fin (N ^ k + 1)) := by
    have hpow : Fintype.card (Fin k → Fin N) = N ^ k := by
      simp [Fintype.card_pi, Fintype.card_fin]
    rw [hpow, Fintype.card_fin]; omega
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (intervalMapMulti α N hN) hcard
  have hval_ne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval_ne with h | h
  · exact simultaneous_aux α N hN j i h hfij.symm
  · exact simultaneous_aux α N hN i j h hfij

/-- Quotient form matching the classical statement:
    |α l - p l / q| < 1/(qN) simultaneously for all coordinates l. -/
theorem dirichlet_simultaneous_div {k : ℕ} (α : Fin k → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ (p : Fin k → ℤ) (q : ℕ), 1 ≤ q ∧ q ≤ N ^ k ∧
      ∀ l, |α l - ↑(p l) / ↑q| < 1 / (↑q * ↑N) := by
  obtain ⟨p, q, hq1, hqN, hb⟩ := dirichlet_simultaneous α N hN
  have hq_pos : (0 : ℝ) < ↑q := by exact_mod_cast hq1
  have hq_ne : (↑q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  refine ⟨p, q, hq1, hqN, fun l => ?_⟩
  have hb' := hb l
  have heq : α l - ↑(p l) / ↑q = (↑q * α l - ↑(p l)) / ↑q := by
    field_simp
  rw [heq, abs_div, abs_of_pos hq_pos, div_lt_iff₀ hq_pos]
  have hrw : 1 / (↑q * ↑N) * ↑q = 1 / (↑N : ℝ) := by field_simp; ring
  rw [hrw]; exact hb'

end DirichletApproximationOQ02
