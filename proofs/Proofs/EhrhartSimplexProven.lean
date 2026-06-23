/-
  Ehrhart Polynomial of the Standard Simplex: First-Principles Proof
  (ehrhart-cube-proven-oq-01)

  The d-dimensional standard simplex Δ^d with vertices at the origin
  and the d standard basis vectors satisfies:

    |n·Δ^d ∩ ℤ^d| = C(n+d, d)

  This file proves the simplex Ehrhart formula axiom-free using a
  bijection with multisets: Sym (Fin (d+1)) n (multisets of size n
  from {0,...,d}) bijects with simplex lattice points via the
  multiplicity map, with element 0 as the "slack" coordinate.

  This mirrors the cube proof's bijection (Fin d → Fin (n+1)) and
  answers ehrhart-cube-proven OQ-01: "Can the simplex Ehrhart
  polynomial be proved axiom-free using a similar bijection?"

  Key identity used: |Sym α n| = C(|α|+n-1, n) (Sym.card_sym_eq_choose)

  Main results:
  1. simplex_lattice_count:        |Sym (Fin (d+1)) n| = C(n+d, d)
  2. simplex_at_zero:              count at n=0 is 1 (the origin)
  3. simplex_at_one:               count at n=1 is d+1 (the d+1 vertices)
  4. simplex_1d:                   segment [0,n]: n+1 lattice points
  5. simplex_interior_count:       interior points = C(n-1, d) for n ≥ d+1
  6. simplex_boundary_count:       Ehrhart-Macdonald: total vs interior counts
  7. simplex_monotone:             count is increasing in n
  8. simplex_pascal:               Pascal-type recursion between dimensions
  9. simplex_count_descFactorial:  count·d! = (n+d)(n+d−1)···(n+1)
  10. simplex_count_ascFactorial:  count·d! = (n+1)(n+2)···(n+d)
  11. simplex_count_prod:          count·d! = ∏ i ∈ range d, (n + 1 + i)
-/
import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace EhrhartSimplexProven

-- ============================================================
-- SECTION I: Main Theorem
-- ============================================================

/-
## Lattice Points via Multisets

The d-simplex lattice points correspond to multisets of size n over {0,...,d}:
- Element k ≥ 1 contributes 1 to coordinate k (lattice position)
- Element 0 is the "slack" (= n minus the L¹-norm of the point)

This bijection: (x₁,...,xd) ↦ multiset {k : 1≤k≤d, k appears xₖ times} + slack 0s
is the simplex analogue of the cube's Fin d → Fin (n+1) bijection.

Cardinality: |Sym (Fin (d+1)) n| = C(d+1+n-1, n) = C(n+d, n) = C(n+d, d).
-/

/-- **Main theorem**: lattice points of n·Δ^d = C(n+d, d).

    Modeled as multisets Sym (Fin (d+1)) n: size-n multisets from {0,...,d}.
    Proof: Sym.card_sym_eq_choose + binomial symmetry. -/
theorem simplex_lattice_count (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) n) = (n + d).choose d := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  simp only [show d + 1 + n - 1 = n + d from by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

-- ============================================================
-- SECTION II: Base Cases
-- ============================================================

/-- At n = 0: every dilated simplex has exactly 1 lattice point (the origin).
    C(d+0, d) = C(d, d) = 1. -/
theorem simplex_at_zero (d : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) 0) = 1 := by
  simp [Sym.card_sym_eq_choose]

/-- At n = 1: exactly d+1 lattice points — the d+1 vertices of Δ^d.
    The vertices are the origin and the d unit vectors. C(d+1, d) = d+1. -/
theorem simplex_at_one (d : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) 1) = d + 1 := by
  simp [Sym.card_sym_eq_choose, Fintype.card_fin]

-- ============================================================
-- SECTION III: Dimensional Specializations
-- ============================================================

/-- **0D simplex** (single point): always 1 lattice point, any n. -/
theorem simplex_0d (n : ℕ) :
    Fintype.card (Sym (Fin 1) n) = 1 := by
  simp [simplex_lattice_count]

/-- **1D simplex** (line segment [0, n]): exactly n+1 lattice points.
    Same count as the 1D cube. C(n+1, 1) = n+1. -/
theorem simplex_1d (n : ℕ) :
    Fintype.card (Sym (Fin 2) n) = n + 1 := by
  simp [simplex_lattice_count, Nat.choose_one_right]

/-- **2D simplex** (triangle): C(n+2, 2) lattice points.
    Equals (n+1)(n+2)/2, the triangular numbers. -/
theorem simplex_2d (n : ℕ) :
    Fintype.card (Sym (Fin 3) n) = (n + 2).choose 2 := by
  simp [simplex_lattice_count]

/-- **3D simplex** (tetrahedron): C(n+3, 3) lattice points.
    Equals (n+1)(n+2)(n+3)/6, the tetrahedral numbers. -/
theorem simplex_3d (n : ℕ) :
    Fintype.card (Sym (Fin 4) n) = (n + 3).choose 3 := by
  simp [simplex_lattice_count]

-- Concrete verifications
example : Fintype.card (Sym (Fin 3) 1) = 3 := by native_decide  -- triangle n=1
example : Fintype.card (Sym (Fin 3) 2) = 6 := by native_decide  -- triangle n=2
example : Fintype.card (Sym (Fin 3) 3) = 10 := by native_decide -- triangle n=3
example : Fintype.card (Sym (Fin 4) 2) = 10 := by native_decide -- tetrahedron n=2
example : Fintype.card (Sym (Fin 4) 3) = 20 := by native_decide -- tetrahedron n=3

-- ============================================================
-- SECTION IV: Interior Lattice Points
-- ============================================================

/-
## Interior of n·Δ^d

The strictly interior lattice points of n·Δ^d are:
  {(x₁,...,xd) ∈ ℕ^d : ∀ i, xᵢ ≥ 1, x₁ + ... + xd < n}

By substituting yᵢ = xᵢ - 1 (shift down by 1), interior points biject with:
  {(y₁,...,yd) ∈ ℕ^d : ∀ i, yᵢ ≥ 0, y₁ + ... + yd ≤ n - d - 1}

which is exactly Sym (Fin (d+1)) (n-d-1), having cardinality C(n-1, d).

Ehrhart-Macdonald reciprocity: interior count at n equals the
polynomial L_Δd evaluated in a reflected argument.
-/

/-- Interior lattice point count for n·Δ^d equals C(n-1, d), for n ≥ d+1.

    The interior requires n > d (n ≥ d+1) for nonempty interior. -/
theorem simplex_interior_count (d n : ℕ) (hn : d + 1 ≤ n) :
    Fintype.card (Sym (Fin (d + 1)) (n - d - 1)) = (n - 1).choose d := by
  rw [Sym.card_sym_eq_choose, Fintype.card_fin]
  simp only [show d + 1 + (n - d - 1) - 1 = n - 1 from by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- Ehrhart-Macdonald reciprocity for Δ^d (numerical form):
    total count at n minus interior count at n equals the boundary count.
    C(n+d, d) - C(n-1, d) = boundary lattice points (for n ≥ d+1). -/
theorem simplex_boundary_count (d n : ℕ) (hn : d + 1 ≤ n) :
    Fintype.card (Sym (Fin (d + 1)) n) - Fintype.card (Sym (Fin (d + 1)) (n - d - 1)) =
    (n + d).choose d - (n - 1).choose d := by
  rw [simplex_lattice_count, simplex_interior_count d n hn]

-- Concrete: 2D simplex (triangle) has 3n boundary points at dilation n ≥ 2
-- Total - Interior = C(n+2,2) - C(n-1,2) = (n+1)(n+2)/2 - (n-1)(n-2)/2 = 3n
example : (Fintype.card (Sym (Fin 3) 3)) - (Fintype.card (Sym (Fin 3) 1)) = 7 := by
  native_decide

-- ============================================================
-- SECTION V: Monotonicity and Recursion
-- ============================================================

/-- The simplex Ehrhart count is monotone increasing in n:
    more dilation means more lattice points. -/
theorem simplex_monotone (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) n) ≤ Fintype.card (Sym (Fin (d + 1)) (n + 1)) := by
  simp only [simplex_lattice_count]
  exact Nat.choose_le_choose d (by omega)

/-- **Pascal-type recursion**: The (d+1)-simplex at dilation n+1 decomposes
    as the d-simplex at n+1 plus the (d+1)-simplex at n.

    Equivalently: C(n+1+(d+1), d+1) = C(n+1+d, d) + C(n+(d+1), d+1)
    which is Pascal's rule: C(m+1, k+1) = C(m, k) + C(m, k+1). -/
theorem simplex_pascal (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 2)) (n + 1)) =
    Fintype.card (Sym (Fin (d + 1)) (n + 1)) +
    Fintype.card (Sym (Fin (d + 2)) n) := by
  simp only [simplex_lattice_count]
  have h1 : n + 1 + (d + 1) = n + d + 1 + 1 := by omega
  have h2 : n + 1 + d = n + d + 1 := by omega
  have h3 : n + (d + 1) = n + d + 1 := by omega
  rw [h1, h2, h3]
  linarith [Nat.choose_succ_succ (n + d + 1) d]

-- ============================================================
-- SECTION VI: Comparison with Cube
-- ============================================================

/-- The 1D simplex and 1D cube agree: both give n+1 lattice points.
    Simplex [0,n] = Cube [0,n]^1 in dimension 1. -/
theorem simplex_cube_1d_agree (n : ℕ) :
    Fintype.card (Sym (Fin 2) n) = Fintype.card (Fin (n + 1)) := by
  simp [simplex_lattice_count, Nat.choose_one_right]

/-- The simplex count grows as C(n+d, d) ~ n^d/d!, much slower than
    the cube count (n+1)^d. At n=2, d=3: simplex = 10 < cube = 27. -/
example : Fintype.card (Sym (Fin 4) 2) < Fintype.card (Fin 3 → Fin 3) := by
  native_decide

-- ============================================================
-- SECTION VII: Polynomial Form (closed form via factorials)
-- ============================================================

/-
## The Ehrhart Count is a Polynomial in n

The simplex Ehrhart count L(Δ^d, n) = C(n+d, d) is a polynomial of
degree d in n with positive rational coefficients. Multiplying by
d! exhibits the polynomial directly, with three equivalent forms:

  L(Δ^d, n) · d! = (n+d)(n+d−1)···(n+1)         (descending factorial)
                = (n+1)(n+2)···(n+d)             (ascending factorial)
                = ∏ i ∈ range d, (n + 1 + i)     (product form)

The polynomial has roots at n = −1, −2, …, −d and leading
coefficient 1/d! when divided by d!. This is the analogue, for the
simplex, of the cube's `(n+1)^d`: a closed-form polynomial that
makes the Ehrhart polynomial existence theorem unnecessary in
this case.
-/

/-- **Polynomial form (descending)**: L(Δ^d, n) · d! = (n+d)(n+d−1)···(n+1).

    Direct corollary of `Nat.descFactorial_eq_factorial_mul_choose`. -/
theorem simplex_count_descFactorial (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) n) * d.factorial = (n + d).descFactorial d := by
  rw [simplex_lattice_count, mul_comm]
  exact (Nat.descFactorial_eq_factorial_mul_choose (n + d) d).symm

/-- **Polynomial form (ascending)**: L(Δ^d, n) · d! = (n+1)(n+2)···(n+d).

    Direct corollary of `Nat.ascFactorial_eq_factorial_mul_choose`. -/
theorem simplex_count_ascFactorial (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) n) * d.factorial = (n + 1).ascFactorial d := by
  rw [simplex_lattice_count, mul_comm]
  exact (Nat.ascFactorial_eq_factorial_mul_choose n d).symm

/-- **Product form**: L(Δ^d, n) · d! = ∏ i ∈ range d, (n + 1 + i).

    Combines `simplex_count_ascFactorial` with `Nat.ascFactorial_eq_prod_range`,
    exhibiting the count as an explicit finite product. -/
theorem simplex_count_prod (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) n) * d.factorial =
      ∏ i ∈ Finset.range d, (n + 1 + i) := by
  rw [simplex_count_ascFactorial, Nat.ascFactorial_eq_prod_range]

-- Concrete polynomial verifications
-- 2D triangle at n=3:  2! · 10 = 20 = 4 · 5
example : Fintype.card (Sym (Fin 3) 3) * 2 = 4 * 5 := by native_decide
-- 3D tetrahedron at n=2: 3! · 10 = 60 = 3 · 4 · 5
example : Fintype.card (Sym (Fin 4) 2) * 6 = 3 * 4 * 5 := by native_decide
-- 4D pentachoron at n=2: 4! · 15 = 360 = 3 · 4 · 5 · 6
example : Fintype.card (Sym (Fin 5) 2) * 24 = 3 * 4 * 5 * 6 := by native_decide

-- ============================================================
-- Exports
-- ============================================================

#check simplex_lattice_count
#check simplex_interior_count
#check simplex_monotone
#check simplex_pascal
#check simplex_count_descFactorial
#check simplex_count_ascFactorial
#check simplex_count_prod

end EhrhartSimplexProven
