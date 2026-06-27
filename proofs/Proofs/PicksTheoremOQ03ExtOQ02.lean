/-
# Pick's Theorem OQ-03 Extension, follow-up OQ-02
# Abstract Characterization of h*-Vector Palindromy (Hibi's Criterion)

The parent entry (`PicksTheoremOQ03Ext.lean`) verifies h*-vector palindromy for
**specific** reflexive polytopes — the octahedron `(1,3,3,1)`, the cube,
the simplex — and the Ehrhart–Macdonald reciprocity identities on concrete
examples.  This follow-up proves the **general algebraic characterization** that
those examples instantiate, the combinatorial heart of Hibi's palindromy theorem
(1991):

  > The h*-vector `(h₀,…,h_d)` of a lattice polytope is *palindromic*
  >   (`h_i = h_{d-i}` for all `i ≤ d`)
  > **iff** its h*-polynomial `H(X) = Σ h_i Xⁱ` is *self-reciprocal*, i.e. equal
  >   to its own degree-`d` reflection `reflect d H = H`.

This is `reflect_eq_iff_palindromic`.  It is a clean, fully general fact about
polynomials over an arbitrary commutative semiring — no Ehrhart machinery, no
case analysis on a fixed dimension.

The link to geometry is `reflexive_hStar_palindromic`: for a reflexive
`d`-polytope, Ehrhart–Macdonald reciprocity (`L°(n) = (-1)^d L(-n)` together with
`L°(n) = L(n-1)`) forces precisely the self-reciprocity of the h*-polynomial, and
palindromy then follows from the general characterization.  We record this bridge
taking the self-reciprocity (the reciprocity content) as an explicit hypothesis on
the input — honest about what is assumed, since the generating-function machinery
producing it is not yet available in Mathlib.

Finally we recover the parent's octahedron example as a corollary of the general
theorem, confirming the abstraction is faithful, and derive the standard
"reflexive normalization" `h₀ = h_d`.

## Results (0 sorries, 0 axioms — fully proved)
Pure polynomial algebra; the main theorem holds over any commutative semiring.
-/

import Mathlib

namespace PicksOQ03ExtOQ02

open Polynomial Finset

variable {R : Type*} [Semiring R]

/-- The **h*-polynomial** of an h*-vector `h` supported on `{0,…,d}`:
    `H(X) = Σ_{i=0}^{d} h_i Xⁱ`. -/
noncomputable def hStarPoly (d : ℕ) (h : ℕ → R) : R[X] :=
  ∑ i ∈ range (d + 1), C (h i) * X ^ i

/-- A vector is **palindromic** through index `d` when `h_i = h_{d-i}` for `i ≤ d`. -/
def Palindromic (d : ℕ) (h : ℕ → R) : Prop := ∀ i ≤ d, h i = h (d - i)

/-- The coefficients of the h*-polynomial are exactly the entries of `h` up to `d`. -/
@[simp] theorem coeff_hStarPoly (d : ℕ) (h : ℕ → R) (k : ℕ) :
    (hStarPoly d h).coeff k = if k ≤ d then h k else 0 := by
  simp only [hStarPoly, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq (range (d + 1)) k (fun i => h i)]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- **Main theorem (Hibi's criterion, algebraic core).**
The h*-vector `h` is palindromic through `d` iff its h*-polynomial is
self-reciprocal, `reflect d (hStarPoly d h) = hStarPoly d h`. -/
theorem reflect_eq_iff_palindromic (d : ℕ) (h : ℕ → R) :
    reflect d (hStarPoly d h) = hStarPoly d h ↔ Palindromic d h := by
  constructor
  · intro hH i hi
    have hk := Polynomial.ext_iff.mp hH i
    rw [coeff_reflect, revAt_le hi, coeff_hStarPoly, coeff_hStarPoly,
      if_pos (Nat.sub_le d i), if_pos hi] at hk
    exact hk.symm
  · intro hp
    ext k
    rw [coeff_reflect, coeff_hStarPoly, coeff_hStarPoly]
    rcases le_or_lt k d with hk | hk
    · rw [revAt_le hk, if_pos (Nat.sub_le d k), if_pos hk]
      exact (hp k hk).symm
    · rw [revAt_eq_self_of_lt hk]

/-- **Reflexive ⟹ palindromic h*-vector** (the reduction step in Hibi's theorem).
For a reflexive `d`-polytope, Ehrhart–Macdonald reciprocity forces the
h*-polynomial to be self-reciprocal; palindromy of the h*-vector is then immediate
from `reflect_eq_iff_palindromic`.  The self-reciprocity is taken as a hypothesis
on the input (its derivation from the Ehrhart series is the reciprocity content). -/
theorem reflexive_hStar_palindromic (d : ℕ) (h : ℕ → R)
    (hreflexive : reflect d (hStarPoly d h) = hStarPoly d h) :
    Palindromic d h :=
  (reflect_eq_iff_palindromic d h).mp hreflexive

/-- **Reflexive normalization.** A palindromic h*-vector has matching extreme
entries `h₀ = h_d`; for a lattice polytope `h₀ = 1`, so a reflexive polytope has
`h_d = 1` (the Gorenstein/reflexive normalization). -/
theorem hStar_constant_eq_leading (d : ℕ) (h : ℕ → R) (hp : Palindromic d h) :
    h 0 = h d := by
  have := hp 0 (Nat.zero_le d)
  simpa using this

-- ============================================================
-- Recovering the parent's octahedron example from the general theorem
-- ============================================================

/-- The octahedron (3D cross-polytope) h*-vector `(1, 3, 3, 1)` as a function. -/
def octaH : ℕ → ℚ := fun i => if i = 0 then 1 else if i = 1 then 3 else
  if i = 2 then 3 else if i = 3 then 1 else 0

/-- The octahedron h*-vector is palindromic — an instance of the general criterion. -/
theorem octaH_palindromic : Palindromic 3 octaH := by
  intro i hi
  interval_cases i <;> simp [octaH]

/-- Equivalently, the octahedron h*-polynomial is self-reciprocal — obtained from
palindromy through the general equivalence, demonstrating the bridge is faithful. -/
theorem octaH_self_reciprocal :
    reflect 3 (hStarPoly 3 octaH) = hStarPoly 3 octaH :=
  (reflect_eq_iff_palindromic 3 octaH).mpr octaH_palindromic

/-- Consistency check: the octahedron satisfies the reflexive normalization. -/
theorem octaH_normalization : octaH 0 = octaH 3 :=
  hStar_constant_eq_leading 3 octaH octaH_palindromic

end PicksOQ03ExtOQ02
