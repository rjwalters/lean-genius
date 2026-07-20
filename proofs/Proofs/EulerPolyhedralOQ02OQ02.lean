/-
  Chern-Gauss-Bonnet in Higher Dimensions (OQ-02-OQ-02)

  This file connects the discrete Gauss-Bonnet theorem (OQ-02) and the smooth
  2-dimensional Gauss-Bonnet theorem (OQ-02-OQ-01) to their full higher-dimensional
  generalization, the **Chern-Gauss-Bonnet theorem**:

    ∫_M Pf(Ω) = (2π)^n · χ(M)        (M closed oriented, dim M = 2n)

  equivalently, in normalized form,

    ∫_M Pf(Ω / 2π) = χ(M).

  Here Ω is the curvature 2-form of a Riemannian metric, Pf is the Pfaffian of the
  (antisymmetric) curvature matrix, and χ(M) is the Euler characteristic. The theorem
  was proved by Chern (1944-45) using characteristic classes; for n = 1 the Pfaffian
  of the 2×2 curvature is the Gaussian curvature times the area form and the formula
  reduces to the classical Gauss-Bonnet ∫_M K dA = 2π·χ(M).

  ## Why this is axiomatized

  Mathlib (v4.26.0) has neither the Pfaffian of a curvature form, nor integration of
  characteristic forms over manifolds, nor a manifold Euler characteristic. We therefore
  encode the Chern-Gauss-Bonnet identity as a field of a `CGBManifold` structure
  (a structure-encoded assumption, hence `axiomatized`), and prove the substantive
  consequences that follow purely algebraically:

  1. Euler characteristic of spheres S^m = 1 + (-1)^m  (verified, 0-axiom).
  2. The normalization constant (2π)^n: positivity and multiplicativity (verified).
  3. The 2×2 Pfaffian/determinant identity Pf² = det underlying the n = 1 reduction.
  4. Dimension is even; the normalized integral equals χ; χ = 0 ⇒ ∫ Pf = 0.
  5. Recovery of the 2-dimensional Gauss-Bonnet ∫ Pf(Ω) = 2π·χ at n = 1.
  6. Functorial constructions: spheres S^{2n}, products M × N (χ multiplies), tori.

  ## References
  - Chern (1944): A simple intrinsic proof of the Gauss-Bonnet formula for closed
    Riemannian manifolds. Ann. of Math. 45, 747-752.
  - Chern (1945): On the curvatura integra in a Riemannian manifold. Ann. of Math. 46.
  - Allendoerfer-Weil (1943): The Gauss-Bonnet theorem for Riemannian polyhedra.
  - Spivak, A Comprehensive Introduction to Differential Geometry, Vol. V.
-/

import Mathlib

open Real

set_option linter.unusedVariables false

noncomputable section

namespace ChernGaussBonnet

-- ============================================================================
-- Part I: Euler characteristics of spheres (verified, 0-axiom)
-- ============================================================================

/-- Euler characteristic of the m-sphere: χ(S^m) = 1 + (-1)^m.
    This is 2 in even dimension and 0 in odd dimension — exactly the parity that
    makes the Pfaffian (an even-dimensional object) the right curvature integrand. -/
def sphereEulerChar (m : ℕ) : ℤ := 1 + (-1) ^ m

/-- Even-dimensional spheres S^{2n} have Euler characteristic 2. -/
theorem sphereEulerChar_even (n : ℕ) : sphereEulerChar (2 * n) = 2 := by
  unfold sphereEulerChar
  rw [pow_mul]
  norm_num

/-- Odd-dimensional spheres S^{2n+1} have Euler characteristic 0. -/
theorem sphereEulerChar_odd (n : ℕ) : sphereEulerChar (2 * n + 1) = 0 := by
  unfold sphereEulerChar
  rw [pow_succ, pow_mul]
  norm_num

/-- χ(S^0) = 2 (two points). -/
theorem sphereEulerChar_zero : sphereEulerChar 0 = 2 := by decide

/-- χ(S^1) = 0 (the circle). -/
theorem sphereEulerChar_one : sphereEulerChar 1 = 0 := by decide

/-- χ(S^2) = 2 (the ordinary 2-sphere, base case of classical Gauss-Bonnet). -/
theorem sphereEulerChar_two : sphereEulerChar 2 = 2 := by decide

/-- χ(S^4) = 2 (first genuinely higher-dimensional Chern-Gauss-Bonnet case). -/
theorem sphereEulerChar_four : sphereEulerChar 4 = 2 := by decide

/-- The even/odd dichotomy in one statement: χ(S^m) is 2 when m is even, 0 when odd. -/
theorem sphereEulerChar_eq_ite (m : ℕ) :
    sphereEulerChar m = if Even m then 2 else 0 := by
  unfold sphereEulerChar
  rcases Nat.even_or_odd m with he | ho
  · rw [if_pos he, he.neg_one_pow]; norm_num
  · rw [if_neg (by simpa using ho), ho.neg_one_pow]; ring

-- ============================================================================
-- Part II: The Chern normalization constant (2π)^n (verified, 0-axiom)
-- ============================================================================

/-- The Chern-Gauss-Bonnet normalization constant for a 2n-dimensional manifold:
    (2π)^n. It converts the unnormalized Pfaffian integral ∫ Pf(Ω) into χ(M). -/
def cgbConst (n : ℕ) : ℝ := (2 * π) ^ n

/-- The normalization constant is strictly positive (so dividing by it is safe). -/
theorem cgbConst_pos (n : ℕ) : 0 < cgbConst n := by
  unfold cgbConst; positivity

/-- The normalization constant is nonzero. -/
theorem cgbConst_ne_zero (n : ℕ) : cgbConst n ≠ 0 := (cgbConst_pos n).ne'

/-- For a 0-dimensional manifold (a finite set of points) the constant is 1. -/
theorem cgbConst_zero : cgbConst 0 = 1 := by simp [cgbConst]

/-- For a surface (dim 2, n = 1) the constant is 2π — the classical Gauss-Bonnet factor. -/
theorem cgbConst_one : cgbConst 1 = 2 * π := by simp [cgbConst]

/-- Multiplicativity: (2π)^{m+n} = (2π)^m · (2π)^n. This is what makes the
    Chern-Gauss-Bonnet integral multiplicative under products of manifolds. -/
theorem cgbConst_add (m n : ℕ) : cgbConst (m + n) = cgbConst m * cgbConst n := by
  unfold cgbConst; rw [pow_add]

-- ============================================================================
-- Part III: The 2×2 Pfaffian and Pf² = det (verified, 0-axiom)
-- ============================================================================

/-
  In dimension 2 (n = 1) the curvature is encoded by a single antisymmetric matrix
  [[0, a], [-a, 0]] whose Pfaffian is `a`. Its determinant is a², so Pf² = det — the
  algebraic identity behind "Pf(Ω) reduces to the Gaussian curvature 2-form" when n = 1.
-/

/-- Pfaffian of the 2×2 antisymmetric matrix [[0, a], [-a, 0]]. -/
def pf2 (a : ℝ) : ℝ := a

/-- Determinant of the 2×2 antisymmetric matrix [[0, a], [-a, 0]] = a². -/
def det2 (a : ℝ) : ℝ := 0 * 0 - a * (-a)

/-- The Pfaffian-determinant identity in dimension 2: Pf² = det. -/
theorem pf2_sq_eq_det2 (a : ℝ) : (pf2 a) ^ 2 = det2 a := by
  unfold pf2 det2; ring

/-- The 2×2 determinant evaluates to a². -/
theorem det2_eq (a : ℝ) : det2 a = a ^ 2 := by unfold det2; ring

/-- Hence the Pfaffian of the 2×2 antisymmetric matrix is its (1,2)-entry. -/
theorem pf2_eq (a : ℝ) : pf2 a = a := rfl

-- ============================================================================
-- Part IV: The Chern-Gauss-Bonnet manifold (structure-encoded assumption)
-- ============================================================================

/-- A closed oriented Riemannian manifold of even dimension 2·`halfDim`, carrying its
    Euler characteristic `chi` and total Pfaffian curvature `totalPfaffian` = ∫_M Pf(Ω),
    subject to the Chern-Gauss-Bonnet identity.

    The field `chern_gauss_bonnet` is the mathematical assumption (Mathlib lacks the
    machinery to derive it), which is why entries built from this structure are
    `axiomatized` rather than `verified`. -/
structure CGBManifold where
  /-- Half the (even) dimension: dim M = 2 · halfDim. -/
  halfDim : ℕ
  /-- Euler characteristic χ(M) ∈ ℤ. -/
  chi : ℤ
  /-- Total Pfaffian curvature ∫_M Pf(Ω) ∈ ℝ. -/
  totalPfaffian : ℝ
  /-- **Chern-Gauss-Bonnet**: ∫_M Pf(Ω) = (2π)^n · χ(M), where n = halfDim. -/
  chern_gauss_bonnet : totalPfaffian = cgbConst halfDim * chi

namespace CGBManifold

/-- The (full) dimension of the manifold: 2 · halfDim. -/
def dim (M : CGBManifold) : ℕ := 2 * M.halfDim

/-- The dimension of a Chern-Gauss-Bonnet manifold is even — the Pfaffian, and hence
    the whole theorem, only makes sense in even dimensions. -/
theorem dim_even (M : CGBManifold) : Even M.dim := ⟨M.halfDim, by unfold dim; ring⟩

/-- **Normalized Chern-Gauss-Bonnet**: ∫_M Pf(Ω / 2π) = χ(M). Dividing the total
    Pfaffian by (2π)^n recovers the (integer) Euler characteristic exactly. -/
theorem normalized (M : CGBManifold) :
    M.totalPfaffian / cgbConst M.halfDim = M.chi := by
  rw [M.chern_gauss_bonnet, mul_comm, mul_div_assoc, div_self (cgbConst_ne_zero _), mul_one]

/-- The total Pfaffian is an exact integer multiple of the normalization constant. -/
theorem totalPfaffian_eq (M : CGBManifold) :
    M.totalPfaffian = cgbConst M.halfDim * M.chi := M.chern_gauss_bonnet

/-- If the Euler characteristic vanishes then so does the total Pfaffian curvature.
    (In particular this holds for all odd-dimensional closed manifolds and for even tori.) -/
theorem totalPfaffian_eq_zero_of_chi_zero (M : CGBManifold) (h : M.chi = 0) :
    M.totalPfaffian = 0 := by
  rw [M.chern_gauss_bonnet, h]; simp

/-- Conversely, a nonzero total Pfaffian forces a nonzero Euler characteristic. -/
theorem chi_ne_zero_of_totalPfaffian_ne_zero (M : CGBManifold)
    (h : M.totalPfaffian ≠ 0) : M.chi ≠ 0 := by
  intro hchi; exact h (M.totalPfaffian_eq_zero_of_chi_zero hchi)

/-- The sign of the total Pfaffian matches the sign of the Euler characteristic
    (since the normalization constant is positive). -/
theorem totalPfaffian_pos_iff (M : CGBManifold) :
    0 < M.totalPfaffian ↔ 0 < M.chi := by
  rw [M.chern_gauss_bonnet]
  constructor
  · intro h
    have := (mul_pos_iff_of_pos_left (cgbConst_pos M.halfDim)).mp h
    exact_mod_cast this
  · intro h
    have : (0 : ℝ) < (M.chi : ℝ) := by exact_mod_cast h
    exact mul_pos (cgbConst_pos M.halfDim) this

end CGBManifold

-- ============================================================================
-- Part V: Recovery of the 2-dimensional Gauss-Bonnet theorem (n = 1)
-- ============================================================================

/-- **Reduction to classical Gauss-Bonnet.** For a 2-dimensional (halfDim = 1)
    Chern-Gauss-Bonnet manifold the identity becomes ∫_M Pf(Ω) = 2π·χ(M). Combined
    with the 2×2 reduction Pf(Ω) = K · (area form) this is exactly the smooth
    Gauss-Bonnet theorem ∫_M K dA = 2π·χ(M) of entry OQ-02-OQ-01, and the discrete
    Σ_v δ(v) = 2π·χ of entry OQ-02. -/
theorem two_dim_gauss_bonnet (M : CGBManifold) (h : M.halfDim = 1) :
    M.totalPfaffian = 2 * π * M.chi := by
  rw [M.chern_gauss_bonnet, h, cgbConst_one]

/-- A 0-dimensional manifold (finite point set) has ∫ Pf = χ: the Chern-Gauss-Bonnet
    integrand is the counting measure and χ is the number of points. -/
theorem zero_dim_counts_points (M : CGBManifold) (h : M.halfDim = 0) :
    M.totalPfaffian = M.chi := by
  rw [M.chern_gauss_bonnet, h, cgbConst_zero, one_mul]

-- ============================================================================
-- Part VI: Sphere manifolds S^{2n}
-- ============================================================================

/-- The even-dimensional sphere S^{2n} as a Chern-Gauss-Bonnet manifold: χ = 2 and
    ∫ Pf(Ω) = 2·(2π)^n. -/
def sphereCGB (n : ℕ) : CGBManifold where
  halfDim := n
  chi := 2
  totalPfaffian := 2 * cgbConst n
  chern_gauss_bonnet := by push_cast; ring

/-- S^{2n} has the dimension we expect: 2n. -/
theorem sphereCGB_dim (n : ℕ) : (sphereCGB n).dim = 2 * n := rfl

/-- The Euler characteristic field of `sphereCGB n` agrees with the combinatorial
    value χ(S^{2n}) = 1 + (-1)^{2n} = 2 from Part I. -/
theorem sphereCGB_chi_eq (n : ℕ) : (sphereCGB n).chi = sphereEulerChar (2 * n) := by
  rw [sphereEulerChar_even]; rfl

/-- The total Pfaffian curvature of S^{2n} is 2·(2π)^n. For n = 1 this is the familiar
    ∫_{S²} K dA = 4π. -/
theorem sphereCGB_totalPfaffian (n : ℕ) :
    (sphereCGB n).totalPfaffian = 2 * (2 * π) ^ n := rfl

/-- Concretely for the 2-sphere: ∫_{S²} Pf(Ω) = 4π. -/
theorem sphere_two_total : (sphereCGB 1).totalPfaffian = 4 * π := by
  show 2 * cgbConst 1 = 4 * π
  rw [cgbConst_one]; ring

-- ============================================================================
-- Part VII: Products of manifolds (χ is multiplicative)
-- ============================================================================

/-- The product M × N of two Chern-Gauss-Bonnet manifolds. The dimension adds, the
    Euler characteristic multiplies (χ(M×N) = χ(M)·χ(N)), and the total Pfaffian
    multiplies — consistent with Chern-Gauss-Bonnet because (2π)^{m+n} factors. -/
def prodCGB (M N : CGBManifold) : CGBManifold where
  halfDim := M.halfDim + N.halfDim
  chi := M.chi * N.chi
  totalPfaffian := M.totalPfaffian * N.totalPfaffian
  chern_gauss_bonnet := by
    rw [M.chern_gauss_bonnet, N.chern_gauss_bonnet, cgbConst_add]
    push_cast; ring

/-- Dimensions add under products: dim(M × N) = dim M + dim N. -/
theorem prodCGB_dim (M N : CGBManifold) :
    (prodCGB M N).dim = M.dim + N.dim := by
  show 2 * (M.halfDim + N.halfDim) = 2 * M.halfDim + 2 * N.halfDim; ring

/-- The Euler characteristic is multiplicative: χ(M × N) = χ(M)·χ(N). -/
theorem prodCGB_chi (M N : CGBManifold) :
    (prodCGB M N).chi = M.chi * N.chi := rfl

/-- The total Pfaffian curvature is multiplicative under products. -/
theorem prodCGB_totalPfaffian (M N : CGBManifold) :
    (prodCGB M N).totalPfaffian = M.totalPfaffian * N.totalPfaffian := rfl

/-- S² × S² is 4-dimensional with χ = 4, so ∫ Pf(Ω) = 4·(2π)² = 16π². -/
theorem sphere_prod_sphere_chi :
    (prodCGB (sphereCGB 1) (sphereCGB 1)).chi = 4 := by
  show (2 : ℤ) * 2 = 4; ring

-- ============================================================================
-- Part VIII: Vanishing Euler characteristic — tori and odd dimensions
-- ============================================================================

/-- The even-dimensional torus T^{2n} as a Chern-Gauss-Bonnet manifold: it is flat,
    χ = 0, and ∫ Pf(Ω) = 0. -/
def torusCGB (n : ℕ) : CGBManifold where
  halfDim := n
  chi := 0
  totalPfaffian := 0
  chern_gauss_bonnet := by simp

/-- The flat torus has vanishing total Pfaffian. -/
theorem torusCGB_totalPfaffian (n : ℕ) : (torusCGB n).totalPfaffian = 0 := rfl

/-- The even-dimensional torus `T^{2n}` has dimension `2n`.  The `dim` companion of
    `torusCGB_totalPfaffian`, matching `sphereCGB_dim` / `prodCGB_dim`. -/
theorem torusCGB_dim (n : ℕ) : (torusCGB n).dim = 2 * n := rfl

/-- The even-dimensional torus `T^{2n}` has vanishing Euler characteristic — the
    defining feature that makes `torusCGB_totalPfaffian` an instance of
    `totalPfaffian_eq_zero_of_chi_zero`.  The `chi` companion completing the torus's
    invariant triple `(dim, chi, totalPfaffian) = (2n, 0, 0)`, matching the
    `sphereCGB` / `prodCGB` / `genusSurfaceCGB` constructions. -/
theorem torusCGB_chi (n : ℕ) : (torusCGB n).chi = 0 := rfl

/-- A closed odd-dimensional manifold has vanishing Euler characteristic (Poincaré
    duality), which is *why* the Chern-Gauss-Bonnet integrand — built from the Pfaffian,
    an even-dimensional invariant — carries no information there. We record the
    χ = 0 conclusion as a structure-encoded fact. -/
structure ClosedOddManifold where
  /-- The odd dimension 2k+1. -/
  k : ℕ
  /-- Euler characteristic, forced to 0 by Poincaré duality in odd dimension. -/
  chi : ℤ
  /-- Poincaré duality: χ(M) = 0 for closed odd-dimensional M. -/
  chi_zero : chi = 0

/-- The dimension of a closed odd manifold is odd. -/
theorem ClosedOddManifold.dim_odd (M : ClosedOddManifold) : Odd (2 * M.k + 1) :=
  ⟨M.k, rfl⟩

/-- Its Euler characteristic vanishes. -/
theorem ClosedOddManifold.euler_char_zero (M : ClosedOddManifold) : M.chi = 0 :=
  M.chi_zero

/-- The odd sphere S^{2k+1} realizes this: its combinatorial Euler characteristic is 0,
    matching `ClosedOddManifold.chi_zero`. -/
theorem oddSphere_chi_zero (k : ℕ) : sphereEulerChar (2 * k + 1) = 0 :=
  sphereEulerChar_odd k

-- ============================================================================
-- Part IX: The Chern multiplicities — Euler number is an integer
-- ============================================================================

/-- The Euler number ∫_M Pf(Ω/2π) is always an integer (it equals χ(M) ∈ ℤ). This is
    the deep content of Chern-Gauss-Bonnet: a transcendental curvature integral lands
    on a topological integer. -/
theorem euler_number_integral (M : CGBManifold) :
    ∃ k : ℤ, M.totalPfaffian / cgbConst M.halfDim = (k : ℝ) :=
  ⟨M.chi, by rw [M.normalized]⟩

/-- Two Chern-Gauss-Bonnet manifolds of the same dimension with the same total Pfaffian
    have the same Euler characteristic — the integral determines χ. -/
theorem chi_determined (M N : CGBManifold)
    (hdim : M.halfDim = N.halfDim) (hpf : M.totalPfaffian = N.totalPfaffian) :
    M.chi = N.chi := by
  have hM := M.normalized
  have hN := N.normalized
  rw [hdim, hpf, hN] at hM
  exact_mod_cast hM.symm

-- ============================================================================
-- Part X: Connected sums (χ is additive up to the sphere correction)
-- ============================================================================

/-- The connected sum `M # N` of two Chern-Gauss-Bonnet manifolds of the *same*
    dimension (`h : M.halfDim = N.halfDim`). Removing an open `2n`-disk from each
    and gluing along the boundary spheres gives χ(M # N) = χ(M) + χ(N) − χ(S^{2n})
    = χ(M) + χ(N) − 2, and correspondingly ∫Pf drops by the sphere's contribution
    `2·(2π)^n`. This is consistent with Chern-Gauss-Bonnet because the same
    normalization constant `cgbConst n` governs all three pieces. -/
def connectedSumCGB (M N : CGBManifold) (h : M.halfDim = N.halfDim) : CGBManifold where
  halfDim := M.halfDim
  chi := M.chi + N.chi - 2
  totalPfaffian := M.totalPfaffian + N.totalPfaffian - 2 * cgbConst M.halfDim
  chern_gauss_bonnet := by
    rw [M.chern_gauss_bonnet, N.chern_gauss_bonnet, h]
    push_cast; ring

/-- Connected sum preserves dimension: dim(M # N) = dim M. -/
theorem connectedSumCGB_dim (M N : CGBManifold) (h : M.halfDim = N.halfDim) :
    (connectedSumCGB M N h).dim = M.dim := rfl

/-- **Euler characteristic of a connected sum**: χ(M # N) = χ(M) + χ(N) − 2. -/
theorem connectedSumCGB_chi (M N : CGBManifold) (h : M.halfDim = N.halfDim) :
    (connectedSumCGB M N h).chi = M.chi + N.chi - 2 := rfl

/-- **Total Pfaffian of a connected sum**: it is additive minus the sphere's
    `2·(2π)^n` (the curvature removed with the two glued disks). -/
theorem connectedSumCGB_totalPfaffian (M N : CGBManifold) (h : M.halfDim = N.halfDim) :
    (connectedSumCGB M N h).totalPfaffian
      = M.totalPfaffian + N.totalPfaffian - 2 * cgbConst M.halfDim := rfl

/-- **The sphere is the identity for connected sum** (on Euler characteristics):
    χ(S^{2n} # N) = χ(N). Connected sum makes `2n`-manifolds a monoid with
    identity `S^{2n}`, and χ − 2 is the induced additive homomorphism to ℤ. -/
theorem connectedSum_sphere_chi (n : ℕ) (N : CGBManifold)
    (h : (sphereCGB n).halfDim = N.halfDim) :
    (connectedSumCGB (sphereCGB n) N h).chi = N.chi := by
  rw [connectedSumCGB_chi]
  show (2 : ℤ) + N.chi - 2 = N.chi
  ring

/-- The sphere is also neutral for the total Pfaffian: ∫Pf(S^{2n} # N) = ∫Pf(N),
    since the `2·(2π)^n` removed with the two disks exactly cancels the sphere's own
    total Pfaffian `2·(2π)^n`. -/
theorem connectedSum_sphere_totalPfaffian (n : ℕ) (N : CGBManifold)
    (h : (sphereCGB n).halfDim = N.halfDim) :
    (connectedSumCGB (sphereCGB n) N h).totalPfaffian = N.totalPfaffian := by
  rw [connectedSumCGB_totalPfaffian]
  show 2 * cgbConst n + N.totalPfaffian - 2 * cgbConst n = N.totalPfaffian
  ring

/-- **Right identity: `χ(N # S^{2n}) = χ(N)`.**  The mirror of `connectedSum_sphere_chi`
    (the left identity `χ(S^{2n} # N) = χ(N)`).  With both sides, `S^{2n}` is a genuine
    *two-sided* identity for connected sum on Euler characteristics — the identity axiom of
    the connected-sum monoid the docstrings advertise. -/
theorem connectedSum_sphere_chi_right (n : ℕ) (N : CGBManifold)
    (h : N.halfDim = (sphereCGB n).halfDim) :
    (connectedSumCGB N (sphereCGB n) h).chi = N.chi := by
  rw [connectedSumCGB_chi]
  show N.chi + (2 : ℤ) - 2 = N.chi
  ring

/-- **Commutativity on Euler characteristics: `χ(M # N) = χ(N # M)`.**  Connected sum is
    commutative on `χ` (`χ(M#N) = M.chi + N.chi − 2` is symmetric in `M, N`), the commutativity
    axiom of the connected-sum monoid.  Together with `connectedSumCGB_chi_assoc` and the
    two-sided sphere identity (`connectedSum_sphere_chi` / `connectedSum_sphere_chi_right`) this
    makes `(2n`-manifolds, `#)` a genuine *commutative* monoid on `χ`, with `χ − 2` the induced
    additive homomorphism to `ℤ`. -/
theorem connectedSumCGB_chi_comm (M N : CGBManifold) (h : M.halfDim = N.halfDim) :
    (connectedSumCGB M N h).chi = (connectedSumCGB N M h.symm).chi := by
  rw [connectedSumCGB_chi, connectedSumCGB_chi]; ring

/-- **Associativity on Euler characteristics: `χ((M # N) # P) = χ(M # (N # P))`.**  Both sides
    equal `M.chi + N.chi + P.chi − 4`, so connected sum is associative on `χ` — the associativity
    axiom of the connected-sum monoid.  (The dimension hypotheses force all three `halfDim`s
    equal, so both nested connected sums are well-formed.) -/
theorem connectedSumCGB_chi_assoc (M N P : CGBManifold)
    (hMN : M.halfDim = N.halfDim) (hNP : N.halfDim = P.halfDim) :
    (connectedSumCGB (connectedSumCGB M N hMN) P (hMN.trans hNP)).chi
      = (connectedSumCGB M (connectedSumCGB N P hNP) hMN).chi := by
  rw [connectedSumCGB_chi, connectedSumCGB_chi, connectedSumCGB_chi, connectedSumCGB_chi]
  ring

/-- **Commutativity on the total Pfaffian: `∫Pf(M # N) = ∫Pf(N # M)`.**  The Gauss-Bonnet
    companion of `connectedSumCGB_chi_comm`: the connected-sum total curvature
    `M.totalPfaffian + N.totalPfaffian − 2·cgbConst` is symmetric in `M, N` because the removed
    sphere correction `2·cgbConst M.halfDim = 2·cgbConst N.halfDim` agrees (`h : M.halfDim =
    N.halfDim`).  So connected sum is commutative as a Chern-Gauss-Bonnet operation, not merely
    on `χ`. -/
theorem connectedSumCGB_totalPfaffian_comm (M N : CGBManifold) (h : M.halfDim = N.halfDim) :
    (connectedSumCGB M N h).totalPfaffian = (connectedSumCGB N M h.symm).totalPfaffian := by
  rw [connectedSumCGB_totalPfaffian, connectedSumCGB_totalPfaffian, h]; ring

/-- **Genus-2 surface from two tori.** The connected sum T² # T² is the genus-2
    closed orientable surface, with χ = 0 + 0 − 2 = −2 — matching the classical
    χ(Σ_g) = 2 − 2g at g = 2. -/
theorem genus_two_surface_chi :
    (connectedSumCGB (torusCGB 1) (torusCGB 1) rfl).chi = -2 := by
  rw [connectedSumCGB_chi]
  show (0 : ℤ) + 0 - 2 = -2
  ring

/-- The genus-2 surface has total Pfaffian ∫Pf = −4π (so ∫Pf/2π = −2 = χ),
    consistent with Gauss-Bonnet: a hyperbolic Σ₂ has ∫K dA = 2π·χ = −4π. -/
theorem genus_two_surface_totalPfaffian :
    (connectedSumCGB (torusCGB 1) (torusCGB 1) rfl).totalPfaffian = -(4 * π) := by
  rw [connectedSumCGB_totalPfaffian]
  show (0 : ℝ) + 0 - 2 * cgbConst 1 = -(4 * π)
  rw [cgbConst_one]; ring

-- ============================================================================
-- Part XI: The closed orientable surface of genus g — full classification
-- ============================================================================

/-- **The closed orientable surface of genus `g`, `Σ_g`, as a Chern-Gauss-Bonnet
    manifold.**  Topologically `Σ_g` is the `g`-fold connected sum of tori (a sphere
    with `g` handles); attaching each handle drops the Euler characteristic by `2`
    (`connectedSumCGB_chi` with `χ(T²) = 0`), giving `χ(Σ_g) = 2 − 2g`.  We record it
    directly as a dimension-`2` (`halfDim = 1`) manifold with that Euler characteristic
    and the Gauss-Bonnet-consistent total curvature `∫Pf = 2π·χ`; the Chern-Gauss-Bonnet
    identity then holds by definition.  This generalizes the `g = 0, 1, 2` special cases
    (`sphereCGB 1`, `torusCGB 1`, `T² # T²`) to every genus at once. -/
def genusSurfaceCGB (g : ℕ) : CGBManifold where
  halfDim := 1
  chi := 2 - 2 * (g : ℤ)
  totalPfaffian := cgbConst 1 * ((2 - 2 * (g : ℤ) : ℤ) : ℝ)
  chern_gauss_bonnet := rfl

/-- `Σ_g` is a surface: `halfDim = 1`, i.e. real dimension `2`. -/
@[simp] theorem genusSurfaceCGB_halfDim (g : ℕ) : (genusSurfaceCGB g).halfDim = 1 := rfl

/-- **Full surface classification: `χ(Σ_g) = 2 − 2g`.**  The Euler characteristic of the
    genus-`g` closed orientable surface, for every `g`. -/
theorem genusSurfaceCGB_chi (g : ℕ) : (genusSurfaceCGB g).chi = 2 - 2 * (g : ℤ) := rfl

/-- **Gauss-Bonnet for `Σ_g`: `∫_{Σ_g} K dA = 2π·χ = 4π(1 − g)`.**  The total curvature of
    the genus-`g` surface, obtained from the dimension-`2` reduction `two_dim_gauss_bonnet`
    of the Chern-Gauss-Bonnet identity. -/
theorem genusSurfaceCGB_gauss_bonnet (g : ℕ) :
    (genusSurfaceCGB g).totalPfaffian = 2 * π * (genusSurfaceCGB g).chi :=
  two_dim_gauss_bonnet (genusSurfaceCGB g) rfl

/-- The total curvature of `Σ_g` in closed form: `∫Pf = (2 − 2g)·2π = 4π(1 − g)`, negative
    once `g ≥ 2` (the hyperbolic regime). -/
theorem genusSurfaceCGB_totalPfaffian (g : ℕ) :
    (genusSurfaceCGB g).totalPfaffian = (2 - 2 * (g : ℝ)) * (2 * π) := by
  show cgbConst 1 * ((2 - 2 * (g : ℤ) : ℤ) : ℝ) = (2 - 2 * (g : ℝ)) * (2 * π)
  rw [cgbConst_one]; push_cast; ring

/-- **Handle attachment.**  Passing from `Σ_g` to `Σ_{g+1}` adds a torus handle and drops
    the Euler characteristic by `2`: `χ(Σ_{g+1}) = χ(Σ_g) + χ(T²) − 2`, exactly the
    connected-sum law `connectedSumCGB_chi` with `χ(T²) = 0`.  This is the recursive content
    behind the closed formula `χ(Σ_g) = 2 − 2g`. -/
theorem genusSurfaceCGB_chi_succ (g : ℕ) :
    (genusSurfaceCGB (g + 1)).chi = (genusSurfaceCGB g).chi + (torusCGB 1).chi - 2 := by
  show (2 - 2 * ((g + 1 : ℕ) : ℤ)) = (2 - 2 * (g : ℤ)) + 0 - 2
  push_cast; ring

/-- Genus `0` is the sphere: `χ(Σ_0) = 2`. -/
theorem genusSurfaceCGB_zero_chi : (genusSurfaceCGB 0).chi = 2 := by decide

/-- Genus `1` is the torus: `χ(Σ_1) = 0`. -/
theorem genusSurfaceCGB_one_chi : (genusSurfaceCGB 1).chi = 0 := by decide

/-- Genus `2`: `χ(Σ_2) = −2`, matching `genus_two_surface_chi` (the `T² # T²` construction). -/
theorem genusSurfaceCGB_two_chi : (genusSurfaceCGB 2).chi = -2 := by decide

-- ============================================================================
-- Part XII: Genus is additive under connected sum — (surfaces, #) ≅ (ℕ, +)
-- ============================================================================

/-- **Genus additivity (Euler characteristic).**  The connected sum of the genus-`g`
    and genus-`h` closed orientable surfaces is the genus-`(g+h)` surface:
    `χ(Σ_g # Σ_h) = χ(Σ_{g+h})`.  Indeed `(2−2g) + (2−2h) − 2 = 2 − 2(g+h)`.  This is
    the full additivity behind the single-handle recursion `genusSurfaceCGB_chi_succ`
    (the `h = 1` case), and exhibits genus as the monoid isomorphism
    `(closed orientable surfaces, #) ≅ (ℕ, +)`. -/
theorem connectedSum_genusSurface_chi (g h : ℕ) :
    (connectedSumCGB (genusSurfaceCGB g) (genusSurfaceCGB h) rfl).chi
      = (genusSurfaceCGB (g + h)).chi := by
  simp only [connectedSumCGB_chi, genusSurfaceCGB_chi]
  push_cast
  ring

/-- **Genus additivity (total curvature).**  The connected sum is also consistent on
    the Gauss-Bonnet total Pfaffian: `∫Pf(Σ_g # Σ_h) = ∫Pf(Σ_{g+h}) = 4π(1 − g − h)`.
    The `2·(2π)` curvature removed with the two glued disks accounts exactly for the
    `χ`-drop, so `Σ_g # Σ_h` and `Σ_{g+h}` agree as Chern-Gauss-Bonnet manifolds. -/
theorem connectedSum_genusSurface_totalPfaffian (g h : ℕ) :
    (connectedSumCGB (genusSurfaceCGB g) (genusSurfaceCGB h) rfl).totalPfaffian
      = (genusSurfaceCGB (g + h)).totalPfaffian := by
  simp only [connectedSumCGB_totalPfaffian, genusSurfaceCGB_halfDim,
    genusSurfaceCGB_totalPfaffian, cgbConst_one]
  push_cast
  ring

-- ============================================================================
-- Part XIII: χ is a complete invariant of Σ_g — faithfulness of the monoid
--            embedding (surfaces, #) ↪ (ℕ, +)
-- ============================================================================

/-- **Euler characteristic is a complete invariant of the genus surfaces.**  Two
    genus surfaces have the same Euler characteristic iff they have the same genus:
    `χ(Σ_g) = χ(Σ_h) ↔ g = h`.  Combined with the additivity `connectedSum_genusSurface_chi`
    (the homomorphism half), this injectivity is the *faithfulness* half that upgrades
    `g ↦ Σ_g` from a monoid homomorphism to a genuine monoid **embedding**
    `(closed orientable surfaces, #) ↪ (ℕ, +)`: distinct genera are never conflated by
    `χ`.  The forward direction is the classification statement `2 − 2g = 2 − 2h ⇒ g = h`. -/
theorem genusSurfaceCGB_chi_inj (g h : ℕ) :
    (genusSurfaceCGB g).chi = (genusSurfaceCGB h).chi ↔ g = h := by
  rw [genusSurfaceCGB_chi, genusSurfaceCGB_chi]
  omega

/-- **Distinct genera give distinct surfaces.**  The contrapositive of the injectivity
    `genusSurfaceCGB_chi_inj`: if `g ≠ h` then `χ(Σ_g) ≠ χ(Σ_h)`.  This is precisely the
    faithfulness of the connected-sum monoid embedding — no two non-homeomorphic closed
    orientable surfaces share an Euler characteristic. -/
theorem genusSurfaceCGB_chi_ne_of_ne {g h : ℕ} (hgh : g ≠ h) :
    (genusSurfaceCGB g).chi ≠ (genusSurfaceCGB h).chi :=
  fun hc => hgh ((genusSurfaceCGB_chi_inj g h).mp hc)

/-- **The inverse of the classification: genus recovered from Euler characteristic.**
    `2g = 2 − χ(Σ_g)`, i.e. `g = (2 − χ)/2`.  This explicit left inverse of `g ↦ χ(Σ_g)`
    is the constructive witness for `genusSurfaceCGB_chi_inj`, and expresses the genus of
    a closed orientable surface directly in terms of its Euler characteristic. -/
theorem genusSurfaceCGB_genus_of_chi (g : ℕ) :
    2 * (g : ℤ) = 2 - (genusSurfaceCGB g).chi := by
  rw [genusSurfaceCGB_chi]; ring

/-- **Total curvature is also a complete invariant of the genus surfaces**:
    `∫Pf(Σ_g) = ∫Pf(Σ_h) ↔ g = h`.  The Gauss-Bonnet total curvature `4π(1 − g)` is faithful in the
    genus, exactly like the Euler characteristic (`genusSurfaceCGB_chi_inj`) — unsurprising since the
    two differ only by the positive constant `2π` (`genusSurfaceCGB_gauss_bonnet`), but it records that
    the *analytic* invariant, not just the topological one, distinguishes all closed orientable
    surfaces. -/
theorem genusSurfaceCGB_totalPfaffian_inj (g h : ℕ) :
    (genusSurfaceCGB g).totalPfaffian = (genusSurfaceCGB h).totalPfaffian ↔ g = h := by
  rw [genusSurfaceCGB_totalPfaffian, genusSurfaceCGB_totalPfaffian]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  constructor
  · intro heq
    have h2 : (2 - 2 * (g : ℝ)) = (2 - 2 * (h : ℝ)) :=
      mul_right_cancel₀ (ne_of_gt hpi) heq
    have : (g : ℝ) = (h : ℝ) := by linarith
    exact_mod_cast this
  · intro hgh; subst hgh; rfl

/-- **Total curvature strictly decreases with genus**: `g < h ⟹ ∫Pf(Σ_h) < ∫Pf(Σ_g)`.  Each added
    handle makes the total Gauss-Bonnet curvature `4π(1 − g)` strictly more negative — the monotone
    refinement of the sign trichotomy below, and the quantitative form of "more topology forces more
    negative curvature". -/
theorem genusSurfaceCGB_totalPfaffian_strictAnti {g h : ℕ} (hgh : g < h) :
    (genusSurfaceCGB h).totalPfaffian < (genusSurfaceCGB g).totalPfaffian := by
  rw [genusSurfaceCGB_totalPfaffian, genusSurfaceCGB_totalPfaffian]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hgh' : (g : ℝ) < (h : ℝ) := by exact_mod_cast hgh
  have hfac : (2 - 2 * (h : ℝ)) < (2 - 2 * (g : ℝ)) := by linarith
  exact mul_lt_mul_of_pos_right hfac hpi

/-- **Euler characteristic is strictly decreasing in genus.**  `g ↦ χ(Σ_g) = 2 − 2g` is
    `StrictAnti`: every added handle strictly lowers the Euler characteristic.  This is the
    order-theoretic sharpening of the injectivity `genusSurfaceCGB_chi_inj` — the embedding
    `(surfaces, #) ↪ (ℕ, +)` reverses order under `χ` — and the discrete shadow of the
    Gauss-Bonnet sign trichotomy (`χ` drops from `+2` through `0` into the negatives as `g`
    grows). -/
theorem genusSurfaceCGB_chi_strictAnti :
    StrictAnti (fun g : ℕ => (genusSurfaceCGB g).chi) := by
  intro a b hab
  simp only [genusSurfaceCGB_chi]
  omega

/-- **The sphere maximizes the Euler characteristic: `χ(Σ_g) ≤ 2`.**  Since `χ(Σ_g) = 2 − 2g`
    and `g ≥ 0`, no closed orientable surface has Euler characteristic above `2`; the bound
    is attained only at the sphere. -/
theorem genusSurfaceCGB_chi_le_two (g : ℕ) : (genusSurfaceCGB g).chi ≤ 2 := by
  rw [genusSurfaceCGB_chi]; omega

/-- **`χ = 2` characterizes the sphere.**  Equality in `genusSurfaceCGB_chi_le_two` holds
    exactly at genus `0`: `χ(Σ_g) = 2 ↔ g = 0`.  The top of the `χ`-range is the unique
    positively-curved surface, matching `genusSurfaceCGB_totalPfaffian_pos_iff`. -/
theorem genusSurfaceCGB_chi_eq_two_iff (g : ℕ) : (genusSurfaceCGB g).chi = 2 ↔ g = 0 := by
  rw [genusSurfaceCGB_chi]; omega

/-- **The Euler characteristic of a closed orientable surface is even.**  `χ(Σ_g) = 2 − 2g
    = 2(1 − g)` is always even — the parity constraint that, together with `χ ≤ 2`
    (`genusSurfaceCGB_chi_le_two`), pins the image of `g ↦ χ(Σ_g)` to exactly the even
    integers `≤ 2`. -/
theorem genusSurfaceCGB_chi_even (g : ℕ) : Even (genusSurfaceCGB g).chi :=
  ⟨1 - (g : ℤ), by rw [genusSurfaceCGB_chi]; ring⟩

-- ============================================================================
-- Part XIV: The Gauss-Bonnet sign trichotomy — total curvature detects the
--           uniformization regime (spherical / flat / hyperbolic) from the genus
-- ============================================================================

/-- **Positive total curvature ⇔ the sphere (`g = 0`).**  Since `∫Pf(Σ_g) = 4π(1 − g)`
    and `2π > 0`, the total Gauss-Bonnet curvature is *positive* exactly for genus `0` —
    the spherical (positively-curved) case.  This is the `χ > 0` corner of the
    uniformization trichotomy, read off directly from the genus. -/
theorem genusSurfaceCGB_totalPfaffian_pos_iff (g : ℕ) :
    0 < (genusSurfaceCGB g).totalPfaffian ↔ g = 0 := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [genusSurfaceCGB_totalPfaffian, mul_pos_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have h1 : (g : ℝ) < 1 := by linarith
      have : g < 1 := by exact_mod_cast h1
      omega
    · exact absurd h (lt_asymm hpi)
  · intro hg; subst hg; exact Or.inl ⟨by push_cast; norm_num, hpi⟩

/-- **Zero total curvature ⇔ the torus (`g = 1`).**  The total Gauss-Bonnet curvature
    `4π(1 − g)` vanishes exactly for genus `1` — the flat (Euclidean) case.  This is the
    `χ = 0` corner of the uniformization trichotomy. -/
theorem genusSurfaceCGB_totalPfaffian_eq_zero_iff (g : ℕ) :
    (genusSurfaceCGB g).totalPfaffian = 0 ↔ g = 1 := by
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [genusSurfaceCGB_totalPfaffian, mul_eq_zero]
  constructor
  · rintro (h | h)
    · have : (g : ℝ) = 1 := by linarith
      exact_mod_cast this
    · exact absurd h hpi
  · intro hg; subst hg; exact Or.inl (by push_cast; ring)

/-- **Negative total curvature ⇔ higher genus (`g ≥ 2`).**  The total Gauss-Bonnet
    curvature `4π(1 − g)` is *negative* exactly for genus `≥ 2` — the hyperbolic
    (negatively-curved) case.  Together with `genusSurfaceCGB_totalPfaffian_pos_iff` and
    `..._eq_zero_iff` this is the full **Gauss-Bonnet sign trichotomy**: the sign of the
    total curvature of a closed orientable surface reads off its uniformization type
    (spherical `g = 0`, flat `g = 1`, hyperbolic `g ≥ 2`) directly from the genus. -/
theorem genusSurfaceCGB_totalPfaffian_neg_iff (g : ℕ) :
    (genusSurfaceCGB g).totalPfaffian < 0 ↔ 2 ≤ g := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  rw [genusSurfaceCGB_totalPfaffian, mul_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd h (lt_asymm hpi)
    · have h1 : (1 : ℝ) < (g : ℝ) := by linarith
      have : 1 < g := by exact_mod_cast h1
      omega
  · intro hg
    refine Or.inr ⟨?_, hpi⟩
    have : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
    linarith

-- ============================================================================
-- Part XV: Weak antitonicity of the genus Euler characteristic, and the
--          Euler characteristic / total curvature of product surfaces `Σ_g × Σ_h`
-- ============================================================================

/-- **`χ(Σ_g)` is (weakly) antitone in the genus**, the `≤`-form of
    `genusSurfaceCGB_chi_strictAnti` (Part XIII).  Every added handle can only lower
    the Euler characteristic, so `g ↦ χ(Σ_g) = 2 − 2g` is monotone decreasing. -/
theorem genusSurfaceCGB_chi_antitone :
    Antitone (fun g : ℕ => (genusSurfaceCGB g).chi) :=
  genusSurfaceCGB_chi_strictAnti.antitone

/-- **Euler characteristic of the product surface `Σ_g × Σ_h`.**  Since `χ` is
    multiplicative under products (`prodCGB_chi`), the product `4`-manifold
    `Σ_g × Σ_h` has `χ = (2 − 2g)(2 − 2h)`.  Generalises `sphere_prod_sphere_chi`
    (the `g = h = 0` case, `χ = 4`) to arbitrary genera. -/
theorem prodCGB_genusSurface_chi (g h : ℕ) :
    (prodCGB (genusSurfaceCGB g) (genusSurfaceCGB h)).chi
      = (2 - 2 * (g : ℤ)) * (2 - 2 * (h : ℤ)) := by
  rw [prodCGB_chi, genusSurfaceCGB_chi, genusSurfaceCGB_chi]

/-- **Total Gauss-Bonnet curvature of the product surface `Σ_g × Σ_h`.**  The total
    Pfaffian multiplies under products (`prodCGB_totalPfaffian`), giving the closed
    form `∫Pf(Σ_g × Σ_h) = [4π(1−g)]·[4π(1−h)] = 16π²(1−g)(1−h)` for the product
    `4`-manifold — the Chern-Gauss-Bonnet content `(2π)²·χ(Σ_g × Σ_h)` written out. -/
theorem prodCGB_genusSurface_totalPfaffian (g h : ℕ) :
    (prodCGB (genusSurfaceCGB g) (genusSurfaceCGB h)).totalPfaffian
      = 16 * π ^ 2 * (1 - (g : ℝ)) * (1 - (h : ℝ)) := by
  rw [prodCGB_totalPfaffian, genusSurfaceCGB_totalPfaffian, genusSurfaceCGB_totalPfaffian]
  ring

-- ============================================================================
-- Part XVI: The homological origin of `χ(Σ_g) = 2 − 2g` — Betti numbers,
--           Poincaré duality, and the Euler–Poincaré formula
-- ============================================================================

/-
  Parts XI–XV obtain `χ(Σ_g) = 2 − 2g` *geometrically*: from the connected-sum handle
  recursion and, ultimately, the Chern-Gauss-Bonnet identity carried in `CGBManifold`.
  There is a second, purely *topological* route through the singular homology of the
  surface.  For the closed orientable surface `Σ_g` the homology groups are

      H₀(Σ_g) ≅ ℤ,   H₁(Σ_g) ≅ ℤ^{2g},   H₂(Σ_g) ≅ ℤ,   Hᵢ = 0 (i ≥ 3),

  so the Betti numbers (ranks) are `b₀ = 1`, `b₁ = 2g`, `b₂ = 1`.  The **Euler–Poincaré
  formula** `χ = Σ (−1)ⁱ bᵢ` then gives `χ = 1 − 2g + 1 = 2 − 2g`, agreeing with the
  geometric value `genusSurfaceCGB_chi`.  This section records that homological data and
  the two structural facts it encodes: **Poincaré duality** `bᵢ = b_{2−i}` (which forces
  the middle Betti number `b₁ = 2g` to be even — the rank of the symplectic intersection
  form on `H₁`) and the Euler–Poincaré identity itself.  Everything here is elementary
  arithmetic over `ℕ`/`ℤ`, hence fully verified (0-axiom); the Betti numbers are recorded
  as data, not derived from a Mathlib singular-homology computation.
-/

/-- **Betti numbers of the closed orientable surface `Σ_g`.**  `bᵢ = rank Hᵢ(Σ_g; ℤ)`:
    `b₀ = 1` (connected), `b₁ = 2g` (`H₁ ≅ ℤ^{2g}`, the abelianized fundamental group),
    `b₂ = 1` (closed orientable ⇒ `H₂ ≅ ℤ`), and `bᵢ = 0` for `i ≥ 3`. -/
def genusSurfaceBetti (g : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2 * g
  | 2 => 1
  | _ + 3 => 0

/-- `b₀(Σ_g) = 1`: the surface is connected. -/
@[simp] theorem genusSurfaceBetti_zero (g : ℕ) : genusSurfaceBetti g 0 = 1 := rfl

/-- **`b₁(Σ_g) = 2g`.**  The first Betti number is twice the genus — the rank of
    `H₁(Σ_g; ℤ) ≅ ℤ^{2g}`, equivalently the rank of the abelianization of `π₁(Σ_g)`
    (each handle contributes two independent `1`-cycles). -/
@[simp] theorem genusSurfaceBetti_one (g : ℕ) : genusSurfaceBetti g 1 = 2 * g := rfl

/-- `b₂(Σ_g) = 1`: a closed orientable surface has top homology `H₂ ≅ ℤ` generated by the
    fundamental class. -/
@[simp] theorem genusSurfaceBetti_two (g : ℕ) : genusSurfaceBetti g 2 = 1 := rfl

/-- `bᵢ(Σ_g) = 0` for `i ≥ 3`: a `2`-manifold has no homology above its dimension. -/
@[simp] theorem genusSurfaceBetti_vanish (g i : ℕ) : genusSurfaceBetti g (i + 3) = 0 := rfl

/-- **The Euler–Poincaré formula for `Σ_g`: `χ = b₀ − b₁ + b₂`.**  The alternating sum of
    the Betti numbers reproduces the Euler characteristic `2 − 2g` computed geometrically
    in `genusSurfaceCGB_chi`.  This is the topological (homological) origin of the
    Gauss-Bonnet value: `∫Pf(Ω)/(2π) = χ = Σ(−1)ⁱ bᵢ`. -/
theorem genusSurface_euler_poincare (g : ℕ) :
    (genusSurfaceCGB g).chi
      = (genusSurfaceBetti g 0 : ℤ) - genusSurfaceBetti g 1 + genusSurfaceBetti g 2 := by
  rw [genusSurfaceCGB_chi, genusSurfaceBetti_zero, genusSurfaceBetti_one, genusSurfaceBetti_two]
  push_cast; ring

/-- **Poincaré duality for `Σ_g`: `bᵢ = b_{2−i}` for `i ≤ 2`.**  The Betti sequence
    `(1, 2g, 1)` is palindromic — the manifestation of the duality `Hᵢ ≅ H^{2−i} ≅ H_{2−i}`
    for a closed orientable `2`-manifold (finitely generated free homology). -/
theorem genusSurfaceBetti_poincare_duality (g : ℕ) {i : ℕ} (hi : i ≤ 2) :
    genusSurfaceBetti g i = genusSurfaceBetti g (2 - i) := by
  interval_cases i <;> rfl

/-- **Top Betti equals bottom Betti: `b₂ = b₀ = 1`.**  The `i = 0` case of Poincaré duality:
    orientability and connectedness pin both the fundamental class and the point class to
    rank `1`. -/
theorem genusSurfaceBetti_top_eq_bottom (g : ℕ) :
    genusSurfaceBetti g 2 = genusSurfaceBetti g 0 := rfl

/-- **Total Betti number of `Σ_g`: `b₀ + b₁ + b₂ = 2 + 2g`.**  The total rank of the
    homology `H_*(Σ_g; ℤ)` (the dimension of `H_*` over `ℚ`) grows linearly with the genus,
    while the *alternating* sum stays `2 − 2g` (`genusSurface_euler_poincare`). -/
theorem genusSurface_betti_total (g : ℕ) :
    genusSurfaceBetti g 0 + genusSurfaceBetti g 1 + genusSurfaceBetti g 2 = 2 + 2 * g := by
  simp only [genusSurfaceBetti_zero, genusSurfaceBetti_one, genusSurfaceBetti_two]
  omega

/-- **The middle Betti number is even.**  `b₁(Σ_g) = 2g` is even — the rank of the
    nondegenerate skew-symmetric (symplectic) intersection form on `H₁(Σ_g)`, which forces
    an even rank.  This is the homological reason the Euler characteristic is even
    (`genusSurfaceCGB_chi_even`), since `χ = 2 − b₁`. -/
theorem genusSurface_first_betti_even (g : ℕ) : Even (genusSurfaceBetti g 1) :=
  ⟨g, by rw [genusSurfaceBetti_one]; ring⟩

/-- **`χ(Σ_g) = 2 − b₁`.**  With `b₀ = b₂ = 1` (Poincaré duality), the Euler–Poincaré sum
    collapses to `χ = 2 − b₁`: the first Betti number alone determines the Euler
    characteristic of a closed orientable surface.  Combined with `genusSurface_first_betti_even`
    this re-proves `genusSurfaceCGB_chi_even` homologically. -/
theorem genusSurface_chi_eq_two_sub_first_betti (g : ℕ) :
    (genusSurfaceCGB g).chi = 2 - (genusSurfaceBetti g 1 : ℤ) := by
  rw [genusSurfaceCGB_chi, genusSurfaceBetti_one]; push_cast; ring

/-- **Homological re-derivation of the evenness of `χ`.**  Since `χ = 2 − b₁`
    (`genusSurface_chi_eq_two_sub_first_betti`) and `b₁` is even
    (`genusSurface_first_betti_even`), the Euler characteristic is even — the same
    conclusion as `genusSurfaceCGB_chi_even`, now traced to Poincaré duality on `H₁`
    rather than to the algebraic form `2 − 2g`. -/
theorem genusSurfaceCGB_chi_even' (g : ℕ) : Even (genusSurfaceCGB g).chi := by
  rw [genusSurface_chi_eq_two_sub_first_betti]
  obtain ⟨k, hk⟩ := genusSurface_first_betti_even g
  exact ⟨1 - (k : ℤ), by rw [hk]; push_cast; ring⟩

-- ============================================================================
-- Part XVII: The Cartesian-product monoid — (CGBManifolds, ×) with the point as
--            identity, and χ a monoid homomorphism to (ℤ, ·)
-- ============================================================================

/-
  Part X exhibits the *connected-sum* monoid `(2n`-manifolds, `#)`, with the sphere
  `S^{2n}` as identity and `χ − 2` the induced additive homomorphism to `(ℤ, +)`.
  The Cartesian product `×` (`prodCGB`) carries the complementary monoid structure:
  it is commutative and associative on `χ`, its identity is the single **point**
  (the `0`-dimensional manifold with `χ = 1`), and `χ` is *multiplicative*
  (`prodCGB_chi`).  So `χ` is a monoid homomorphism `((CGBManifolds, ×) → (ℤ, ·))`,
  exactly as `χ − 2` is one `((·, #) → (ℤ, +))`.  Everything reduces to the
  commutative-ring structure of `ℤ`, hence is fully verified (the two
  structure-encoded CGB assumptions are not invoked).
-/

/-- **The point manifold** — the `0`-dimensional closed manifold consisting of a single
    point: `halfDim = 0`, `χ = 1`, `∫Pf = 1` (the empty Pfaffian integrates to the point
    count).  It is the identity for the Cartesian product `prodCGB`. -/
def pointCGB : CGBManifold where
  halfDim := 0
  chi := 1
  totalPfaffian := 1
  chern_gauss_bonnet := by rw [cgbConst_zero]; norm_num

/-- `χ(pt) = 1`: the point has Euler characteristic one. -/
@[simp] theorem pointCGB_chi : pointCGB.chi = 1 := rfl

/-- `dim(pt) = 0`: the point is `0`-dimensional. -/
@[simp] theorem pointCGB_dim : pointCGB.dim = 0 := rfl

/-- `∫Pf(pt) = 1`: the point's total Pfaffian is its point count. -/
@[simp] theorem pointCGB_totalPfaffian : pointCGB.totalPfaffian = 1 := rfl

/-- **Left identity for `×` (Euler characteristic): `χ(pt × M) = χ(M)`.**  Since
    `χ(pt) = 1` and `χ` is multiplicative, the point is a left identity for the
    Cartesian-product monoid — the multiplicative analogue of the sphere's role as
    connected-sum identity (`connectedSum_sphere_chi`). -/
theorem prodCGB_point_chi (M : CGBManifold) : (prodCGB pointCGB M).chi = M.chi := by
  rw [prodCGB_chi]; show (1 : ℤ) * M.chi = M.chi; rw [one_mul]

/-- **Right identity for `×` (Euler characteristic): `χ(M × pt) = χ(M)`.**  The mirror of
    `prodCGB_point_chi`; together they make the point a genuine *two-sided* identity for
    the product monoid on `χ`. -/
theorem prodCGB_chi_point (M : CGBManifold) : (prodCGB M pointCGB).chi = M.chi := by
  rw [prodCGB_chi]; show M.chi * (1 : ℤ) = M.chi; rw [mul_one]

/-- **Commutativity on Euler characteristics: `χ(M × N) = χ(N × M)`.**  `χ` is multiplicative
    and `ℤ` is commutative, so the Cartesian product is commutative on `χ` — the commutativity
    axiom of the product monoid, paralleling `connectedSumCGB_chi_comm`. -/
theorem prodCGB_chi_comm (M N : CGBManifold) :
    (prodCGB M N).chi = (prodCGB N M).chi := by
  rw [prodCGB_chi, prodCGB_chi]; ring

/-- **Associativity on Euler characteristics: `χ((M × N) × P) = χ(M × (N × P))`.**  Both sides
    equal `χ(M)·χ(N)·χ(P)`, so the Cartesian product is associative on `χ` — the associativity
    axiom of the product monoid, paralleling `connectedSumCGB_chi_assoc`. -/
theorem prodCGB_chi_assoc (M N P : CGBManifold) :
    (prodCGB (prodCGB M N) P).chi = (prodCGB M (prodCGB N P)).chi := by
  rw [prodCGB_chi, prodCGB_chi, prodCGB_chi, prodCGB_chi]; ring

/-- **Left identity for `×` (total curvature): `∫Pf(pt × M) = ∫Pf(M)`.**  The total Pfaffian
    multiplies under products (`prodCGB_totalPfaffian`) and `∫Pf(pt) = 1`, so the point is
    also neutral for the Gauss-Bonnet total curvature — the product monoid is realised on
    `∫Pf`, not merely on `χ`. -/
theorem prodCGB_point_totalPfaffian (M : CGBManifold) :
    (prodCGB pointCGB M).totalPfaffian = M.totalPfaffian := by
  rw [prodCGB_totalPfaffian]; show (1 : ℝ) * M.totalPfaffian = M.totalPfaffian; rw [one_mul]

/-- **Commutativity on the total curvature: `∫Pf(M × N) = ∫Pf(N × M)`.**  The Gauss-Bonnet
    companion of `prodCGB_chi_comm`: the product total Pfaffian `M.totalPfaffian ·
    N.totalPfaffian` is symmetric in `M, N`, so the Cartesian product is commutative as a
    Chern-Gauss-Bonnet operation. -/
theorem prodCGB_totalPfaffian_comm (M N : CGBManifold) :
    (prodCGB M N).totalPfaffian = (prodCGB N M).totalPfaffian := by
  rw [prodCGB_totalPfaffian, prodCGB_totalPfaffian]; ring

/-- **The point is `0`-dimensional identity: `dim(pt × M) = dim M`.**  Cartesian product adds
    dimensions (`prodCGB_dim`) and `dim(pt) = 0`, so multiplying by the point preserves
    dimension — confirming the point is the product identity on the full invariant triple
    `(dim, χ, ∫Pf)`, just as the sphere `S^{2n}` is the connected-sum identity in each
    fixed dimension. -/
theorem prodCGB_point_dim (M : CGBManifold) : (prodCGB pointCGB M).dim = M.dim := by
  rw [prodCGB_dim]; show pointCGB.dim + M.dim = M.dim; rw [pointCGB_dim, zero_add]

-- ============================================================================
-- Part XVIII: The Künneth formula for Betti numbers — a homological
--             re-derivation of the multiplicativity of χ for `Σ_g × Σ_h`
-- ============================================================================

/-
  Part VII proves `χ(M × N) = χ(M)·χ(N)` from the structure field `prodCGB_chi`, and
  Part XVI records the Betti numbers `(b₀,b₁,b₂) = (1, 2g, 1)` of the surface `Σ_g`.
  The two meet through the **Künneth theorem**: for spaces with free integral homology
  (surfaces are such), the homology of a product is the graded tensor product, so the
  Betti numbers *convolve*,

      bₖ(M × N) = Σ_{i+j=k} bᵢ(M)·bⱼ(N).

  Applying this to the two surfaces gives the Betti numbers of the closed oriented
  `4`-manifold `Σ_g × Σ_h`:

      (b₀,b₁,b₂,b₃,b₄) = (1, 2(g+h), 2 + 4gh, 2(g+h), 1),

  a palindromic sequence (Poincaré duality on the `4`-manifold, `bᵢ = b_{4−i}`).  Its
  Euler–Poincaré alternating sum is `χ = Σ(−1)ⁱbᵢ = (2−2g)(2−2h)`, so **Künneth on Betti
  numbers reproduces `prodCGB_genusSurface_chi` homologically** — the multiplicativity of
  the Euler characteristic is the value at `t = −1` of the multiplicativity of the Poincaré
  polynomial.  Two familiar `4`-manifolds fall out as `g = h = 0` and `g = h = 1`:
  `S² × S²` with Betti `(1,0,2,0,1)` and `χ = 4`, and the `4`-torus `T⁴ = T² × T²` with
  Betti `(1,4,6,4,1) = (C(4,k))ₖ` and `χ = 0`.  Everything is finite convolution and
  integer arithmetic, hence fully verified (0-axiom); the two structure-encoded CGB
  assumptions are not invoked.
-/

/-- `b₃(Σ_g) = 0` at the literal degree `3` (a `2`-manifold has no homology in degree `3`).
    The literal-degree companion of `genusSurfaceBetti_vanish`, needed to evaluate the
    Künneth convolution in degrees `3` and `4`. -/
@[simp] theorem genusSurfaceBetti_three (g : ℕ) : genusSurfaceBetti g 3 = 0 := rfl

/-- `b₄(Σ_g) = 0` at the literal degree `4`. -/
@[simp] theorem genusSurfaceBetti_four (g : ℕ) : genusSurfaceBetti g 4 = 0 := rfl

/-- **Künneth convolution of two Betti sequences.**  `(b ⋆ c)(k) = Σ_{i+j=k} bᵢ·cⱼ`, the
    graded-tensor-product rank in degree `k`.  Over `ℤ` with free homology this is exactly
    the Betti number of a product space (no `Tor` correction). -/
def kunnethBetti (b c : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), b i * c (k - i)

/-- **Betti numbers of the product surface `Σ_g × Σ_h`**, the closed oriented `4`-manifold.
    Given here as explicit data `(1, 2(g+h), 2+4gh, 2(g+h), 1)`; `prodSurfaceBetti_kunneth`
    verifies that this sequence is exactly the Künneth convolution of the factor Betti
    numbers `genusSurfaceBetti g` and `genusSurfaceBetti h`. -/
def prodSurfaceBetti (g h : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 2 * (g + h)
  | 2 => 2 + 4 * g * h
  | 3 => 2 * (g + h)
  | 4 => 1
  | _ + 5 => 0

/-- `b₀(Σ_g × Σ_h) = 1`: the product of two connected surfaces is connected. -/
@[simp] theorem prodSurfaceBetti_zero (g h : ℕ) : prodSurfaceBetti g h 0 = 1 := rfl

/-- `b₁(Σ_g × Σ_h) = 2(g + h)`: the `H₁` of a product splits as `H₁(Σ_g) ⊕ H₁(Σ_h)`. -/
@[simp] theorem prodSurfaceBetti_one (g h : ℕ) : prodSurfaceBetti g h 1 = 2 * (g + h) := rfl

/-- `b₂(Σ_g × Σ_h) = 2 + 4gh`: the middle Betti number.  The `2` comes from the two
    fundamental classes `[Σ_g] ⊗ 1` and `1 ⊗ [Σ_h]`; the `4gh = (2g)(2h)` from the tensor
    product `H₁(Σ_g) ⊗ H₁(Σ_h)`. -/
@[simp] theorem prodSurfaceBetti_two (g h : ℕ) : prodSurfaceBetti g h 2 = 2 + 4 * g * h := rfl

/-- `b₃(Σ_g × Σ_h) = 2(g + h)`: equal to `b₁` by Poincaré duality on the `4`-manifold. -/
@[simp] theorem prodSurfaceBetti_three (g h : ℕ) : prodSurfaceBetti g h 3 = 2 * (g + h) := rfl

/-- `b₄(Σ_g × Σ_h) = 1`: the top Betti number of the closed oriented `4`-manifold
    `Σ_g × Σ_h`, generated by the product fundamental class `[Σ_g] ⊗ [Σ_h]`. -/
@[simp] theorem prodSurfaceBetti_four (g h : ℕ) : prodSurfaceBetti g h 4 = 1 := rfl

/-- **The explicit Betti numbers satisfy the Künneth formula.**  For every degree `k ≤ 4`,
    `bₖ(Σ_g × Σ_h) = Σ_{i≤k} bᵢ(Σ_g)·b_{k−i}(Σ_h)` — the palindrome `(1, 2(g+h), 2+4gh,
    2(g+h), 1)` really is the convolution of the two factor sequences `(1, 2g, 1)`, so
    `prodSurfaceBetti` carries genuine Künneth content rather than an ad hoc table. -/
theorem prodSurfaceBetti_kunneth (g h : ℕ) {k : ℕ} (hk : k ≤ 4) :
    prodSurfaceBetti g h k
      = kunnethBetti (genusSurfaceBetti g) (genusSurfaceBetti h) k := by
  interval_cases k <;>
    simp only [kunnethBetti, prodSurfaceBetti, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.reduceSub, genusSurfaceBetti_zero, genusSurfaceBetti_one, genusSurfaceBetti_two,
      genusSurfaceBetti_three, genusSurfaceBetti_four] <;> ring

/-- **Poincaré duality for the product `4`-manifold: `bᵢ = b_{4−i}`.**  The Betti sequence
    `(1, 2(g+h), 2+4gh, 2(g+h), 1)` is palindromic — the manifestation of
    `Hᵢ ≅ H_{4−i}` for the closed orientable `4`-manifold `Σ_g × Σ_h`. -/
theorem prodSurfaceBetti_poincare_duality (g h : ℕ) {i : ℕ} (hi : i ≤ 4) :
    prodSurfaceBetti g h i = prodSurfaceBetti g h (4 - i) := by
  interval_cases i <;>
    simp only [Nat.reduceSub, prodSurfaceBetti_zero, prodSurfaceBetti_one,
      prodSurfaceBetti_two, prodSurfaceBetti_three, prodSurfaceBetti_four]

/-- **The middle Betti number `b₂ = 2 + 4gh` is even.**  It is the rank of the (here
    even-dimensional) intersection form on `H₂(Σ_g × Σ_h)`; evenness is forced by the two
    dual fundamental classes plus the symplectic `H₁ ⊗ H₁` block. -/
theorem prodSurface_second_betti_even (g h : ℕ) : Even (prodSurfaceBetti g h 2) :=
  ⟨1 + 2 * g * h, by rw [prodSurfaceBetti_two]; ring⟩

/-- **Euler characteristic of a `4`-manifold from its Betti numbers**:
    `χ = b₀ − b₁ + b₂ − b₃ + b₄`, the Euler–Poincaré alternating sum truncated at
    dimension `4`. -/
def eulerFromBetti4 (b : ℕ → ℕ) : ℤ := (b 0 : ℤ) - b 1 + b 2 - b 3 + b 4

/-- **Total Betti number of a `4`-manifold**: `b₀ + b₁ + b₂ + b₃ + b₄`, the rank of the
    full homology `H_*( · ; ℤ)` (the value of the Poincaré polynomial at `t = 1`). -/
def totalBetti4 (b : ℕ → ℕ) : ℕ := b 0 + b 1 + b 2 + b 3 + b 4

/-- **Künneth ⟹ multiplicativity of χ (homological).**  The Euler–Poincaré sum of the
    Künneth Betti numbers of `Σ_g × Σ_h` equals `(2 − 2g)(2 − 2h)` — the product of the two
    surface Euler characteristics.  This is `χ(M × N) = χ(M)·χ(N)` derived from the graded
    tensor product of homology, independently of the structure field `prodCGB_chi`. -/
theorem prodSurface_euler_poincare (g h : ℕ) :
    eulerFromBetti4 (prodSurfaceBetti g h) = (2 - 2 * (g : ℤ)) * (2 - 2 * (h : ℤ)) := by
  unfold eulerFromBetti4
  rw [prodSurfaceBetti_zero, prodSurfaceBetti_one, prodSurfaceBetti_two,
    prodSurfaceBetti_three, prodSurfaceBetti_four]
  push_cast; ring

/-- **The homological χ agrees with the geometric `prodCGB` χ.**  The Künneth Euler–Poincaré
    value equals `(prodCGB (genusSurfaceCGB g) (genusSurfaceCGB h)).chi`, so Part XVIII
    re-proves `prodCGB_genusSurface_chi` from singular-homology data rather than from the
    Chern-Gauss-Bonnet structure assumption. -/
theorem prodSurface_euler_eq_prodCGB_chi (g h : ℕ) :
    eulerFromBetti4 (prodSurfaceBetti g h)
      = (prodCGB (genusSurfaceCGB g) (genusSurfaceCGB h)).chi := by
  rw [prodCGB_genusSurface_chi, prodSurface_euler_poincare]

/-- **χ factors through the two surface Euler characteristics.**  Restates
    `prodSurface_euler_poincare` as `χ = χ(Σ_g)·χ(Σ_h)` using `genusSurfaceCGB_chi`. -/
theorem prodSurface_euler_factor (g h : ℕ) :
    eulerFromBetti4 (prodSurfaceBetti g h)
      = (genusSurfaceCGB g).chi * (genusSurfaceCGB h).chi := by
  rw [prodSurface_euler_poincare, genusSurfaceCGB_chi, genusSurfaceCGB_chi]

/-- **Total Betti number of `Σ_g × Σ_h` is `(2 + 2g)(2 + 2h)`.**  The total rank multiplies
    under products (Poincaré polynomial at `t = 1`), the counterpart of the alternating sum
    multiplying (`prodSurface_euler_poincare`). -/
theorem prodSurface_betti_total (g h : ℕ) :
    totalBetti4 (prodSurfaceBetti g h) = (2 + 2 * g) * (2 + 2 * h) := by
  unfold totalBetti4
  rw [prodSurfaceBetti_zero, prodSurfaceBetti_one, prodSurfaceBetti_two,
    prodSurfaceBetti_three, prodSurfaceBetti_four]
  ring

/-- **Total Betti multiplies: `Σbₖ(M×N) = (Σbᵢ(M))·(Σbⱼ(N))`.**  Writes the product's total
    Betti number as the product of the factors' total Betti numbers `2 + 2g` and `2 + 2h`
    (`genusSurface_betti_total`). -/
theorem prodSurface_betti_total_eq_prod (g h : ℕ) :
    totalBetti4 (prodSurfaceBetti g h)
      = (genusSurfaceBetti g 0 + genusSurfaceBetti g 1 + genusSurfaceBetti g 2)
        * (genusSurfaceBetti h 0 + genusSurfaceBetti h 1 + genusSurfaceBetti h 2) := by
  rw [prodSurface_betti_total]
  simp only [genusSurfaceBetti_zero, genusSurfaceBetti_one, genusSurfaceBetti_two]
  ring

/-- **`S² × S²`** (`g = h = 0`): Betti numbers `(1, 0, 2, 0, 1)` and `χ = 4`.  The middle
    `b₂ = 2` are the classes `[S²] ⊗ 1` and `1 ⊗ [S²]`; `χ = 4 = χ(S²)²` agrees with
    `sphere_prod_sphere_chi`. -/
theorem prodSurface_sphere_betti_two : prodSurfaceBetti 0 0 2 = 2 := by
  rw [prodSurfaceBetti_two]

/-- Euler characteristic of `S² × S²` from its Betti numbers: `χ = 1 − 0 + 2 − 0 + 1 = 4`. -/
theorem prodSurface_sphere_euler : eulerFromBetti4 (prodSurfaceBetti 0 0) = 4 := by
  rw [prodSurface_euler_poincare]; norm_num

/-- **The `4`-torus `T⁴ = T² × T²`** (`g = h = 1`): middle Betti number `b₂ = 6`.  The full
    Betti sequence is `(1, 4, 6, 4, 1) = (C(4,k))ₖ`, the binomial coefficients — reflecting
    `H_*(T⁴) ≅ Λ*(ℤ⁴)`. -/
theorem prodSurface_torus_betti_two : prodSurfaceBetti 1 1 2 = 6 := by
  rw [prodSurfaceBetti_two]

/-- Euler characteristic of `T⁴` from its Betti numbers: `χ = 1 − 4 + 6 − 4 + 1 = 0` — the
    vanishing Euler characteristic of the flat `4`-torus (`torusCGB`), recovered from the
    binomial Betti sequence `(C(4,k))ₖ`. -/
theorem prodSurface_torus_euler : eulerFromBetti4 (prodSurfaceBetti 1 1) = 0 := by
  rw [prodSurface_euler_poincare]; norm_num

-- ============================================================================
-- Part XIX: The Künneth convolution — commutativity and the point as unit
-- ============================================================================

/-
  Part XVIII computes *one* Künneth convolution `kunnethBetti (genusSurfaceBetti g)
  (genusSurfaceBetti h)` and matches it to the product-surface Betti table.  The convolution
  `kunnethBetti` is, however, a binary operation on Betti sequences in its own right, and it
  carries the algebraic structure behind the symmetric-monoidal product of spaces:

  * it is **commutative**, `b ⋆ c = c ⋆ b` (`kunnethBetti_comm`) — the homological shadow of
    the flip homeomorphism `M × N ≅ N × M` under which the graded tensor product of homology
    is symmetric; and
  * the **point** `δ = (1, 0, 0, …)` (`pointBetti`) is a two-sided **unit**,
    `δ ⋆ c = c = c ⋆ δ` (`kunnethBetti_pointBetti_left`/`_right`) — the homological shadow of
    `pt × M ≅ M`, mirroring `pointCGB` as the identity of the Cartesian-product manifold
    monoid (Part XVII, `prodCGB_point_chi`).

  Together with the (standard, not formalized here) associativity of the Cauchy product these
  exhibit `(Betti sequences, ⋆, δ)` as a commutative monoid, with the Betti-number assignment
  a monoid homomorphism from the product monoid of Part XVII.  The commutativity yields a
  concrete geometric corollary: the product-surface Betti table is symmetric in its two
  genera (`prodSurfaceBetti_comm`), the homological shadow of `Σ_g × Σ_h ≅ Σ_h × Σ_g`.  The
  proofs are finite-sum reindexing over `ℕ`, hence fully verified (0-axiom); the two
  structure-encoded CGB assumptions are not invoked.
-/

/-- **The Künneth convolution is commutative: `b ⋆ c = c ⋆ b`.**  Reindexing the convolution
    sum `∑_{i+j=k} bᵢ·cⱼ` by `i ↦ k − i` swaps the two factors — the algebraic form of the
    homeomorphism `M × N ≅ N × M`, under which the graded tensor product of homology is
    symmetric (no sign, the ranks being unsigned). -/
theorem kunnethBetti_comm (b c : ℕ → ℕ) (k : ℕ) :
    kunnethBetti b c k = kunnethBetti c b k := by
  unfold kunnethBetti
  rw [← Finset.sum_range_reflect (fun i => c i * b (k - i)) (k + 1)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have h1 : k + 1 - 1 - i = k - i := by omega
  have h2 : k - (k - i) = i := by omega
  simp only [h1, h2]
  ring

/-- **Betti sequence of the point** `δ = (1, 0, 0, …)`: `b₀ = 1`, `bᵢ = 0` for `i ≥ 1`.  This
    is the unit of the Künneth convolution, mirroring `pointCGB` as the unit of the
    Cartesian-product manifold monoid (Part XVII). -/
def pointBetti : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0

/-- `b₀(pt) = 1`: the point is a single connected `0`-cell. -/
@[simp] theorem pointBetti_zero : pointBetti 0 = 1 := rfl

/-- `bᵢ(pt) = 0` for `i ≥ 1`: the point has no homology above degree `0`. -/
@[simp] theorem pointBetti_succ (k : ℕ) : pointBetti (k + 1) = 0 := rfl

/-- **The point is a left unit for the Künneth convolution: `δ ⋆ c = c`.**  Only the `i = 0`
    term of `∑_{i} pointBettiᵢ · c_{k−i}` survives (`pointBetti` vanishes off degree `0`),
    leaving `1 · c_k = c_k`.  Homologically, `H_*(pt × M) ≅ H_*(M)`. -/
theorem kunnethBetti_pointBetti_left (c : ℕ → ℕ) (k : ℕ) :
    kunnethBetti pointBetti c k = c k := by
  unfold kunnethBetti
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi0
    cases i with
    | zero => exact absurd rfl hi0
    | succ j => simp
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h

/-- **The point is a right unit for the Künneth convolution: `c ⋆ δ = c`.**  Immediate from
    the left-unit law and commutativity; the point is therefore a genuine two-sided identity,
    the homological shadow of `M × pt ≅ M`. -/
theorem kunnethBetti_pointBetti_right (b : ℕ → ℕ) (k : ℕ) :
    kunnethBetti b pointBetti k = b k := by
  rw [kunnethBetti_comm, kunnethBetti_pointBetti_left]

/-- **The Künneth convolution is associative: `(a ⋆ b) ⋆ c = a ⋆ (b ⋆ c)`.**  The Cauchy
    product `(b ⋆ c)(k) = ∑_{i+j=k} bᵢcⱼ` over `ℕ` is associative — both sides expand to the
    triple sum `∑_{i+j+l=k} aᵢbⱼcₗ`.  Formally, after distributing the outer factor into each
    convolution (`Finset.sum_mul` / `Finset.mul_sum`) both sides become double sums over the
    triangular index sets `{(m,i) : i ≤ m ≤ k}` and `{(i,j) : i+j ≤ k}`, matched by the
    reindexing bijection `(m,i) ↦ (i, m−i)` with inverse `(i,j) ↦ (i+j, i)` (`Finset.sum_bij'`).
    Together with `kunnethBetti_comm` and the two-sided unit `pointBetti`
    (`kunnethBetti_pointBetti_left`/`_right`), this makes `⋆` a commutative-monoid operation on
    Betti sequences — the homological shadow of the associativity of the Cartesian product
    `(M × N) × P ≅ M × (N × P)`. -/
theorem kunnethBetti_assoc (a b c : ℕ → ℕ) (k : ℕ) :
    kunnethBetti (kunnethBetti a b) c k = kunnethBetti a (kunnethBetti b c) k := by
  unfold kunnethBetti
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _ => (⟨x.2, x.1 - x.2⟩ : (_ : ℕ) × ℕ))
    (fun y _ => (⟨y.1 + y.2, y.1⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨i, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy ⊢
    omega
  · rintro ⟨m, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have hm : i + (m - i) = m := by omega
    simp only [hm]
  · rintro ⟨i, j⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_range] at hy
    have hj : i + j - i = j := by omega
    simp only [hj]
  · rintro ⟨m, i⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have hc : k - i - (m - i) = k - m := by omega
    simp only [hc]
    ring

/-- **The product-surface Betti table is symmetric in its genera: `bₖ(Σ_g × Σ_h) =
    bₖ(Σ_h × Σ_g)` for `k ≤ 4`.**  A concrete consequence of the commutativity of the Künneth
    convolution (`kunnethBetti_comm`) applied to `prodSurfaceBetti_kunneth`: the palindrome
    `(1, 2(g+h), 2+4gh, 2(g+h), 1)` is unchanged under `g ↔ h`, the homological shadow of the
    flip homeomorphism `Σ_g × Σ_h ≅ Σ_h × Σ_g`. -/
theorem prodSurfaceBetti_comm (g h : ℕ) {k : ℕ} (hk : k ≤ 4) :
    prodSurfaceBetti g h k = prodSurfaceBetti h g k := by
  rw [prodSurfaceBetti_kunneth g h hk, prodSurfaceBetti_kunneth h g hk, kunnethBetti_comm]
-- Part XX: The Poincaré polynomial of `Σ_g` — functional equation and the
--            connected-sum law with the sphere correction
-- ============================================================================

/-
  The Betti numbers `(b₀, b₁, b₂) = (1, 2g, 1)` of Part XVI are packaged by the
  **Poincaré polynomial**

      P_{Σ_g}(t) = Σᵢ bᵢ tⁱ = 1 + 2g·t + t².

  Two evaluations recover invariants already computed: `P(−1) = 1 − 2g + 1 = 2 − 2g = χ`
  (the Euler–Poincaré formula, `genusSurface_euler_poincare`) and `P(1) = 2 + 2g`, the
  total Betti number (`genusSurface_betti_total`).  The **palindromic** coefficient
  sequence `(1, 2g, 1)` — Poincaré duality `bᵢ = b_{2−i}` — is equivalent to the
  self-reciprocal *functional equation* `t²·P(1/t) = P(t)`.  Finally, connected sum acts
  on Poincaré polynomials by addition minus the sphere polynomial `P_{S²}(t) = 1 + t²`,
  the polynomial refinement of the Euler-characteristic correction `χ(M#N) = χM + χN − 2`
  (`connectedSumCGB_chi`); evaluating that law at `t = −1` returns the χ-law exactly.
  Everything is polynomial arithmetic over `ℝ`, hence 0-axiom.
-/

/-- **The Poincaré polynomial of `Σ_g`**, `P_{Σ_g}(t) = Σᵢ bᵢ tⁱ = 1 + 2g·t + t²`,
    the generating polynomial of the Betti numbers `(b₀, b₁, b₂) = (1, 2g, 1)`. -/
def poincarePoly (g : ℕ) (t : ℝ) : ℝ := 1 + 2 * g * t + t ^ 2

/-- The Poincaré polynomial is the Betti generating function: `P(t) = Σᵢ bᵢ tⁱ`,
    written out over the recorded Betti numbers `genusSurfaceBetti`. -/
theorem poincarePoly_eq_betti_sum (g : ℕ) (t : ℝ) :
    poincarePoly g t
      = (genusSurfaceBetti g 0 : ℝ) + (genusSurfaceBetti g 1 : ℝ) * t
        + (genusSurfaceBetti g 2 : ℝ) * t ^ 2 := by
  simp only [poincarePoly, genusSurfaceBetti_zero, genusSurfaceBetti_one, genusSurfaceBetti_two]
  push_cast; ring

/-- **`P(0) = b₀ = 1`.**  The constant term is the zeroth Betti number: the surface is
    connected. -/
theorem poincarePoly_zero (g : ℕ) : poincarePoly g 0 = 1 := by
  simp [poincarePoly]

/-- **`P(1) = 2 + 2g`, the total Betti number.**  Evaluating the generating polynomial at
    `t = 1` sums the Betti numbers `Σ bᵢ = b₀ + b₁ + b₂` (`genusSurface_betti_total`). -/
theorem poincarePoly_one (g : ℕ) : poincarePoly g 1 = 2 + 2 * g := by
  simp only [poincarePoly]; ring

/-- **`P(1)` equals the total Betti number `b₀ + b₁ + b₂`.**  The bridge from the
    Poincaré-polynomial evaluation to the combinatorial total of `genusSurface_betti_total`. -/
theorem poincarePoly_one_eq_total_betti (g : ℕ) :
    poincarePoly g 1
      = ((genusSurfaceBetti g 0 + genusSurfaceBetti g 1 + genusSurfaceBetti g 2 : ℕ) : ℝ) := by
  rw [poincarePoly_one, genusSurface_betti_total]; push_cast; ring

/-- **`P(−1) = χ(Σ_g)`, the Euler–Poincaré formula.**  Evaluating the Poincaré polynomial
    at `t = −1` forms the alternating sum `Σ (−1)ⁱ bᵢ = 1 − 2g + 1 = 2 − 2g`, the Euler
    characteristic `genusSurfaceCGB_chi`. -/
theorem poincarePoly_neg_one (g : ℕ) :
    poincarePoly g (-1) = ((genusSurfaceCGB g).chi : ℝ) := by
  rw [genusSurfaceCGB_chi]; simp only [poincarePoly]; push_cast; ring

/-- **Functional equation (Poincaré duality): `t²·P(1/t) = P(t)` for `t ≠ 0`.**  The
    palindromic coefficient sequence `(1, 2g, 1)` — the manifestation of `bᵢ = b_{2−i}`
    (`genusSurfaceBetti_poincare_duality`) — makes the Poincaré polynomial self-reciprocal:
    reversing the coefficients (the `t ↦ 1/t`, rescale-by-`t²` operation) returns the same
    polynomial. -/
theorem poincarePoly_functional_eq (g : ℕ) {t : ℝ} (ht : t ≠ 0) :
    t ^ 2 * poincarePoly g (1 / t) = poincarePoly g t := by
  simp only [poincarePoly]
  field_simp
  ring

/-- **Poincaré polynomial of the sphere `S² = Σ_0`: `P_{S²}(t) = 1 + t²`.**  The Betti
    numbers of `S²` are `(1, 0, 1)`, so its Poincaré polynomial has no linear term. -/
theorem poincarePoly_genus_zero (t : ℝ) : poincarePoly 0 t = 1 + t ^ 2 := by
  simp only [poincarePoly]; push_cast; ring

/-- **Connected-sum law for Poincaré polynomials:**
    `P_{Σ_g # Σ_h}(t) = P_{Σ_g}(t) + P_{Σ_h}(t) − (1 + t²)`.
    Because `Σ_g # Σ_h = Σ_{g+h}` (genus additivity, `connectedSum_genusSurface_chi`), the
    left side is `P_{Σ_{g+h}}`.  The subtracted `1 + t² = P_{S²}` is the sphere polynomial:
    a connected sum removes a `2`-disk from each summand and glues along a boundary sphere,
    the polynomial refinement of the Euler-characteristic correction `− χ(S²) = −2`
    (`connectedSumCGB_chi`). -/
theorem poincarePoly_connectedSum (g h : ℕ) (t : ℝ) :
    poincarePoly (g + h) t = poincarePoly g t + poincarePoly h t - (1 + t ^ 2) := by
  simp only [poincarePoly]; push_cast; ring

/-- **The connected-sum polynomial law at `t = −1` is the Euler-characteristic law.**
    Evaluating `poincarePoly_connectedSum` at `t = −1` collapses the sphere polynomial
    `1 + t²` to `2 = χ(S²)`, recovering `χ(Σ_g # Σ_h) = χ(Σ_g) + χ(Σ_h) − 2`
    (`connectedSum_genusSurface_chi`) — so the χ-additivity of connected sum is exactly the
    `t = −1` shadow of the finer Poincaré-polynomial additivity. -/
theorem poincarePoly_connectedSum_chi (g h : ℕ) :
    poincarePoly (g + h) (-1) = poincarePoly g (-1) + poincarePoly h (-1) - 2 := by
  rw [poincarePoly_connectedSum]; norm_num

/-- **First Betti number is additive under connected sum:** `b₁(Σ_g # Σ_h) = b₁(Σ_g) + b₁(Σ_h)`.
    Since `Σ_g # Σ_h = Σ_{g+h}`, this reads `2(g+h) = 2g + 2h` — the homological form of genus
    additivity (`connectedSum_genusSurface_chi`), and the reason the middle coefficient of the
    Poincaré polynomial adds under connected sum while `b₀, b₂` stay pinned at `1`. -/
theorem genusSurfaceBetti_one_connectedSum (g h : ℕ) :
    genusSurfaceBetti (g + h) 1 = genusSurfaceBetti g 1 + genusSurfaceBetti h 1 := by
  simp only [genusSurfaceBetti_one]; ring

end ChernGaussBonnet

end
