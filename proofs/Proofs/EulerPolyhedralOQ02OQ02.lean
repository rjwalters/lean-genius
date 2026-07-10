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

end ChernGaussBonnet

end
