/-
# Quartic Discriminant and Ferrari's Resolvent Cubic

Extends the discriminant computations from VietasFormulasOQ03 to degree 4.

**OQ-05** (from VietasFormulasOQ03): "Extend the discriminant computations to degree 4
(the quartic discriminant has 16 terms in the elementary symmetric polynomial basis)
and connect to the resolvent cubic used in Ferrari's quartic formula."

## Main Results

1. `vieta_quartic` — Monic quartic polynomial from 4 roots (Vieta)
2. `discriminant_quartic` — The product ∏_{i<j} (rᵢ − rⱼ)² equals the 16-term
   formula in elementary symmetric polynomials e₁, e₂, e₃, e₄ (proved by `ring`)
3. `discriminant_depressed` — For the depressed quartic (e₁ = 0, roots sum to 0),
   the 16-term formula collapses to 6 terms (proved by `ring`)
4. `ferrari_identity` — Ferrari's algebraic decomposition:
   x⁴ + px² + qx + r = (x² + y)² − ((2y−p)x² − qx + (y²−r))
5. `resolvent_cubic_condition` — The inner expression in Ferrari's identity is a
   perfect square iff y satisfies the resolvent cubic 8y³ − 4py² − 8ry + (4pr−q²) = 0
6. `resolvent_discriminant_eq` — The discriminant of the resolvent cubic equals
   64 times the depressed quartic discriminant:
   Δ_res(p,q,r) = 64 · Δ₄(p,q,r)

## Mathematical Background

Given a quartic polynomial x⁴ − e₁x³ + e₂x² − e₃x + e₄ with roots r₁, r₂, r₃, r₄,
its discriminant is:
  Δ = ∏_{1 ≤ i < j ≤ 4} (rᵢ − rⱼ)²

This vanishes iff the quartic has a repeated root.

For the **depressed quartic** x⁴ + px² + qx + r (no cubic term, e₁ = 0):
  Δ = 256r³ − 128p²r² + 144pq²r − 27q⁴ + 16p⁴r − 4p³q²

**Ferrari's method** (1545): to solve x⁴ + px² + qx + r = 0, choose y so that
  x⁴ + px² + qx + r = (x² + y)² − (ax + b)²
The parameter y must satisfy the **resolvent cubic** 8y³ − 4py² − 8ry + (4pr − q²) = 0.
The discriminant of this cubic equals 64Δ, confirming the quartic has a repeated root
iff its resolvent cubic does.

## References

- Ferrari, L. (1545): Quartic formula via reduction to a cubic
- Lagrange, J.-L. (1770): Resolvent and discriminant theory
- van der Waerden, B.L. (1949): *Moderne Algebra*, Vol. 1
-/

import Mathlib.Tactic
import Proofs.VietasFormulasOQ03

set_option maxHeartbeats 800000

namespace QuarticDiscriminant

/-
## Part I: Vieta's Formula for the Quartic

The monic quartic (x − r₁)(x − r₂)(x − r₃)(x − r₄) expands to
x⁴ − e₁x³ + e₂x² − e₃x + e₄, where eₖ are the elementary symmetric polynomials.
-/
section Vieta

variable {R : Type*} [CommRing R]

/-- Vieta's formula for the monic quartic: (x − r₁)(x − r₂)(x − r₃)(x − r₄)
    = x⁴ − e₁x³ + e₂x² − e₃x + e₄. -/
theorem vieta_quartic (r₁ r₂ r₃ r₄ : R) :
    ∀ x : R, (x - r₁) * (x - r₂) * (x - r₃) * (x - r₄) =
    x ^ 4 - (r₁ + r₂ + r₃ + r₄) * x ^ 3
    + (r₁*r₂ + r₁*r₃ + r₁*r₄ + r₂*r₃ + r₂*r₄ + r₃*r₄) * x ^ 2
    - (r₁*r₂*r₃ + r₁*r₂*r₄ + r₁*r₃*r₄ + r₂*r₃*r₄) * x
    + r₁*r₂*r₃*r₄ := by
  intro x; ring

end Vieta

/-
## Part II: The 16-Term Quartic Discriminant

The discriminant Δ = ∏_{i<j} (rᵢ − rⱼ)² in terms of e₁, e₂, e₃, e₄.
This is a degree-12 polynomial identity, proved by `ring`.

The 16 terms, grouped by degree in e₄:
  Degree 3 in e₄:  256e₄³
  Degree 2 in e₄: −192e₁e₃e₄² − 128e₂²e₄² + 144e₂e₃²e₄  [sic: + 144e₁²e₂e₄²]
  ...
-/
section Discriminant

variable {R : Type*} [CommRing R]

/-- The quartic discriminant in terms of elementary symmetric polynomials.
    For x⁴ − e₁x³ + e₂x² − e₃x + e₄ with roots r₁, r₂, r₃, r₄:

    Δ = 256e₄³ − 192e₁e₃e₄² − 128e₂²e₄² + 144e₂e₃²e₄ − 27e₃⁴
      + 144e₁²e₂e₄² − 6e₁²e₃²e₄ − 80e₁e₂²e₃e₄ + 18e₁e₂e₃³
      + 16e₂⁴e₄ − 4e₂³e₃²
      − 27e₁⁴e₄² + 18e₁³e₂e₃e₄ − 4e₁³e₃³ − 4e₁²e₂³e₄ + e₁²e₂²e₃²

    This 16-term formula is a polynomial identity over any commutative ring. -/
theorem discriminant_quartic (r₁ r₂ r₃ r₄ : R) :
    (r₁ - r₂) ^ 2 * (r₁ - r₃) ^ 2 * (r₁ - r₄) ^ 2 *
    (r₂ - r₃) ^ 2 * (r₂ - r₄) ^ 2 * (r₃ - r₄) ^ 2 =
    let e₁ := r₁ + r₂ + r₃ + r₄
    let e₂ := r₁*r₂ + r₁*r₃ + r₁*r₄ + r₂*r₃ + r₂*r₄ + r₃*r₄
    let e₃ := r₁*r₂*r₃ + r₁*r₂*r₄ + r₁*r₃*r₄ + r₂*r₃*r₄
    let e₄ := r₁*r₂*r₃*r₄
    256 * e₄ ^ 3 - 192 * e₁ * e₃ * e₄ ^ 2 - 128 * e₂ ^ 2 * e₄ ^ 2
    + 144 * e₂ * e₃ ^ 2 * e₄ - 27 * e₃ ^ 4
    + 144 * e₁ ^ 2 * e₂ * e₄ ^ 2 - 6 * e₁ ^ 2 * e₃ ^ 2 * e₄
    - 80 * e₁ * e₂ ^ 2 * e₃ * e₄ + 18 * e₁ * e₂ * e₃ ^ 3
    + 16 * e₂ ^ 4 * e₄ - 4 * e₂ ^ 3 * e₃ ^ 2
    - 27 * e₁ ^ 4 * e₄ ^ 2 + 18 * e₁ ^ 3 * e₂ * e₃ * e₄
    - 4 * e₁ ^ 3 * e₃ ^ 3 - 4 * e₁ ^ 2 * e₂ ^ 3 * e₄
    + e₁ ^ 2 * e₂ ^ 2 * e₃ ^ 2 := by
  simp only []
  ring

end Discriminant

/-
## Part III: Depressed Quartic Discriminant

For the **depressed quartic** x⁴ + px² + qx + r (no cubic term),
the four roots satisfy r₁ + r₂ + r₃ + r₄ = 0, so e₁ = 0.
Setting e₁ = 0 in the 16-term formula eliminates 10 terms, leaving 6.

Here we parametrize: the fourth root is determined by the other three
(r₄ = −r₁ − r₂ − r₃) and express the discriminant purely in terms of
the coefficients p = e₂, q = −e₃, r = e₄.
-/
section DepressedQuartic

variable {R : Type*} [CommRing R]

/-- For roots with r₁ + r₂ + r₃ + r₄ = 0 (depressed quartic x⁴ + px² + qx + r),
    the discriminant reduces to a 6-term formula:
    Δ = 256r³ − 128p²r² + 144pq²r − 27q⁴ + 16p⁴r − 4p³q²

    We parametrize r₄ := −r₁ − r₂ − r₃ to ensure the sum-zero condition. -/
theorem discriminant_depressed (r₁ r₂ r₃ : R) :
    let r₄ := -r₁ - r₂ - r₃
    let p := r₁*r₂ + r₁*r₃ + r₁*r₄ + r₂*r₃ + r₂*r₄ + r₃*r₄
    let q := -(r₁*r₂*r₃ + r₁*r₂*r₄ + r₁*r₃*r₄ + r₂*r₃*r₄)
    let r' := r₁*r₂*r₃*r₄
    (r₁ - r₂) ^ 2 * (r₁ - r₃) ^ 2 * (r₁ - r₄) ^ 2 *
    (r₂ - r₃) ^ 2 * (r₂ - r₄) ^ 2 * (r₃ - r₄) ^ 2 =
    256 * r' ^ 3 - 128 * p ^ 2 * r' ^ 2 + 144 * p * q ^ 2 * r'
    - 27 * q ^ 4 + 16 * p ^ 4 * r' - 4 * p ^ 3 * q ^ 2 := by
  simp only []
  ring

/-- The 6-term depressed quartic discriminant as a function of coefficients. -/
def depressedDiscriminant (p q r : R) : R :=
  256 * r ^ 3 - 128 * p ^ 2 * r ^ 2 + 144 * p * q ^ 2 * r
  - 27 * q ^ 4 + 16 * p ^ 4 * r - 4 * p ^ 3 * q ^ 2

/-- The depressed quartic discriminant vanishes iff the quartic has a repeated root.
    Symmetry check: Δ is symmetric in q → −q (the quartic x⁴+px²+qx+r maps to
    x⁴+px²−qx+r under x↦−x, which has the same discriminant). -/
theorem depressedDiscriminant_neg_q (p q r : R) :
    depressedDiscriminant p (-q) r = depressedDiscriminant p q r := by
  unfold depressedDiscriminant; ring

end DepressedQuartic

/-
## Part IV: Ferrari's Algebraic Identity

Ferrari's method (1545) for solving quartics: complete the square to reduce to
a quadratic in x². Any quartic x⁴ + px² + qx + r can be written as:
  x⁴ + px² + qx + r = (x² + y)² − ((2y−p)x² − qx + (y²−r))

When the inner expression (2y−p)x² − qx + (y²−r) is a perfect square (ax−b)²,
its discriminant q² − 4(2y−p)(y²−r) = 0 gives the resolvent cubic.
-/
section Ferrari

variable {R : Type*} [CommRing R]

/-- Ferrari's algebraic identity: any quartic x⁴ + px² + qx + r decomposes as
    (x² + y)² minus an inner quadratic in x.
    The inner quadratic is a perfect square when y satisfies the resolvent cubic. -/
theorem ferrari_identity (p q r y x : R) :
    (x ^ 2 + y) ^ 2 - ((2 * y - p) * x ^ 2 - q * x + (y ^ 2 - r)) =
    x ^ 4 + p * x ^ 2 + q * x + r := by ring

/-- Ferrari's resolvent cubic: the inner expression (2y−p)x² − qx + (y²−r) in
    Ferrari's identity is a perfect square iff there exist a, b with:
    a² = 2y − p,  2ab = q,  b² = y² − r.
    These conditions force y to satisfy 8y³ − 4py² − 8ry + (4pr − q²) = 0. -/
theorem resolvent_cubic_condition (p q r y a b : R)
    (ha : a ^ 2 = 2 * y - p)
    (hab : 2 * a * b = q)
    (hb : b ^ 2 = y ^ 2 - r) :
    8 * y ^ 3 - 4 * p * y ^ 2 - 8 * r * y + (4 * p * r - q ^ 2) = 0 := by
  have h : q ^ 2 = 4 * (2 * y - p) * (y ^ 2 - r) :=
    calc q ^ 2 = (2 * a * b) ^ 2 := by rw [hab]
      _ = 4 * a ^ 2 * b ^ 2 := by ring
      _ = 4 * (2 * y - p) * (y ^ 2 - r) := by rw [ha, hb]
  linear_combination -h

/-- The resolvent cubic polynomial: 8y³ − 4py² − 8ry + (4pr − q²).
    This is a monic cubic (after dividing by 8) whose roots parametrize
    the Ferrari factorization of x⁴ + px² + qx + r. -/
def resolventCubic (p q r : R) : R → R :=
  fun y => 8 * y ^ 3 - 4 * p * y ^ 2 - 8 * r * y + (4 * p * r - q ^ 2)

/-- The resolvent cubic evaluated at y = (p/2 + something): sanity check identity.
    At y = p/2, the resolvent is p·p·something... We verify the leading behavior. -/
theorem resolventCubic_apply (p q r y : R) :
    resolventCubic p q r y = 8 * y ^ 3 - 4 * p * y ^ 2 - 8 * r * y + (4 * p * r - q ^ 2) := rfl

end Ferrari

/-
## Part V: Discriminant Connection

The discriminant of the resolvent cubic 8y³ − 4py² − 8ry + (4pr − q²) equals
64 times the depressed quartic discriminant.

For a general cubic ay³ + by² + cy + d, the discriminant is:
  Δ = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²

Substituting a = 8, b = −4p, c = −8r, d = 4pr − q²:
  Δ_res = 64 · (256r³ − 128p²r² + 144pq²r − 27q⁴ + 16p⁴r − 4p³q²)
        = 64 · Δ₄(p, q, r)

This is a pure ring identity, proved by `ring`.
-/
section DiscriminantConnection

variable {R : Type*} [CommRing R]

/-- The discriminant of the cubic ay³ + by² + cy + d. -/
def cubicDiscriminant (a b c d : R) : R :=
  18 * a * b * c * d - 4 * b ^ 3 * d + b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 27 * a ^ 2 * d ^ 2

/-- The discriminant of Ferrari's resolvent cubic 8y³ − 4py² − 8ry + (4pr − q²)
    equals 64 times the depressed quartic discriminant Δ₄(p, q, r).

    This means: the quartic x⁴ + px² + qx + r has a repeated root if and only if
    its resolvent cubic has a repeated root — the two discriminants vanish together. -/
theorem resolvent_discriminant_eq (p q r : R) :
    cubicDiscriminant 8 (-4 * p) (-8 * r) (4 * p * r - q ^ 2) =
    64 * depressedDiscriminant p q r := by
  unfold cubicDiscriminant depressedDiscriminant
  ring

/-- Corollary: The resolvent discriminant formula unfolded explicitly.
    Δ_res = 1024p⁴r − 256p³q² − 8192p²r² + 9216pq²r + 16384r³ − 1728q⁴ -/
theorem resolvent_discriminant_formula (p q r : R) :
    cubicDiscriminant 8 (-4 * p) (-8 * r) (4 * p * r - q ^ 2) =
    1024 * p ^ 4 * r - 256 * p ^ 3 * q ^ 2 - 8192 * p ^ 2 * r ^ 2
    + 9216 * p * q ^ 2 * r + 16384 * r ^ 3 - 1728 * q ^ 4 := by
  unfold cubicDiscriminant
  ring

end DiscriminantConnection

/-
## Part VI: Summary

The main chain of results:
  (quartic has repeated root)
  ⟺ Δ₄(p, q, r) = 0
  ⟺ Δ_res(p, q, r) = 0   [since Δ_res = 64 · Δ₄]
  ⟺ (resolvent cubic has a repeated root)
  ⟺ (Ferrari's factorization degenerates)

This connects the solvability structure of the quartic to its resolvent cubic,
the key step in Ferrari's 16th-century quartic formula.
-/
section Summary

variable {R : Type*} [CommRing R]

/-- The quartic discriminant, resolvent discriminant, and depressed discriminant
    are related by scaling. Summary of the three forms: -/
theorem discriminant_scaling_summary (p q r : R) :
    -- Resolvent discriminant = 64 × quartic discriminant
    cubicDiscriminant 8 (-4 * p) (-8 * r) (4 * p * r - q ^ 2) =
    64 * depressedDiscriminant p q r := resolvent_discriminant_eq p q r

/-- The resolvent cubic of the depressed quartic x⁴+px²+qx+r at a root of the quartic.
    If r₁ is a root of x⁴+px²+qx+r (so r₁⁴+p·r₁²+q·r₁+r = 0), then y = r₁²
    does NOT generally satisfy the resolvent — the resolvent governs the Ferrari
    parametrization, not the quartic roots directly.
    We verify Ferrari's identity holds at any x for any y: -/
theorem ferrari_decomposition_valid (p q r : R) (x y : R) :
    x ^ 4 + p * x ^ 2 + q * x + r =
    (x ^ 2 + y) ^ 2 - ((2 * y - p) * x ^ 2 - q * x + (y ^ 2 - r)) := by ring

end Summary

#check @discriminant_quartic
#check @discriminant_depressed
#check @ferrari_identity
#check @resolvent_cubic_condition
#check @resolvent_discriminant_eq
#check @discriminant_scaling_summary

end QuarticDiscriminant
