/-
Follow-up (`feuerbachs-theorem-oq-02-murakami-oq-01`) to the verified entry
`feuerbachs-theorem-oq-02-murakami` (Grace's 3D Feuerbach theorem for the
trirectangular tetrahedron).

## The question

The parent entry proves that the Grace sphere through the opposite-face
vertices A, B, C of the trirectangular tetrahedron
    A = (a,0,0),  B = (0,b,0),  C = (0,0,c),  D = 0   (a,b,c > 0)
has a RATIONAL centre Θ and radius R, while the two tangent spheres of the
D-homothety pair — the insphere and the D-exsphere — carry the surd
    t = √(a²b² + b²c² + c²a²):
    ρin = (ab + bc + ca − t) / (2σ),   ρex = (ab + bc + ca + t) / (2σ),
    σ = a + b + c.
The parent observes that the surd "cancels" in Θ and R, but does not isolate
the algebraic reason. This entry does: it identifies the exact quadratic
whose two roots are ρin and ρex.

## The answer

`ρin` and `ρex` are the two conjugate roots of the RATIONAL quadratic
    2σ · x² − 2(ab + bc + ca) · x + abc = 0.
Consequently every symmetric function of the pair is surd-free:
    ρin + ρex = (ab + bc + ca) / σ            (rational),
    ρin · ρex = abc / (2σ)                     (rational),
    ρex − ρin = t / σ                          (the surd, an antisymmetric fn).
The product identity is the crux: `ρin · ρex = (e² − t²)/(2σ)²` with
`e = ab + bc + ca`, and the surd relation `t² = a²b² + b²c² + c²a²` gives the
pure ring identity `e² − t² = 2σ·abc` (equivalently `e² − t² = 2·e₁·e₃`, twice
the product of the first and third elementary symmetric polynomials). This is
the 3D echo of the classical fact that in 2D the inradius/exradius products are
rational in the triangle data. The involution t ↦ −t swaps ρin ↔ ρex, which is
exactly why the SAME Grace centre Θ and radius R are internally tangent to both
(the odd-in-t part of each tangency residual vanishes — see the parent).

## Sanity check

At the parent's base point (a,b,c) = (2,3,6): e = 36, σ = 11, t = √504 = 6√14.
    ρin + ρex = 72/22 = 36/11 = e/σ,
    ρin · ρex = (36² − 504)/22² = 792/484 = 18/11 = abc/(2σ),
both surd-free, as claimed.

## Proof discipline (inherited from the parent)

All five identities are polynomial/field identities. Clear the shared
denominator with `field_simp` (σ ≠ 0 by positivity), then close: the sum and
difference are pure `ring` identities (t enters linearly and cancels), while
the product and the two root identities reduce to `ring` modulo the single
surd relation `ht : t² = a²b² + b²c² + c²a²` and so close by
`linear_combination` with an integer-times-σ coefficient.
-/
import Mathlib

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 400000
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.all false

noncomputable section

namespace FeuerbachOQ02MurakamiOQ01

/-- **Conjugate radii of Grace's tangent-sphere pair.** For the trirectangular
tetrahedron with legs `a, b, c > 0`, the insphere radius `ρin` and D-exsphere
radius `ρex` (which individually carry the surd `t = √(a²b²+b²c²+c²a²)`) are the
two roots of the rational quadratic `2σ·x² − 2(ab+bc+ca)·x + abc = 0`, `σ = a+b+c`.
Hence their sum and product are surd-free while their difference is the surd. -/
theorem grace_radii_conjugate
    (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) (ht0 : 0 ≤ t)
    (ρin ρex : ℝ)
    (hρin : ρin = (a * b + b * c + c * a - t) / (2 * (a + b + c)))
    (hρex : ρex = (a * b + b * c + c * a + t) / (2 * (a + b + c))) :
    -- (1) the sum is rational (surd-free)
    (ρin + ρex = (a * b + b * c + c * a) / (a + b + c)) ∧
    -- (2) the product is rational (surd-free): the crux e² − t² = 2σ·abc
    (ρin * ρex = a * b * c / (2 * (a + b + c))) ∧
    -- (3) the difference is exactly the surd t/σ (antisymmetric under t ↦ −t)
    (ρex - ρin = t / (a + b + c)) ∧
    -- (4) ρin is a root of the rational quadratic 2σ·x² − 2(ab+bc+ca)·x + abc
    (2 * (a + b + c) * ρin ^ 2 - 2 * (a * b + b * c + c * a) * ρin + a * b * c = 0) ∧
    -- (5) ρex is the conjugate root of the same rational quadratic
    (2 * (a + b + c) * ρex ^ 2 - 2 * (a * b + b * c + c * a) * ρex + a * b * c = 0) := by
  have hσ : a + b + c ≠ 0 := by positivity
  subst hρin hρex
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- sum: t cancels linearly
    field_simp
    ring
  · -- product: (e−t)(e+t) = e² − t² = 2σ·abc modulo ht
    field_simp
    linear_combination (-2 * (a + b + c)) * ht
  · -- difference: 2t/(2σ) = t/σ, pure ring after clearing
    field_simp
    ring
  · -- ρin a root: numerator collapses to t² − (a²b²+b²c²+c²a²)
    field_simp
    linear_combination ht
  · -- ρex the conjugate root: same residual by t ↦ −t symmetry
    field_simp
    linear_combination ht

/-- The rational quadratic `2σ·x² − 2(ab+bc+ca)·x + abc` has `ρin, ρex` as its
roots, so its two symmetric functions are exactly the surd-free sum and product
above. Restated as an explicit factorisation over `ℝ` valid for all `x`. -/
theorem grace_radii_factorisation
    (a b c t x : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)
    (ρin ρex : ℝ)
    (hρin : ρin = (a * b + b * c + c * a - t) / (2 * (a + b + c)))
    (hρex : ρex = (a * b + b * c + c * a + t) / (2 * (a + b + c))) :
    2 * (a + b + c) * (x - ρin) * (x - ρex)
      = 2 * (a + b + c) * x ^ 2 - 2 * (a * b + b * c + c * a) * x + a * b * c := by
  have hσ : a + b + c ≠ 0 := by positivity
  subst hρin hρex
  field_simp
  linear_combination (-2 * (a + b + c)) * ht

end FeuerbachOQ02MurakamiOQ01
