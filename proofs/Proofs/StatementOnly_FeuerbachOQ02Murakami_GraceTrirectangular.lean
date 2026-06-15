/-
Aristotle target for `feuerbachs-theorem-oq-02-murakami` (step S8).

3D Feuerbach analogue (Grace's theorem) for the trirectangular tetrahedron.
Place the right-angle vertex at the origin D = (0,0,0) with mutually
perpendicular legs along the axes:
    A = (a,0,0),  B = (0,b,0),  C = (0,0,c),   a,b,c > 0.

Prior research (S0–S7, fully hand-verified symbolically + numerically; see
`src/data/research/problems/feuerbachs-theorem-oq-02-murakami.json`) proved:
the unique sphere through the opposite face's vertices A, B, C that is
internally tangent to BOTH members of the D-homothety tangent-sphere pair —
the insphere and the D-exsphere — has RATIONAL centre and radius

    Θ = ( (a+b)(a+c), (a+b)(b+c), (a+c)(b+c) ) / (2σ),     σ = a+b+c,
    R = (a² + b² + c² + ab + bc + ca) / (2σ),

while the two tangent spheres carry the surd
    t = √(a²b² + b²c² + c²a²),
    ρ_in  = (ab + bc + ca − t) / (2σ)   (insphere radius, centred at ρ_in·(1,1,1)),
    ρ_ex  = (ab + bc + ca + t) / (2σ)   (D-exsphere radius, centred at ρ_ex·(1,1,1)).

The surd cancels in Θ and R (the 3D analogue of the 2D nine-point centre being
rational in the triangle data). At T0 = (2,3,6) this returns Θ = (40,45,72)/22,
R = 85/22 — the explicitly verified base case. Reference: Maehara & Martini,
"Tangent Spheres of Tetrahedra and a Theorem of Grace", Amer. Math. Monthly
127(10):897–910 (2020), elementary trirectangular proof.

This file states the five defining identities (3 incidence + 2 internal
tangency) as one theorem over real variables with the surd encoded by `t`,
`t² = a²b² + b²c² + c²a²`. The whole statement is a polynomial/field identity:
after clearing the denominator `2σ`, the three incidence identities are pure
ring identities; the two tangency identities reduce to ring identities modulo
the single relation `ht`. UNVERIFIED — authored under a Docker + Aristotle
blackout; proof left as `sorry` for batch search / local build.
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option pp.fullNames true
set_option pp.structureInstances true

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option linter.all false

noncomputable section

namespace FeuerbachOQ02MurakamiStatement

/-- Grace's theorem (3D Feuerbach) for the trirectangular tetrahedron with legs
`a, b, c > 0` at the origin. With centre `Θ = (qx, qy, qz)` and radius `R` as
below, the sphere through `A=(a,0,0)`, `B=(0,b,0)`, `C=(0,0,c)` is internally
tangent to both the insphere (centre `ρin·(1,1,1)`) and the D-exsphere
(centre `ρex·(1,1,1)`), where `t = √(a²b²+b²c²+c²a²)`. -/
theorem grace_feuerbach_trirectangular
    (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : t ^ 2 = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) (ht0 : 0 ≤ t)
    (qx qy qz R ρin ρex : ℝ)
    (hqx : qx = (a + b) * (a + c) / (2 * (a + b + c)))
    (hqy : qy = (a + b) * (b + c) / (2 * (a + b + c)))
    (hqz : qz = (a + c) * (b + c) / (2 * (a + b + c)))
    (hR  : R  = (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) / (2 * (a + b + c)))
    (hρin : ρin = (a * b + b * c + c * a - t) / (2 * (a + b + c)))
    (hρex : ρex = (a * b + b * c + c * a + t) / (2 * (a + b + c))) :
    -- (1) sphere passes through A, B, C
    ((qx - a) ^ 2 + qy ^ 2 + qz ^ 2 = R ^ 2) ∧
    (qx ^ 2 + (qy - b) ^ 2 + qz ^ 2 = R ^ 2) ∧
    (qx ^ 2 + qy ^ 2 + (qz - c) ^ 2 = R ^ 2) ∧
    -- (2) internally tangent to the insphere centred at ρin·(1,1,1)
    ((qx - ρin) ^ 2 + (qy - ρin) ^ 2 + (qz - ρin) ^ 2 = (R - ρin) ^ 2) ∧
    -- (3) internally tangent to the D-exsphere centred at ρex·(1,1,1)
    ((qx - ρex) ^ 2 + (qy - ρex) ^ 2 + (qz - ρex) ^ 2 = (R - ρex) ^ 2) := by
  sorry

-- Proof attempt (scaffolding; Aristotle may ignore or refine):
-- have hσ : a + b + c ≠ 0 := by positivity
-- subst all of hqx hqy hqz hR hρin hρex
-- refine ⟨?_, ?_, ?_, ?_, ?_⟩
-- · -- incidence through A: pure rational identity
--   field_simp; ring
-- · field_simp; ring            -- through B
-- · field_simp; ring            -- through C
-- · -- tangency to insphere: identity modulo ht (t² = a²b²+b²c²+c²a²)
--   field_simp
--   linear_combination (..coeff in a,b,c..) * ht
-- · field_simp                  -- tangency to D-exsphere (n -> -n symmetric)
--   linear_combination (..coeff in a,b,c..) * ht
-- The even-in-t cancellation (odd-in-t part ≡ 0; even part forces the shared
-- pencil constant G = abc/σ) is what makes (2) and (3) hold for the SAME Θ, R.

end FeuerbachOQ02MurakamiStatement
