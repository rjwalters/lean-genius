/-
Erdős #101 OQ-04 — the rational (Diophantine) layer of the four-point-line conic.

The four-point lines of the quartic `y = x⁴ − 5x²` are governed (via
`four_onQuartic_collinear_iff_sq` in `Proofs.Erdos101OQ04`) by the fixed ternary
conic

    Q(p, q, r) = p² + q² + r² + pq + qr + rp = 5,

the fourth abscissa being `−(p+q+r)`.  Prior sessions pinned the *metric* geometry
of `Q = 5`: it is a positive-definite ellipsoidal shell with squared abscissa radius
confined to `[5/2, 10]`, both endpoints attained (`ternary_conic_*` family).  Its
*arithmetic* geometry, however, was represented only by isolated witnesses — the
irrational endpoints `(√5, −√5, 0)`, `(√(5/6), √(5/6), √(5/6))`, and the single
rational oblique point `(−8/3, 1/3, 1)`.

This file adds the missing Diophantine tool.  A conic carrying one rational point is
rationally parametrized: every rational secant through a rational base point meets the
conic again in a rational point.  We prove the general secant identity
`ternary_conic_secant` (division-free, so it applies over any field), then use it to
produce a *second, structurally distinct* rational four-point line
`(−7/3, 2, −1/3, 2/3)` — genuinely oblique (its abscissa set is not closed under
negation) and disjoint from the earlier witness — witnessing that the parametrization
escapes both the symmetric circle `q = −p` and the single previously-known oblique
point.

Scope honesty.  This is the arithmetic-structure layer of the quartic construction; it
does **not** touch the OPEN super-linear-growth obligation
`solymosi_stojakovic_lower_bound`.  That bound is achieved by a random projection of a
high-dimensional grid, not by the quartic; the quartic route delivers only the
unconditional `Ω(n)` floor.  What the secant parametrization does supply is the
mechanism (rational points dense on the conic) any *explicit* rational/integer
construction would build on.

References
----------
* J. Solymosi and M. Stojaković, *Combinatorica* 33 (2013), 247–258.
* Parent file `Proofs.Erdos101OQ04` for the quartic ↔ conic reduction.
-/

import Proofs.Erdos101OQ04

namespace Erdos101OQ04

open Classical

/-! ### Rational parametrization of the four-point-line conic `Q = 5`

The conic `Q(p,q,r) = p²+q²+r²+pq+qr+rp = 5` is a smooth quadric.  Given a base point
`(a₀,b₀,c₀)` on it and a direction `(da,db,dc)`, the line `t ↦ (a₀,b₀,c₀) + t·(da,db,dc)`
meets `Q = 5` at `t = 0` and at one further parameter `τ`.  Writing
`Q((a₀,b₀,c₀)+t·d) = Q₀ + t·N + t²·Q_d` with

  * `N = (2a₀+b₀+c₀)·da + (2b₀+a₀+c₀)·db + (2c₀+a₀+b₀)·dc`  (the directional gradient),
  * `Q_d = da²+db²+dc²+da·db+db·dc+dc·da`                    (the form on the direction),

the second intersection is the root `τ = −N / Q_d`.  We record the *division-free* form
of this fact — hypothesis `hsec : τ · Q_d = −N` — so the statement is a polynomial
identity valid over any commutative ring, and rational data in `(a₀,b₀,c₀,da,db,dc)`
forces `τ`, hence the new point, to be rational. -/

/-- **Secant parametrization of the ternary conic `Q = 5`.**
If `(a₀,b₀,c₀)` lies on `Q = 5` and `τ` satisfies the secant relation
`τ·Q_d = −N` (with `N` the directional gradient and `Q_d` the form on the direction
`(da,db,dc)`), then the secant point `(a₀,b₀,c₀) + τ·(da,db,dc)` also lies on `Q = 5`.

Proof is the pure polynomial identity `Q(P₀+τd) = Q(P₀) + τ·N + τ²·Q_d`: substituting
`Q(P₀) = 5` and `τ²·Q_d = τ·(τ·Q_d) = τ·(−N)` collapses the `τ·N` terms.  Since the
conic already carries the rational point `(−8/3, 1/3, 1)`, this exhibits `Q = 5` as
rationally parametrized — infinitely many rational four-point lines lie on the quartic
`y = x⁴ − 5x²`. -/
theorem ternary_conic_secant
    (a₀ b₀ c₀ da db dc τ : ℝ)
    (hbase : a₀ ^ 2 + b₀ ^ 2 + c₀ ^ 2 + a₀ * b₀ + b₀ * c₀ + c₀ * a₀ = 5)
    (hsec : τ * (da ^ 2 + db ^ 2 + dc ^ 2 + da * db + db * dc + dc * da)
              = -((2 * a₀ + b₀ + c₀) * da + (2 * b₀ + a₀ + c₀) * db
                    + (2 * c₀ + a₀ + b₀) * dc)) :
    (a₀ + τ * da) ^ 2 + (b₀ + τ * db) ^ 2 + (c₀ + τ * dc) ^ 2
        + (a₀ + τ * da) * (b₀ + τ * db) + (b₀ + τ * db) * (c₀ + τ * dc)
        + (c₀ + τ * dc) * (a₀ + τ * da) = 5 := by
  linear_combination hbase + τ * hsec

/-! ### A second rational oblique four-point line, obtained by a secant

Starting from the *integer* conic point `(−1, 2, 1)` (which is the symmetric quadruple
`{−2,−1,1,2}` under `x₃ = −(p+q+r)`), take the direction `(1, 0, 1)`.  The directional
gradient is `N = (2·(−1)+2+1)·1 + 0 + (2·1+(−1)+2)·1 = 1 + 3 = 4` and the form on the
direction is `Q_d = 1²+0²+1²+1·0+0·1+1·1 = 3`, so the secant parameter is
`τ = −4/3`.  The second intersection is

    (−1, 2, 1) + (−4/3)·(1, 0, 1) = (−7/3, 2, −1/3),

a *rational, oblique* point of `Q = 5`.  Its four-point-line quadruple is
`(−7/3, 2, −1/3, 2/3)`. -/

/-- **The secant from `(−1,2,1)` in direction `(1,0,1)` lands on `Q = 5`.**
Direct instantiation of `ternary_conic_secant` with `τ = −4/3`; the base and secant
relations are closed by `norm_num`.  The resulting point is `(−7/3, 2, −1/3)`. -/
theorem new_oblique_point_via_secant :
    ((-1 : ℝ) + (-4 / 3) * 1) ^ 2 + ((2 : ℝ) + (-4 / 3) * 0) ^ 2
        + ((1 : ℝ) + (-4 / 3) * 1) ^ 2
        + ((-1 : ℝ) + (-4 / 3) * 1) * ((2 : ℝ) + (-4 / 3) * 0)
        + ((2 : ℝ) + (-4 / 3) * 0) * ((1 : ℝ) + (-4 / 3) * 1)
        + ((1 : ℝ) + (-4 / 3) * 1) * ((-1 : ℝ) + (-4 / 3) * 1) = 5 :=
  ternary_conic_secant (-1) 2 1 1 0 1 (-4 / 3) (by norm_num) (by norm_num)

/-- **The new oblique triple `(−7/3, 2, −1/3)` lies on the ternary conic `Q = 5`.**
The clean-coordinate form of `new_oblique_point_via_secant`. -/
theorem new_oblique_triple_on_ternary_conic :
    (-7 / 3 : ℝ) ^ 2 + (2 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2
        + (-7 / 3 : ℝ) * 2 + (2 : ℝ) * (-1 / 3) + (-1 / 3 : ℝ) * (-7 / 3) = 5 := by
  norm_num

/-- **The new oblique quadruple satisfies the arithmetic four-point-line criterion.**
The four abscissae `(−7/3, 2, −1/3, 2/3)` (the fourth `2/3 = −(−7/3 + 2 − 1/3)`) obey
`Σx = 0` and `Σx² = 10` — the two Vieta/sum-of-squares relations that a four-point line
on `y = x⁴ − 5x²` must meet.  The oblique analogue of `oblique_quadruple_criterion`. -/
theorem new_oblique_quadruple_criterion :
    (-7 / 3 : ℝ) + 2 + (-1 / 3) + 2 / 3 = 0 ∧
      (-7 / 3 : ℝ) ^ 2 + (2 : ℝ) ^ 2 + (-1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 = 10 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **The new quadruple is genuinely oblique (not a symmetric `(a,−a,b,−b)` shape).**
A symmetric quadruple has an abscissa set closed under negation.  Here the abscissa `2`
is present but its negation `−2` equals none of `−7/3, 2, −1/3, 2/3`, so no symmetric
relabeling exists — the quadruple is strictly oblique, off the circle slice `q = −p`. -/
theorem new_oblique_quadruple_not_symmetric :
    (-(2 : ℝ) ≠ -7 / 3) ∧ (-(2 : ℝ) ≠ 2) ∧ (-(2 : ℝ) ≠ -1 / 3) ∧ (-(2 : ℝ) ≠ 2 / 3) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The new four-point line is distinct from the earlier oblique witness.**
The abscissa `−7/3` of the new quadruple `(−7/3, 2, −1/3, 2/3)` equals none of the
abscissae `−8/3, 1/3, 1, 4/3` of the previously-known oblique quadruple
(`oblique_quadruple_criterion`).  Hence the two are genuinely different four-point
lines, not a relabeling of one another — the secant construction produces new lines. -/
theorem new_oblique_quadruple_distinct_from_witness :
    (-7 / 3 : ℝ) ≠ -8 / 3 ∧ (-7 / 3 : ℝ) ≠ 1 / 3 ∧ (-7 / 3 : ℝ) ≠ 1 ∧ (-7 / 3 : ℝ) ≠ 4 / 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The new oblique quadruple forms a four-point line on the quartic.**
For the four distinct abscissae `−7/3, 2, −1/3, 2/3`, the four points above them on
`y = x⁴ − 5x²` are collinear — a genuine four-point line anchored through the `(−7/3, ·)`
and `(2, ·)` points.  Derived from the sum-of-squares criterion
`four_onQuartic_collinear_iff_sq` via `new_oblique_quadruple_criterion`; this is a second
explicit oblique witness, produced by the rational secant `ternary_conic_secant`. -/
theorem new_oblique_quadruple_onQuartic_collinear :
    collinear (-7 / 3, (-7 / 3 : ℝ) ^ 4 - 5 * (-7 / 3) ^ 2)
        (2, (2 : ℝ) ^ 4 - 5 * 2 ^ 2)
        (-1 / 3, (-1 / 3 : ℝ) ^ 4 - 5 * (-1 / 3) ^ 2) ∧
      collinear (-7 / 3, (-7 / 3 : ℝ) ^ 4 - 5 * (-7 / 3) ^ 2)
        (2, (2 : ℝ) ^ 4 - 5 * 2 ^ 2)
        (2 / 3, (2 / 3 : ℝ) ^ 4 - 5 * (2 / 3) ^ 2) := by
  rw [four_onQuartic_collinear_iff_sq
      (show onQuartic (-7 / 3, (-7 / 3 : ℝ) ^ 4 - 5 * (-7 / 3) ^ 2) from rfl)
      (show onQuartic (2, (2 : ℝ) ^ 4 - 5 * 2 ^ 2) from rfl)
      (show onQuartic (-1 / 3, (-1 / 3 : ℝ) ^ 4 - 5 * (-1 / 3) ^ 2) from rfl)
      (show onQuartic (2 / 3, (2 / 3 : ℝ) ^ 4 - 5 * (2 / 3) ^ 2) from rfl)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  exact new_oblique_quadruple_criterion

end Erdos101OQ04
