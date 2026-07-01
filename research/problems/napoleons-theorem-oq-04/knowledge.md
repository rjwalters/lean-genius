# Knowledge: Napoleon's Area Theorem (napoleons-theorem-oq-04)

## Goal

Formalize the area half of Napoleon's theorem: for any triangle `z₁z₂z₃`, the outer
Napoleon triangle area minus the inner Napoleon triangle area equals the area of `z₁z₂z₃`.

## Session 1 (researcher-8, 2026-07-01): SOLVED (VERIFIED 0-axiom)

`proofs/Proofs/NapoleonAreaOQ04.lean` — 5 theorems, 2 defs, 121 lines, 0 axioms.

### The math (and why the seeker sketch was false as written)

The classical result: with side lengths `a,b,c` and area `S`,
`Area(outer Napoleon) = (√3/24)(a²+b²+c²) + S/2`,
`Area(inner Napoleon) = (√3/24)(a²+b²+c²) − S/2`, difference `= S`.

The provided sketch had two errors, both confirmed by brute-force numerics:

1. **Centroid vs apex.** The Napoleon triangle is formed by the **centroids** of the
   equilateral triangles on the sides. The centroid offset from a side's midpoint is
   `|q-p|·√3/6`, one third of the apex offset `|q-p|·√3/2`. The sketch used `√3/2`
   (apex) → identity fails. Correct: `napCentroid p q r = (p+q)/2 + (q-p)(i·r·√3/6)`.

2. **Sign / orientation.** With signed area `triArea a b c = ½ Im((b-a) conj(c-a))`
   (the sketch's own code convention) and the **same** cyclic vertex order for both
   Napoleon triangles, the inner triangle is oppositely oriented, so its signed area is
   the negative of its unsigned area. Exhaustive search over {apex, centroid} ×
   {outer sign} × {inner vertex permutation} shows the ONLY true signed identity is
   `centroid, outer +, inner −, inner-vertices reversed`, i.e.
   `triArea(outer) + triArea(inner, same order) = triArea(original)`.

### Verified statements

- `napoleon_area_signed` : `triArea(G_out z₂z₃, G_out z₃z₁, G_out z₁z₂)
  + triArea(G_in z₂z₃, G_in z₃z₁, G_in z₁z₂) = triArea(z₁,z₂,z₃)`.
- `napoleon_area_difference` : `triArea(outer) − triArea(inner, reversed) = triArea(original)`
  (the literal classical subtraction, inner in natural opposite orientation).

### Key Lean recipe (reusable for √3 planar-geometry identities)

- **Route complex signed areas through real coordinates.** Prove once
  `triArea_eq : triArea a b c = ((b.im-a.im)(c.re-a.re) − (b.re-a.re)(c.im-a.im))/2`
  (via `Complex.mul_im`, `Complex.sub_re/im`, `Complex.conj_re/im`, then `ring`).
- **Define points with `Complex.ofReal` scalars, not ℂ-division.** Writing the midpoint as
  `(p+q) * Complex.ofReal (1/2)` and the rotation as `I * Complex.ofReal (r*√3/6)` lets
  `.re`/`.im` expand with only `Complex.{add,sub,mul}_{re,im}`, `Complex.I_{re,im}`,
  `Complex.ofReal_{re,im}` + `ring` — **no** `Complex.div_re`/`normSq` mess.
- **One `linear_combination` for the √3-cancellation.** Set `hs : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)`; after expansion the goal is `LHS = RHS` polynomial in the
  coords and `√3` with `√3` only to power ≤ 2 and the odd part structurally zero, so
  `LHS − RHS = k·(√3² − 3)`. **Compute `k` with sympy** (the `s²` coefficient) and pass
  `linear_combination k * hs`. Here `k = (−z₁.re·z₂.im + z₁.re·z₃.im + z₂.re·z₁.im
  − z₂.re·z₃.im − z₃.re·z₁.im + z₃.re·z₂.im)/12` = original signed area ÷ 12. One-shot.
- **Orientation flip as a lemma:** `triArea a b c = −triArea a c b` by `simp [triArea_eq]; ring`
  converts the signed-addition form to the literal subtraction form.

### Gallery

New entry `napoleons-theorem-oq-04` (badge original, status verified, 0 axioms).
Parent `napoleons-theorem` (equilaterality) unchanged.
