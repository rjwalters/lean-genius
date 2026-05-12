# Knowledge Base: picks-theorem-oq-01-oq-01-oq-01

## The Question

> Can Pick's theorem `I + B/2 - 1 = Area` be derived in Lean 4 by combining
> primitive triangulation with a boundary-point count via the GCD formula
> (boundary points on segment from `v1` to `v2` = `gcd(|v2.1 - v1.1|, |v2.2 - v1.2|)`)?

## The Answer

**Yes, in principle.** Both ingredients are already formalized in this
project:

| Ingredient | File | Status |
|---|---|---|
| Primitive triangulation: every lattice triangle = list of \|det\| primitive triangles | `PicksTheoremOQ01OQ01.lean` | Verified (0 axioms, 0 sorries) |
| GCD boundary count: segment `(0,0)→(a,b)` has `gcd(a,b)+1` lattice points | `PicksTheoremOQ02.lean` | Verified (0 axioms, 0 sorries) |

## Bridge Strategy

The bridge is implemented in `Proofs/PicksTheoremOQ01OQ01OQ01.lean`. The
key definitions:

```
twiceArea T       = |det T|
boundaryCount T   = Σ_i gcd(|Δx_i|, |Δy_i|)        (i = 0, 1, 2 over edges)
pickInterior T    = (twiceArea : ℚ)/2 - (boundaryCount : ℚ)/2 + 1
pickInteriorNum T = (twiceArea : ℤ) - (boundaryCount : ℤ) + 2
```

The bridge identity `2 · pickInterior = pickInteriorNum` lets us reason
in `ℤ` (cleared form) when proving inductive statements.

## Algebraic Sketch

To prove Pick's formula for a lattice triangle `T`:

**Step 1 (Area).** By the shoelace formula (already in `PicksTheoremOQ01`,
Part II), `2 · Area(T) = |det(T)| = twiceArea T`. By `PicksTheoremOQ01OQ01.exists_primitive_triangulation`, `T = ⋃ T_i` for `i ∈ {1, ..., n}` with `n = |det T|` and each `T_i` primitive (`|det T_i| = 1`, so `Area(T_i) = 1/2`).

**Step 2 (Boundary).** By `PicksTheoremOQ02.card_segmentPoints`, the
segment from `(0,0)` to `(a, b)` (with `a, b : ℕ`) carries `gcd(a, b) + 1`
lattice points. The general edge from `(x_1, y_1)` to `(x_2, y_2)` reduces
to this case via translation and reflection: lattice points are
preserved by translation, and `gcd` is invariant under negation, so the
count is `gcd(|x_2 - x_1|, |y_2 - y_1|) + 1`.

Each triangle edge contributes its `gcd(|Δx|, |Δy|) + 1` lattice points
to the boundary, but the three vertices are each shared between two
edges. Total `B = Σ (gcd + 1) - 3 = Σ gcd = boundaryCount T`.

**Step 3 (Pick's formula).** Rearranging `A = I + B/2 - 1` gives
`I = A - B/2 + 1 = (2A - B + 2) / 2 = pickInteriorNum / 2 = pickInterior`.

The remaining content is showing that `pickInterior T` equals the *actual*
interior-point count `realInterior T`, which decomposes into:

(a) **Base case** (primitive triangle, `|det| = 1`): no strictly-interior
    lattice points (`realInterior = 0`), and `pickInterior = 1/2 - 3/2 + 1 = 0`.
(b) **Inductive step**: combining two primitive pieces glued on a shared
    edge with `gcd = 1` adds `pickInterior(T1) + pickInterior(T2)` and
    preserves `realInterior(T1 ∪ T2) = realInterior T1 + realInterior T2`.

## Built Items (this session)

- `LatticeTriangle` (mirror structure)
- `LatticeTriangle.det` (signed determinant)
- `LatticeTriangle.NonDegenerate` (`det ≠ 0`)
- `LatticeTriangle.twiceArea` (= `|det|`)
- `LatticeTriangle.edgeDelta` (`Fin 3 → ℕ × ℕ`)
- `LatticeTriangle.edgeGCD` (`Fin 3 → ℕ`)
- `LatticeTriangle.boundaryCount` (= Σ edgeGCD)
- `LatticeTriangle.pickInterior` (rational form)
- `LatticeTriangle.pickInteriorNum` (cleared-integer form)
- `two_mul_pickInterior` (identity 2·pickInterior = pickInteriorNum)
- `pick_formula_cleared` (twiceArea = 2·pickInterior + boundaryCount - 2)
- Three test-triangle verifications (unit, 2-by-1, 3-by-3).

## Insights

1. **Both ingredients verified independently** — the bridge is purely
   compositional. No new mathematical content; just plumbing.
2. **Cleared-denominator form essential** — `pickInteriorNum = 2A - B + 2`
   stays in `ℤ`, dodging the rationals during the future induction.
3. **Edge accounting** — each edge contributes `gcd + 1` lattice points;
   the three shared vertices double-count, so `B = Σ (gcd + 1) - 3 = Σ gcd`.
   This is why `boundaryCount` is the bare sum, no `+1` or `-3`.
4. **Translation invariance gap** — `PicksTheoremOQ02` only handles
   segments from `(0,0)` to `(a, b)` with `a, b : ℕ`. The general case
   needs a small lemma (`gcd` invariance under translation and reflection),
   straightforward but missing from the project.

## Mathlib Gaps

None for the S1 OBSERVE scope. Future sessions may need:

- A formal definition of "interior lattice points of a triangle" via
  `Finset.Icc` and a half-plane filter. Mathlib has `Convex` / `intrinsicInterior`
  for the topological version, but the discrete lattice-point count
  needs a custom `Finset` definition.
- A general "segment lattice points from `(x1, y1)` to `(x2, y2)`" lemma
  generalizing `PicksTheoremOQ02.card_segmentPoints` to arbitrary
  integer endpoints (5–10 lines of `Finset.image`).

## Next Steps

- **S2** — formalize `realInterior T` as a `Finset` cardinality and verify
  `realInterior unitTriangle = 0` agrees with `pickInterior`.
- **S3** — prove the additivity lemma for primitive sub-triangles sharing
  a `gcd = 1` edge.
- **S4** — close the induction via `exists_primitive_triangulation`.
