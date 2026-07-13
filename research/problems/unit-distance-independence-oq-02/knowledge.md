# Knowledge Base: unit-distance-independence-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: prove `χ(ℝ²) ≤ 7` (Hadwiger-Nelson upper bound) via explicit hexagonal
7-coloring of the plane in Lean 4.

The construction in `proofs/Proofs/UnitDistanceHN7.lean` uses the A₂ lattice with
basis e₁ = (s√3, 0), e₂ = (s√3/2, 3s/2), s = hexSideLength = 2/5, and assigns
color (3q + r) mod 7 to each hex Voronoi cell. Three obligations are needed:

1. **Algebraic distance formula**: ‖center(a₁,b₁) - center(a₂,b₂)‖² = 3s²·Q(Δa,Δb)
   where Q(da,db) = da² + da·db + db².
2. **Color-sublattice min norm**: Q ≥ 7 on `{(da,db) : 3da+db ≡ 0 mod 7}`.
3. **Covering radius**: every point is within distance s of its assigned center.

(2) is a clean integer-arithmetic argument using db = -3da + 7m (already proved).

---

## Insights

### Session 2026-04-29 progress (researcher-1)

**Resolved 2 of 3 sorries** in the main file (`UnitDistanceHN7.lean`):

1. **`hexCenter_dist_sq`** — algebraic distance formula. Proof uses
   `EuclideanSpace.dist_sq_eq` to reduce ‖.‖² to a sum over coordinates, then
   `PiLp.toLp_apply` + `Matrix.cons_val_*` to evaluate the matrix-cons centers.
   The resulting polynomial identity in ℝ has a single `√3·√3` term; supplying
   `Real.mul_self_sqrt` as a hypothesis lets `nlinarith` close it.

2. **Modular-arithmetic step inside `same_color_far`** — extracting
   `3·Δa + Δb ≡ 0 (mod 7)` from `hexColor p = hexColor q`. After
   `simp only [hexColor, Fin.mk.injEq]`, the equality is between
   `((3·aᵢ + bᵢ) % 7).toNat % 7` values. With bounds
   `0 ≤ x % 7 < 7` for both sides, `omega` discharges the goal directly
   (handling `Int.toNat` and the redundant `Nat.mod 7`).

The two resolutions also flow back to `UnitDistanceHN7Aristotle.lean`:
- `hexCenter_dist_sq_ari` now delegates to the main lemma.
- `hexColor_eq_implies_mod_ari` is proved in parallel by the same `omega` step.

### Remaining obligation: `covering_radius`

The cube-coordinate Voronoi rounding in `hexCoord` should send each point to
the nearest A₂ lattice center; the obligation is to bound the resulting
Euclidean distance by s = 2/5.

**Why this is the hardest of the three.** Unlike the algebraic and modular
steps, this lemma quantifies over arbitrary `p : Plane` and unfolds the
cube-coordinate rounding algorithm:
```
rq, rr, ry := ⌊q + 1/2⌋, ⌊r + 1/2⌋, ⌊y + 1/2⌋   where y = -q - r
   if rq + ry + rr = 0 then (rq, rr)
   else fix the coordinate with the largest rounding error.
```

A direct strategy:
1. Without correction: each of `|q - rq|, |r - rr|, |y - ry|` is ≤ 1/2.
2. After correction: the chosen `(a, b)` differs from `(q, r)` by at most 1/2
   in cube norm (max of |Δa|, |Δb|, |Δa + Δb|).
3. The Euclidean distance from `p` to `hexCenter a b` is then bounded by the
   length of the longest cube-step edge of the hex Voronoi cell, which equals s.

Concretely: if `|q - a| ≤ 1/2` and `|r - b| ≤ 1/2` and `|q + r - (a + b)| ≤ 1/2`,
then `(p - center(a,b))` decomposes in the (e₁, e₂) basis as
  `(q - a)·e₁ + (r - b)·e₂`
and the squared length is `3s²·((q-a)² + (q-a)(r-b) + (r-b)²)`. The cube
constraint forces this quadratic form to be ≤ s² (circumradius² of the regular
hexagon with side s).

**Suggested implementation sketch**:
- Prove: for any (q, r) ∈ ℝ², the cube-rounded (a, b) satisfies
  `(q - a)² + (q - a)(r - b) + (r - b)² ≤ 1/3`.
- Combine with `hexCenter_dist_sq` (now proved) and the s = 2/5 specialization
  to conclude `dist p (hexCenter a b)² ≤ 3s²·(1/3) = s²`, hence `≤ s`.

The bound `1/3` is the maximum value of Q over the hex Voronoi cell scaled to
unit lattice (its corners at distance 1/√3).

---

## Dead Ends

- `ring_nf` alone cannot close `hexCenter_dist_sq` because it does not know
  `√3·√3 = 3`. Tried `ring_nf; rw [h3]; ring` initially — `ring_nf` normalizes
  the irrational `√3` differently each time, breaking the rewrite. Final form
  uses `nlinarith [h3, ...]` with `h3 : √3·√3 = 3` as the key hypothesis.

- `simp only [hexColor]` alone leaves a `let (q, r) := ...; ⟨...⟩` shape that
  `omega` cannot parse. Added `Fin.mk.injEq` to peel the `Fin 7` constructor
  and expose the underlying `Nat` equality before `omega`.
