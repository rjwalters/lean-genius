# G3 — A constructive (measure-theory-free) route for the `Q < 2p` slice leaf

**Session:** 2026-06-16 (researcher-2). **Status:** build-free research delta;
both Docker (`docker ps` exit 124) and Aristotle (`prove` → "Resource not found",
the documented 404) are down, so no Lean was built or submitted.

## The single open leaf

After PR #24967 (merged) isolated the `Q < 2p` step into
`proofs/Proofs/ThreeSquaresSliceMinkowski.lean`, the entire remaining open
content of `dirichlet_key_lemma` is one self-contained 2D existence statement:

```lean
theorem exists_slice_point_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p := by sorry
```

The bridge (`slice_point_to_dirichlet_vector`) and the assembled existence
(`exists_dirichlet_vector_lt_two_mul`) in that file are already proved; this
`sorry` is the only gap, and it is flagged there as "the Aristotle target".

## Finding: the witness is explicitly constructive

The file's docstring proposes proving the leaf via a 2D Minkowski convex-body
bound on the disk `x² + d·y² < 2p`. That is correct but would require porting
Mathlib's Haar-measure GoN lemma
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`,
used in the 3D `minkowski_ellipsoid_has_lattice_point`) down to two dimensions —
the same measure-theoretic apparatus that proved too weak in 3D.

It is unnecessary. The index-`p` sublattice
`L = {(x,y) ∈ ℤ² : p ∣ (x − r·y)}` has the **explicit basis** `{(p,0),(r,1)}`
(since `x = r·y + p·k`). Running **Lagrange–Gauss 2D reduction** on this basis
under the `d`-weighted inner product `⟨(x₁,y₁),(x₂,y₂)⟩ = x₁x₂ + d·y₁y₂` returns
the shortest nonzero vector `v ∈ L`, which satisfies the 2D Hermite bound

```
N(v) = v₀² + d·v₁² ≤ γ₂·√d·p = (2/√3)·√d·p
```

and `(2/√3)·√d < 2` **exactly for `d ≤ 2`** (d=1: 1.1547, d=2: 1.6330; d=3:
2.0000 — the boundary). This is elementary number theory: no measure theory, no
Haar volume, no convex-body theorem.

## Certificate

`verify_slice_constructive_witness.py` (committed, pure stdlib, runnable):
over **all** primes `p < 2000`, both `d ∈ {1,2}`, and **every** residue
`r ∈ [0,p)` — 554,100 triples:

- zero-vector failures: **0**
- membership failures (`p ∣ v₀ − r·v₁`): **0**
- `N(v) ≥ 2p` failures: **0**
- worst `N(v)/p`: d=1 → 1.15053 (ceiling 1.15470), d=2 → 1.63068 (ceiling
  1.63299) — i.e. the construction saturates the Hermite bound
- max reduction steps over all triples: **5** (O(log p) termination)

This strictly extends the prior `verify_minkowski_2p_gap.py`, which (a) only
scanned `r = √(−d) mod p` whereas the Lean leaf quantifies over arbitrary `r:ℤ`,
and (b) used a brute-force window with no algorithm. Here the witness is produced
by a deterministic reduction — the exact recursion a Lean proof would induct on.

## Recommended formalization route (when Docker/Aristotle return)

Prove `exists_slice_point_lt_two_mul` by Lagrange–Gauss reduction, not GoN:

1. **Termination / shortest vector.** Reduction strictly decreases
   `max(N(b₁),N(b₂))` until `|⟨b₁,b₂⟩| ≤ ½N(b₁)` — a well-founded recursion on
   `ℕ` (the norm is a non-negative integer). Empirically ≤ 5 steps; the bound is
   the continued-fraction length of `r/p`.
2. **Reduced ⟹ bound.** For a reduced basis, `N(b₁)·N(b₂) ≤ (4/3)·det²` and
   `det(L) = p`, giving `N(b₁) ≤ (2/√3)·√d·p`. Working over ℤ, avoid the real
   `√` by squaring: `3·N(b₁)² ≤ 4·d·p²`, then `N(b₁) < 2p` follows from
   `3·(2p)² = 12p² > 4·d·p²` ⇔ `d < 3`, i.e. `d ≤ 2` (`interval_cases d`).
3. **Membership** is preserved by integer column operations from the start basis
   `{(p,0),(r,1)} ⊂ L`.

Mathlib-bearer status: a direct binary-quadratic-form *reduced-form / shortest
vector* lemma does NOT appear to exist in the gallery or be readily citable from
Mathlib (grep of `proofs/Proofs/` found no reduction bearer; the gallery's
`MinkowskiTheoremOQ02OQ01.lean` is Dirichlet-approximation, not a short-vector
bound). So step 2 must be built. It is, however, a self-contained elementary
lemma and a far better Aristotle target than the measure-theoretic alternative —
resubmit `exists_slice_point_lt_two_mul` to Aristotle once the 404 clears, with
the hint "Lagrange–Gauss reduce {(p,0),(r,1)} under x²+d·y²; interval_cases d".

## Honest scope

This session changed **no Lean** and eliminated **no axiom** — both verification
backends were down. The deliverable is a verified-by-computation route
re-characterization: the keystone leaf has an explicit, measure-theory-free,
O(log p) constructive witness, which materially de-risks (and shrinks) its
eventual formalization. `ThreeSquares.lean` still carries its 2 axioms.
