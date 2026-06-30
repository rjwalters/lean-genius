# Finding: the index-p² 3D-ellipsoid Minkowski route CANNOT supply the `Q < 2p` step

**Session**: researcher-11, 2026-06-16 (Docker free; ORIENT + empirical verification).
**Status**: verified arithmetic finding. Corrects the discharge plan recorded in
`knowledge.md` (sessions R3 06-15, R2) which still describes "choose ellipsoid radius
`R` so `vol > 2³·p²` ⟹ Minkowski point ⟹ `Q < 2p` ⟹ `Q = p`" as the live path to
`dirichlet_key_lemma`. That path is geometrically unattainable as stated; the missing
step needs a **2-dimensional** slice argument, not the 3D ellipsoid bound.

## What is actually missing in `ThreeSquares.lean`

The file has 0 sorries and 2 axioms. To discharge `dirichlet_key_lemma`
(`ThreeSquares.lean:648`) the existing S5–S16 chain reduces to **one** unfinished
geometric step:

> produce a **nonzero** point `v` of the Dirichlet sublattice
> `IsInDirichletSublattice p r v  :=  p ∣ (v0 − r·v1) ∧ p ∣ v2`
> with `dirichletForm d v = v0² + d·v1² + d·v2² < 2p`.

Everything downstream is already proved:
- `dirichletForm_dvd_of_in_sublattice` (`:1275`): `r²+d ≡ 0 (mod p)` ⟹ `p ∣ Q(v)` on the sublattice.
- `dirichletForm_eq_p_of_lt_two_mul` (`:1366`): `0 < Q(v) < 2p` and `p ∣ Q(v)` ⟹ `Q(v) = p`.

**Grep-confirmed**: `dirichletForm_eq_p_of_lt_two_mul` is `private` and the only thing
that consumes it is its own helper `multiple_p_eq_p_of_lt_two_mul`. **No lemma in the
file produces the `Q < 2p` hypothesis** — the sublattice-Minkowski application exists
only as a docstring TODO (`:1692`). That single step is the whole remaining gap.

## Why the existing 3D-ellipsoid infrastructure cannot supply `Q < 2p`

The S16 stack builds the **real** sublattice `dirichletSublatticeReal p r`
(`:1560`) with **covolume p²** (`dirichletSublatticeReal_covolume`, `:1695`), and the
ellipsoid `dirichletEllipsoid d R = {Q ≤ R}` whose volume is `(4π/3)·R^(3/2)/d`.

To force a **nonzero sublattice** point by Minkowski you need
`vol(ellipsoid) > 2³ · covolume = 8p²`, i.e.

```
(4π/3)·R^(3/2)/d > 8p²   ⟺   R > (6 d / π)^(2/3) · p^(4/3).
```

So the **best guarantee this route can give is `Q ≤ R ~ p^(4/3)`**, which exceeds `2p`
for every `p` above a tiny threshold. Verified for `p ∈ {7,…,10007}`, `d ∈ {1,2,3}` in
`verify_minkowski_2p_gap.py` block **[A]** — `R > 2p` in **every** row.

Intuition: the index-p² sublattice is genuinely "long" — e.g. the explicit member
`v = (r, 1, 0)` (it satisfies `v0 − r·v1 = 0` and `v2 = 0`) has `Q = r² + d`, up to
`~p²/4` for the reduced root `|r| ≤ p/2`. A rank-3 nondegenerate form has Witt index ≤ 1,
so the largest sublattice on which `Q ≡ 0 (mod p)` is forced to be index **p²**, and the
generic 2ⁿ Minkowski bound on it is too weak by a factor `~p^(1/3)`.

## The attainable route: the 2D slice `z = 0`

Restricting to `z = 0` drops to the **index-p** sublattice `{(x,y) : x ≡ r·y (mod p)}`
of `ℤ²` with the **binary** form `x² + d·y²`. Its determinant on the sublattice is
`d·p²`, so the 2D Hermite/Minkowski bound gives a nonzero point with

```
Q ≤ (2/√3)·√(d·p²) = (2/√3)·√d · p ,   which is  < 2p  ⟺  d ≤ 2  (since 2/√3·√2 ≈ 1.633).
```

Block **[B]** of `verify_minkowski_2p_gap.py` brute-forces the 2D slice and confirms:
for **every** applicable `(p, d)` with `d ∈ {1,2}` (i.e. `−d` a QR mod `p`), the slice
minimum is `Q = p` (`< 2p`). The case split in the file's own docstring (`:632`) only
ever uses `d ∈ {1, 2}`, so the slice route covers all needed cases.

## Recommended ACT (for the next session with a build host)

The missing `S11` step should be formalized as a **2-dimensional** Minkowski/Hermite
application on the `z = 0` slice — NOT an extension of the 3D `dirichletEllipsoid`
machinery. Concretely:

1. Specialize Mathlib's geometry-of-numbers lemma (or reuse the 2D Dirichlet/Minkowski
   already proved in `Proofs/MinkowskiTheoremOQ02OQ01.lean`) to the index-p sublattice
   `{x ≡ r y mod p}` with the disk `{x² + d y² ≤ R}`, `R` chosen with
   `π R / d > 4p` (the 2D bound `vol > 2²·covol = 4p`) and `R < 2p` — simultaneously
   solvable exactly when `(2/√3)√d·p < 2p`, i.e. `d ≤ 2`.
2. Feed the resulting `(x, y, 0)` to `dirichletForm_dvd_of_in_sublattice` +
   `dirichletForm_eq_p_of_lt_two_mul` to get `Q = p`, then run the existing descent.

Alternatively, abandon the geometry-of-numbers route entirely and formalize
**Davenport–Cassels** (rational ⟹ integral for `x²+y²+z²`) per `G1-dirichlet-bearer.md`
and PR #24149 — the standard textbook proof of three squares, ~150–260 LOC.

## Honest scope

- This note makes **no** claim that three-squares is false or unprovable (it is a
  theorem). It pins down *which* geometric tool the unfinished step requires and *why*
  the current 3D-ellipsoid trajectory stalls.
- All quantitative claims are elementary arithmetic, checked in
  `verify_minkowski_2p_gap.py` (block [A] = the `p^(4/3)` overshoot; block [B] = the 2D
  slice attains `Q = p` for `d ∈ {1,2}`). No Lean was added/changed this session.
