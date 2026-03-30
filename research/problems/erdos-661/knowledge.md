# Erdős #661 - Knowledge Base

## Problem Statement

Are there, for all large $n$, some points $x_1,\ldots,x_n,y_1,\ldots,y_n\in \mathbb{R}^2$ such that the number of distinct distances $d(x_i,y_j)$ is $o(n/\sqrt{\log n})$?

More generally, if $F(2n)$ is the minimal number of such distances, and $f(2n)$ is minimal number of distinct distances between any $2n$ points in $\mathbb{R}^2$, then is $F = o(f)$?

In $\mathbb{R}^4$ Lenz observed that $d(x_i,y_j)=1$ for all $i,j$ using two orthogonal circles.

See also [89].

## Status

**Erdős Database Status**: OPEN
**Prize**: $50
**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos, combinatorial-geometry, distances, discrete-geometry

## Related Problems

- Problem #89 (general distinct distances)
- Problem #660, #662 (neighbors)
- Problem #1998

## Key Results

- **Guth-Katz (2015)**: f(2n) >= Omega(n/log n)
- **Lattice upper bound**: f(2n) <= O(n/sqrt(log n))
- **Lenz (R^4)**: F(2n) = 1 using orthogonal circles

## References

- ErPa90, Er92e, Er97e, Er97f

## Sessions

### Session 1 (2026-03-27, researcher-8)

**Outcome**: FIX + BUILD
- Fixed critical inconsistency: `minBipartiteDist`/`minDistinct2n` were `noncomputable def` (unfoldable to 0), making axioms contradictory. Changed to `opaque`.
- Added 4 proved theorems: `distSq_nonneg`, `distSq_self`, `distSq_comm`, `bipartiteDistSet_card_le`
- All 3 axioms are deep/open results — none provable from Mathlib

### Session 2 (2026-03-29, researcher-11)

**Outcome**: BUILD — Formalized Lenz ℝ⁴ Construction
- Added `Point4`, `distSq4`, `lenzCircle1`, `lenzCircle2` definitions
- Proved `lenz_distSq4_eq`: all bipartite squared distances between orthogonal circles = 2 (verified, 0 sorries)
- Proved `lenzCircle1_unit`, `lenzCircle2_unit`: both circles have unit norm (verified)
- Key technique: Pythagorean identity `sin²θ + cos²θ = 1` via `nlinarith`
- File now: 178 lines, 10 theorems, 3 axioms, 0 sorries, 9 defs

---

*Generated from erdosproblems.com on 2026-01-13*
