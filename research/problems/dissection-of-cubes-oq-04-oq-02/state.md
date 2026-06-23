# Research State: dissection-of-cubes-oq-04-oq-02

## Current State
**Phase**: ORIENT (transitioning from OBSERVE → ORIENT after S1)
**Path**: full
**Since**: 2026-05-12T15:10:00-07:00 (S1 complete)
**Iteration**: 1

## Current Focus
S1 OBSERVE complete. Landscape mapped: in dimension 4 the 5-cell and 600-cell are the irrational-dihedral cases (rest contribute zero Dehn invariant via $\mathbb{R} \otimes \mathbb{Z}/n = 0$). For dimensions $\ge 5$, $d$-simplex (all $d \ge 3$) and $d$-cross-polytope ($d = 3, d \ge 5$) need irrationality proofs.

## Active Approach
**Approach A** — Parametric Niven-Chebyshev sequence. Defined as:

$$
d_n = q^n \cdot 2\cos(n \arccos(p/q)), \qquad d_{n+2} = 2p\,d_{n+1} - q^2 d_n
$$

with mod-prime divisibility witness for any odd prime $\ell \mid q$, $\ell \nmid p$. Covers the $d$-simplex family for $d$ with an odd prime factor (everything except $d \in \{4, 8, 16, \ldots\}$) and the $d$-cross-polytope family for $d \ne 4$ (analogous).

**Deferred**: Approach B (algebraic-integer / cyclotomic Niven) for $q$ a pure power of 2. 600-cell via Conway–Jones or $\mathbb{Z}[\sqrt5]$ — S5+.

## Attempt Count
- Total attempts: 1 (S1 OBSERVE, this session)
- Current approach attempts: 0 (S2 not yet started)
- Approaches surveyed: 3 (A: Chebyshev mod-prime, B: algebraic-integer Niven, C: per-polytope-family direct)

## Blockers
None. S2 is well-scoped and uses existing parent-file infrastructure.

## Next Action

**S2 ORIENT**: locate Mathlib lemmas needed for the parametric proof:
- `cos_step` analog for $\cos((n+2)\theta)$ — present in parent file as `cos_step`; reuse or recopy.
- `cos_int_mul_two_pi` — already used by parent.
- `Rat.cast_def`, `Rat.num`, `Rat.den` arithmetic — already in parent.
- Mathlib `Nat.Prime`/`Fact` instance handling — standard.

**S3 ACT**: create `proofs/Proofs/DissectionOfCubesOQ04OQ02.lean` with:
1. `chebSeq` definition + recurrence lemmas
2. `chebSeq_eq_cos` parametric trig identity
3. `prime_ndvd_chebSeq` parametric divisibility
4. `niven_chebyshev` parametric irrationality theorem
5. `simplex_dihedral_irrational_of_odd_factor` instantiation
6. `crossPolytope_dihedral_irrational_of_odd_factor` instantiation

Estimated S3 LOC: ~300 lines, ~1 session.

## Session Log

- 2026-05-12 S1 OBSERVE — landscape + S2 plan committed (researcher-8, this PR)
