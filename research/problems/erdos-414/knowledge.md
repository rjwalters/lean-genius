# Erdős #414 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $h_1(n)=h(n)=n+\tau(n)$ (where $\tau(n)$ counts the number of divisors of $n$) and $h_k(n)=h(h_{k-1}(n))$. Is it true, for any $m,n$, there exist $i$ and $j$ such that $h_i(m)=h_j(n)$?



Asked by Spiro. That is, there is (eventually) only one possible sequence that the iterations of $n\mapsto h(n)$ can settle on. Erd\H{o}s and Graham believed the answer is yes. Similar questions can be asked by the iterates of many other functions. See also [412] and [413].


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #412
- Problem #413
- Problem #415
- Problem #2
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

### Session 2026-04-27 — researcher-4 (stable-complete assessment)

**Outcome**: surveyed / formalization stable

The Lean formalization in `proofs/Proofs/Erdos414Problem.lean` is at its stable
endpoint: 32 theorems, 1 axiom, 0 sorries. The lone axiom is the open
Erdős-Graham conjecture itself. All supporting theory is proved:

- Growth: `h_strictly_increasing`, `orbit_strictly_increasing`,
  `orbit_linear_lower`, `orbit_linear_lower_ge2`
- Bounds: `h_upper`, `h_upper_sqrt`, `divisors_card_le_two_sqrt`,
  `h_lower_bound_ge2`
- Determinism: `hOrbit_continuation` (once two orbits meet, they stay merged)
- Computed values: `h_one`..`h_ten`, base merges of orbits 2..10 with orbit
  of 1 (`orbit_*_merges_with_1`)
- Structural consequence: `single_eventual_orbit` (derived from the conjecture
  via orbit-of-1 as reference)

**Why no further routine progress is possible**:

1. The remaining axiom IS the open conjecture. Eliminating it requires
   a mathematical breakthrough, not Mathlib lookup.
2. Adding more individual `orbit_N_merges_with_1` theorems for N > 10 is
   enumeration theater — covers a finite set, conjecture concerns infinitely
   many starts.
3. All natural supporting bounds (τ ≤ 2√n, h ≤ n + 2√n, h ≥ n+2 for n ≥ 2)
   are already proved.

**What an actual proof attack would need**:

- A density argument: show every sufficiently large integer lies in the
  forward orbit of 1 under h. Equivalent to proving the image of `h^k(1)`
  for k ≥ 0 has positive density / asymptotic density 1.
- Or a structural reduction: classify residues mod some modulus to merge
  orbit equivalence classes.
- Connection to OEIS A064491 (orbit of 1 under h) — known sequence but no
  proof of merge property.
- Sieve methods or probabilistic heuristics for τ(n) iteration.

**Reusability**: The structural framework (`hOrbit_continuation`,
`hOrbit_pos`, monotonicity pattern) is reusable for related iteration
problems — notably Erdős #412 (σ-iteration version). Worth porting if
someone takes that file beyond its current scope.

---

*Generated from erdosproblems.com on 2026-01-13*
