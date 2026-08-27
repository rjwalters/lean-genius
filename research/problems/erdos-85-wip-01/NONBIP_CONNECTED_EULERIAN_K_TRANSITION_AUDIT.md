# NONBIP-CONNECTED Eulerian K transition audit

## Candidate structure

Let `K=triangleFreeEdgeGraph G=A intersect D`, and write
`k_x=degree_K(x)`.  At even ambient degree,

```text
k_x + 2t_x = q,
```

so every K-degree is even.  This is already formalized as
`binarySquare_regular_triangleFree_degree_even`.  Consequently every
connected component of K is Eulerian and its half-edges admit transition
systems/circuit partitions.

The divergence-78 proposal asked whether a mod-4 invariant of these circuit
partitions could force either rooted terminal congruence.

## Literature boundary

Martin/circuit-partition polynomials and the extended Cohn--Lempel equality do
provide canonical sums over transition systems.  The directly relevant
references include:

- Lorenzo Traldi, *Binary nullity, Euler circuits and interlace polynomials*,
  arXiv:0903.4405 (extended Cohn--Lempel equality for circuit partitions in
  4-regular graphs);
- Ellis-Monaghan, *New Results for the Martin Polynomial*, JCTB 74 (1998),
  and the circuit-partition identities literature for general Eulerian graphs.

These results count circuit partitions after a transition system (or sum over
all systems); they do not attach the ambient A/D layer data needed here.  At
vertices of K-degree greater than two, a transition pairing is noncanonical.
Summing over all `(2m-1)!!` pairings removes the choice but does not create a
new rooted phase.

## Visit-weight circularity

Fix an ambient root `x`.  Every transition system of K uses exactly
`k_y/2` local transitions at a vertex `y`.  Therefore the total number of
transitions based at ambient neighbors of x is independent of the circuit
partition:

```text
sum_{y in N_A(x)} k_y/2 = (A k)_x/2.
```

Any multiplicative phase depending only on whether a transition visits
`N_A(x)` consequently factors out of the Martin/circuit-partition sum as

```text
i^((A k)_x/2) * (unweighted circuit-partition sum).
```

But the sharp rooted mass terminal satisfies

```text
(A k)_x + 2(A t)_x = q^2.
```

When `8 divides q`, the desired `(A t)_x=2 (mod 4)` is equivalent to
`(A k)_x=4 (mod 8)`, i.e. to fixing precisely the phase that was factored
out.  The transition polynomial records the missing residue; it does not
force it.

## No local R/S transition color

One might try to avoid this factorization by weighting the pairing of
individual K half-edges according to their rooted layers.  This also has no
local input.  If `y` is adjacent to x and `yz` is a K-edge, then z cannot be
adjacent to x: otherwise x is a common neighbor of y and z, contradicting
that `yz` is triangle-free.  Since `x-y-z` is a two-path, every such z lies in
the second-layer branch owned by y.

Thus all K half-edges at a vertex `y in N_A(x)` have the same rooted layer and
the same branch label.  A local degree-four pairing, for example, has three
possible transitions but no A/D-rooted color that distinguishes them.  Any
weight based only on visits/layers is factorable and returns the circular
phase above.  A nonfactorable weight would need genuinely nonlocal data not
supplied by generic Eulerian transition theory.

## Verdict

Eulerianity of K is valid global structure, but the raw Martin/interlace
transition mechanism is **cut** for the rooted terminal.  It either requires a
noncanonical pairing or, after summing over all pairings, factors out exactly
the unknown `(A k)_x/2` phase.  Reopening this lane requires a separately
defined nonlocal transition weight with an independent evaluation; ordinary
circuit counts, visit phases, and local rooted-layer colors do not advance the
two terminal congruences.
