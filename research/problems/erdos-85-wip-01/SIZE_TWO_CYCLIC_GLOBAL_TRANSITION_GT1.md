# GT1 correction: half-shift agreements give target digons only

Date: 2026-08-24

Scope: `BinarySizeTwoCyclicPackingBound`; correction and stop result for the
first-level global transition route

## Retraction

The first version of this note incorrectly claimed that a half-shift
agreement produces an isolated two-vertex component with four parallel
edges.  The mistake was to compare congruent source row and column
coordinates while forgetting that local coordinate nodes are indexed by the
entire routing block.  The two sources `(x,t)` and `(x+m,t)` are different
blocks, so their source incidences cannot be paired by one folded coordinate
node.

The correct statement is the one recorded independently in
`SIZE_TWO_CYCLIC_SEPARATION_CORE_AUDIT.md`: a half-shift agreement produces a
parallel row/column **digon at the common target block only**.  The remaining
two incidences of each central vertex continue through their separate source
blocks.  The digon is generally not a connected component, and it has no
fixed additive contribution to `|P|-c(G)` or interlacement nullity.

Commit `e900ac033d` and the original room message advertising a
four-parallel component are superseded by this correction.

## Correct coordinate translation

Put `q=2m`.  Fix a difference `t`, bases `x,x+m`, and aligned relative rows
`r,r-m`.  If the partial permutations agree, their relative columns are
`c,c-m`, and both routed darts have the same absolute target cell.  Let their
reciprocal-pair central vertices be `e_1,e_2`.

At the two source ends we have incidences

```text
((x,t),   R, r mod m),       ((x,t),   C, c mod m),
((x+m,t), R, (r-m) mod m),   ((x+m,t), C, (c-m) mod m).
```

The displayed residues agree in pairs, but the block indices do not.
Therefore these are four different local coordinate nodes and create no
source-side edges between `e_1,e_2`.

At the target end, both reverse darts lie in the same block.  Their reverse
rows `-r,-(r-m)` differ by `m`, and their reverse columns
`t-r,t-(r-m)` also differ by `m`.  The target block therefore has one
degree-two folded row node and one degree-two folded column node incident to
`e_1,e_2`.  Suppression produces exactly two parallel graph edges:

```text
target-row edge:    e_1 -- e_2;
target-column edge: e_1 -- e_2.
```

This labelled digon is equivalent to the common target of the half-shifted
source pair.  Under the fixed shore-preserving transition at central
vertices, however, each of its two edges is paired with an edge continuing
toward a source block.  The two parallel edges do not form a partition
circuit by themselves.

Diagonal routes still require the dummy-loop inflation described in
`SIZE_TWO_CYCLIC_GLOBAL_TRANSITION_TYPECHECK.md`, but that issue does not turn
the target digon into an isolated component.

## Exact cap content

The same-difference cap at source separation `m` says that, for each labelled
half-shifted source pair, at most one target-block row/column digon occurs.
It does not forbid all digons, and it does not determine how their four
remaining source-side incidences recombine.

This is all of the cap information visible in the first half quotient.
Higher source separations are not encoded by that quotient.

## Bounded stop result

The exact q=8 separation-orbit census in
`SIZE_TWO_CYCLIC_SEPARATION_CORE_AUDIT.md` is decisive for this mechanism:

- capping only the half-shift separation orbit `4` is SAT;
- capping the three core fibers `{0,2,4}` only at separation `4` is SAT;
- for the loopless `t=4` terminal, every proper subset of the four undirected
  nonzero separation orbits `{1,2,3,4}` is SAT, while all four are UNSAT.

Hence the first half-quotient graph and any invariant determined solely by
its target digons admit exact models satisfying every cap they can see.  An
extended Cohn--Lempel nullity calculation on this level cannot prove the q=8
terminal.  This is stronger than failure to find the right statistic: the
relevant relaxed routing object exists.

## Surviving direction

A transition formulation can survive only by retaining all nonzero source
separation orbits simultaneously, or an equivalent full group-algebra
correlation object.  The missing theorem must couple the digons labelled by
different separations while preserving the exact one-per-row/column slice
and reciprocity.  Ordinary first-level nullity, total digon count, or a
single dyadic layer is insufficient.

This correction therefore closes GT1 as originally proposed.  The honest
replacement chain is:

```text
full separation-labelled transition/correlation system
  -> all-orbit coupling theorem                         [GAP]
  -> duplicate labelled common neighbour or support contradiction
  -> BinarySizeTwoCyclicPackingBound.
```
