# GT1: half-shift agreements are four-parallel components

Date: 2026-08-24

Scope: `BinarySizeTwoCyclicPackingBound`; global transition-system route

## Result

Let `q=2m`.  In the repaired hub graph from
`SIZE_TWO_CYCLIC_GLOBAL_TRANSITION_TYPECHECK.md`, a **non-diagonal** agreement
between the same-difference routing blocks based at `x` and `x+m` produces
an isolated component consisting of two central vertices joined by four parallel edges.
The four edges are the paired source rows, source columns, target rows, and
target columns.  Under the fixed shore-preserving reciprocity transition at
the two central vertices, this component is partitioned into exactly two
two-edge circuits: a row digon and a column digon.

Consequently the same-difference agreement cap says that, for every
half-shifted source-block pair, there is at most one such four-parallel
component.  In the core fiber `t=0` every agreement is automatically
non-diagonal because column zero is forbidden.  For a general fiber, a cap
may instead be consumed by a diagonal agreement; that case has a different
transition gadget and is not covered here.  This is the precise current GT1
translation.  It is q-generic and uses
the uncancelled lifts; mod-two folded-cell cancellation would erase all four
parallel edges in pairs and lose the statement.

GT1 does not itself give a contradiction.  The next step, GT2, must force
more than one four-parallel component for some half-shifted source pair, or
derive an incompatible interlacement nullity from their global count.

## Coordinate proof

Fix an allowed difference `t` and two bases `x` and `x+m`.  Suppose their
partial permutations agree at aligned rows `r` and `r-m`, and neither route
is diagonal.  Write their
relative columns as `c` and `c-m`; the agreement equation is

```text
c = m + (c-m).
```

The two routed darts therefore have the same absolute target cell:

```text
source 1: (x,t),   row r,   column c;
source 2: (x+m,t), row r-m, column c-m.
```

Let their reciprocal-pair central vertices be `e_1,e_2`.  At the source
blocks, both coordinate differences are `m`, so reduction modulo `m` puts
the two row incidences at one degree-two coordinate node and the two column
incidences at another.  After suppression these give two parallel edges

```text
source-row edge:    e_1 -- e_2;
source-column edge: e_1 -- e_2.
```

Both darts have the same target difference

```text
s = c-r = (c-m)-(r-m),
```

and hence reverse into the same target block `(x+r,s)`.  Their reverse rows
are `-r` and `-(r-m)`, again differing by `m`; their reverse columns are
`t-r` and `t-(r-m)`, also differing by `m`.  The target block therefore adds
two more parallel edges between the same central vertices.

Because neither route is self-reciprocal, both central vertices have two
distinct endpoint views.  Every incidence of `e_1` and `e_2` appears in
those four edges.  Neither central vertex is incident to a hub or to any other central vertex, so the
four-parallel bundle is a connected component, not merely a local minor.
The fixed central transition

```text
R_source -- R_target | C_source -- C_target
```

pairs the two row edges into one digon and the two column edges into the
other.

Conversely, a four-parallel component whose four edges arise from the
source/target row/column nodes for one half-shifted block pair reconstructs
the two aligned routes and their shared absolute target cell.  Hence this
coordinate-labelled component is equivalent to a half-shift agreement.

If one route is diagonal, its reverse endpoint view coincides with its source
view and its central object has only two real incidences.  The other route's
remaining incidences continue elsewhere in the hub graph; adding the dummy
loop needed for 4-regularity does not recreate the missing coordinate edges.
Therefore diagonal agreements must not be counted as four-parallel
components.  At `t=0` they cannot occur because allowed columns exclude `0`.

## Exact cap statement

For fixed `(x,t)`, the same-difference cap compares the blocks `(x,t)` and
`(x+m,t)` and allows at most one aligned row agreement.  Replacing `x` by
`x+m` counts the same unordered block pair and the same four-parallel
component from the other orientation.  Thus:

```text
number of four-parallel components at fiber t
  = (1/2) * sum_x number of non-diagonal half-shift agreements at (x,t),
```

and each unordered half-shifted source pair contributes at most one component
when fiber `t` is capped.  Equality with all agreements holds at `t=0` (or
under Loopless), but not for an arbitrary reduced-code fiber.

This formulation avoids an overclaim: the cap does not forbid all such
components; it forbids multiplicity two for the same source-block pair.

## Executable calibration

The exact q=8 loop-permitting permutation CNF was sampled with
`cross_mode=same-t`.  For every selected cap set, the coordinate assertions
in the proof above passed for every half-shift agreement, and capped fibers
had multiplicity at most one.  One solver model per control gave:

```text
selected caps   oriented non-diagonal agreements over all fibers
{0}             30
{2}             40
{4}             36
{0,2}            0
{0,4}            0
{2,4}           16
{0,2,4}         UNSAT
```

The counts include uncapped fibers and count each component from both source
orientations.  They are calibration only, not a finite proof.  Their useful
message is negative as well as positive: many four-parallel components are
compatible with one- and two-fiber controls.  GT2 must use their labels,
distribution, or interlacement interaction; total component count alone is
not terminal.

The `{0}` model also had four oriented diagonal agreements (two unordered
events) in uncapped fibers.  This adversarial control is why the
non-diagonal qualifier is necessary.  The other displayed models happened
to have none, but no theorem is inferred from that sample.

## GT2 interface

After dummy-loop inflation of diagonal central objects, choose an Euler
system of the fixed hub graph.  The circuit partition fixes the central
transitions and varies the three hub transitions.  Each non-diagonal
half-shift agreement component contributes exactly

```text
two partition circuits - one graph component = 1
```

to `|P|-c(G)`, hence one unit of interlacement nullity.  A possible GT2 must
show that the binary/hub boundary laws force too much nullity in one labelled
source-pair sector, or force a second component with the same label.  The
ordinary extended Cohn--Lempel equality only totals these contributions and
does not by itself provide that pigeonhole principle.
