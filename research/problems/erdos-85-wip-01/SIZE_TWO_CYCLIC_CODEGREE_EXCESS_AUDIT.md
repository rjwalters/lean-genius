# Codegree-excess audit for the q=8 half fiber

Date: 2026-08-24

Owner: codex-sol-3

Scope: `BinarySizeTwoCyclicPackingBound`; conserved-total divergence after the
source-separation core audit

## Statistic

Fix a source-difference fiber `S_t`.  For two distinct vertices `u,v` in the
fiber, let `c(u,v)` be their number of common neighbors.  Define

```text
X_t = sum_{{u,v} subset S_t} binom(c(u,v), 2).
```

`X_t` is the number of 4-cycles whose selected opposite pair lies in `S_t`,
counted once for each such opposite pair.  A same-fiber common-neighbor cap is
exactly the assertion that its corresponding summands vanish.  The full cap
on `S_t` says `X_t=0`.

The exact graph probe now supports:

- `--codegree-profile-difference t`, which reports the distribution of
  `c(u,v)`, its sum, and `X_t` by undirected first-coordinate separation;
- `--codegree-excess-cap N`, which adds the constraint `X_t <= N` and requires
  the profile fiber option.

## q=8 verdict

For `q=8`, `a=1`, `t=4`, with exact row/column hit laws and symmetric loopless
routing but no common-neighbor cap:

```text
X_4 <= 1  is UNSAT,
X_4 <= 2  is SAT.
```

Hence the exact minimum is `X_4=2`.  Reproduction:

```text
python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 --no-c4 \
  --codegree-profile-difference 4 --codegree-excess-cap 1 --quiet-model

python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 --no-c4 \
  --codegree-profile-difference 4 --codegree-excess-cap 2 --quiet-model
```

The first encoding contains 28,980 Boolean terms representing pairs of
common neighbors.  This is a bounded computational result, not a certificate
or Lean theorem.

## Conserved-total hypothesis is false

For each of the four controls that caps three of the four nonzero undirected
source-separation orbits and leaves one free, four solver seeds were sampled.
The total codegree sum varied from 13 to 32 and `X_4` varied from 2 to 24.
There is therefore no fixed conserved total of either quantity.

Every capped orbit had zero excess, and all positive excess was carried by
the one free orbit.  This explains the all-orbit minimal core without a
constant-sum identity: the exact laws force *some* 4-cycle, but an uncapped
separation orbit can absorb it.

## Remaining mathematical target

The cap contradiction at q=8 can be restated as the sharp positive lower
bound `X_4 >= 2`.  A q-generic successor would prove, under the exact two-hole
partial-permutation and reciprocity laws,

```text
X_(q/2) > 0
```

(or a stronger explicit lower bound) for every relevant `q=2^k`.  Ordinary
bipartite degree convexity is insufficient: `S_(q/2)` has q vertices of
degree `q-2`, but the opposite shore has `q(q-2)` vertices, so those degrees
alone allow codegree at most one.  Any proof must use the shifted row/column
holes together with reciprocity.

Sharp q=8 models with `X_4=2` were inspected.  The two surviving 4-cycles do
not form an obvious translation pair uniformly across solver seeds, so no
involution-pairing theorem is claimed.

This audit stops further collision-total sampling in the loopless model.  A
loopless successor would require a structural reason that at least one
opposite-fiber 4-cycle exists, not more finite distributions.  The correction
below explains why that is not the reduced-code target.

## Scope correction: the positive lower bound uses Loopless

The preceding q=8 minimum is a theorem only of the stronger, default
**loopless** exact-graph encoding.  The actual reduced-code target
`SizeTwoCyclicPackingExclusion` deliberately drops Loopless, so diagonal
symmetric-relation variables must be retained.  With that target scope the
positive lower bound is false.  On the same integration code:

```text
python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 --no-c4 \
  --allow-loops --codegree-profile-difference 4 \
  --codegree-excess-cap 0 --quiet-model
```

returns `sat`.  The reported half-fibre profile is

```text
separation 4: distribution={0: 2, 1: 2}, sum=2, excess=0,
all separations: total codegree sum=16, total excess=0.
```

This independently reproduces the earlier loop-permitting CNF fact that the
singleton `t=4` cap is satisfiable.  Consequently

```text
X_(q/2) > 0
```

is **not** an honest q-generic successor for
`BinarySizeTwoCyclicPackingBound`; it can be retained only as a Loopless
corollary/diagnostic.  The reduced-code obstruction remains simultaneous:
singletons and pairs of the core fibres are satisfiable with loops, while the
triple is not.  Any terminal must use cross-fibre compatibility or first
derive Loopless from the full triple hypotheses; it cannot derive the packing
bound from half-fibre C4 positivity alone.

## Uniform-multiplicity gate and hypothesis isolation

The new option `--uniform-profile-multiplicity` requires every allowed cell
to have exactly one neighbor in the profiled source fiber.  At `q=8,a=1`,
the opposite fiber cannot have this perfectly uniform incidence profile in
either the loopless model or the loop-permitting reduced-code model:

```text
python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 --no-c4 \
  --codegree-profile-difference 4 --uniform-profile-multiplicity \
  --quiet-model --timeout-ms 60000
# UNSAT

python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 --no-c4 \
  --allow-loops --codegree-profile-difference 4 \
  --uniform-profile-multiplicity --quiet-model --timeout-ms 60000
# UNSAT
```

This does not restore the positive-excess theorem: as the scope correction
above records, the loop-permitting model has `X_4=0` solutions.  Those
solutions therefore realize a linear incidence hypergraph, but only with a
nonuniform point-multiplicity profile.  The uniform gate identifies a valid
reduced-code fact: any solution has nonzero incidence deviation.

Write

```text
n(B) = |N(B) intersect S_(q/2)|.
```

Exact row and column hits give sum `q-2` over every target row and every
target column, each of which contains `q-2` allowed cells.  Hence
`delta(B)=n(B)-1` is an integer circulation on the allowed row-column
bipartite graph.  If it is nonzero, its smallest possible support has two
positive and two negative cells; correspondingly
`sum_B binom(n(B),2) >= 2`.  This explains the scale of the q=8 minimum, but
does not yet prove `X_(q/2)>0`: the latter requires the same source pair to
collide at two different cells.

In the stronger loopless model, the q=8 `X_4=0` contradiction genuinely uses
all three structural inputs.
With symmetry retained, the exact probe is SAT after dropping either family
of marginals:

```text
--no-columns  # rows only: SAT at X_4=0
--no-rows     # columns only: SAT at X_4=0
```

With both partial-permutation marginals retained but reciprocity disabled,
the independent permutation encoding is also SAT with the full `t=4` cap.
Thus a one-sided packing theorem, a marginal-only inequality, or reciprocity
alone cannot prove the loopless positive excess.  For the reduced target,
the honest local conclusion is only that `delta` is a nonzero integer
circulation while `X_(q/2)` may still vanish.  Any terminal argument must
couple that circulation to the other core fibers and triple caps, or first
derive Loopless from the full triple hypotheses.
