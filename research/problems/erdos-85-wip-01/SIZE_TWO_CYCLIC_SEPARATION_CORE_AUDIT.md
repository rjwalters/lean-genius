# Source-separation core audit for the q=8 half fiber

Date: 2026-08-24

Owner: codex-sol-3

Scope: `BinarySizeTwoCyclicPackingBound`; stop result for global-transition
candidate `GT1`

## Result

For the loopless direct routing model at `q=8`, reflection parameter `a=1`,
and the common-neighbor cap restricted to source-difference fiber `t=4`, the
four undirected nonzero first-coordinate separation orbits are represented by

```text
{1, 2, 3, 4},   with d identified with -d modulo 8.
```

The model is satisfiable when the cap is retained on any proper subset of
these four orbits and unsatisfiable when it is retained on all four.  The
proper-subset statement was checked exhaustively by orbit subset size: all
four singletons, all six pairs, and all four three-element subsets are SAT.
The full set is the previously observed singleton-fiber `t=4` UNSAT result.

The reusable option `--c4-separation d` in
`size_two_cyclic_exact_graph_probe.py` selects these orbits.  For example:

```text
# A largest proper subset: SAT
python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 \
  --c4-pair-mode same-difference --c4-difference 4 \
  --c4-separation 1 --c4-separation 2 --c4-separation 3 \
  --quiet-model

# No separation filter, hence all four orbits: UNSAT
python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 \
  --c4-pair-mode same-difference --c4-difference 4 \
  --quiet-model
```

`--c4-separation` is an undirected filter: selecting `d` also selects `-d`.
It composes with the existing source-difference filter and does not change
default semantics.

## Exact first-level interpretation

Put `q=2m`.  Let

```text
A  = (x,   x+t),
A+ = (x+m, x+m+t).
```

If `B=(u,u+s)` is a common neighbor of `A,A+`, the two reverse darts in B's
routing block have relative rows

```text
x-u, x+m-u
```

and relative columns

```text
x+t-u, x+m+t-u.
```

They are therefore the two lifts of one folded row and one folded column.
In the uncancelled half-quotient transition graph, the two corresponding
reciprocal-dart vertices are joined by parallel row and column transitions: a
digon labelled by the source pair `{A,A+}`.  Conversely, every such parallel
row/column pair comes from a common neighbor of an m-separated same-fiber
source pair.

Hence the caps visible in the first half quotient are exactly the caps in
separation orbit `m`.  At q=8 this is orbit `4`.  The new executable result
shows that capping only this orbit is SAT, even in fiber `t=4`; capping all
three core fibers `{0,2,4}` only on separation `4` is also SAT.

## Consequence for the proposed mechanism

The first half-quotient transition graph, its Z/2 derived double cover, and
any invariant determined solely by either graph cannot prove the q=8
terminal: an exact routing model satisfying every cap visible at that level
exists.  In particular, a single extended Cohn--Lempel interlacement-nullity
argument cannot supply `GT1`.

More strongly, the t=4 obstruction does not live in any proper set of source
separation orbits.  Odd separations `{1,3}` alone are SAT, even separations
`{2,4}` alone are SAT, and every three-of-four selection is SAT.  The bounded
data therefore points to a genuinely global group-algebra relation coupling
all nonzero separations, not a single 2-adic layer or a proper truncation of a
dyadic descent.

This is a stop result, not a proof of `BinarySizeTwoCyclicPackingBound`.  A
replacement mechanism must explain the all-orbit coupling q-generically; it
must not extrapolate a contradiction from the first half quotient.
