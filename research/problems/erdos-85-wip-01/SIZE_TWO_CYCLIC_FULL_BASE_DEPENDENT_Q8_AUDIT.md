# Full base-dependent q8 code audit

## Purpose

All earlier SAT controls imposed translation invariance
`E(t,u,r)=E(t,u,r+x)` after normalization.  The actual theorem
`BinarySizeTwoCyclicPackingBound` concerns an arbitrary base-dependent cyclic
code.  The new probe `size_two_cyclic_full_probe.py` removes that reduction.

For `q=8,a=2` it has 48 vertices `(x,t)`, where `x` is a base and `t` is one
of the six allowed difference fibres.  It creates one Boolean for each
unordered vertex pair (1,128 edge variables) and directly imposes:

1. for every source cell and absolute target row, zero hits in its two
   consecutive component rows and exactly one hit in every other row;
2. the analogous exact law for absolute target columns;
3. at most one precise common target for every pair of bases in every fixed
   difference fibre; and
4. optionally, no internal edge in a selected fibre.

Using unordered edge variables is exactly block-transpose reciprocity.  The
`--directed` control instead uses 2,256 ordered variables and drops only that
condition.

## Verdict and controls

All runs use `q=8,a=2` and finish in seconds:

| constraints | verdict |
|---|---|
| exact hits + reciprocity, no caps | SAT |
| exact hits + reciprocity, no caps, empty fibre 4 | SAT |
| exact hits + all caps, directed, empty fibre 4 | SAT |
| exact hits + reciprocity + all caps | UNSAT |
| exact hits + reciprocity + all caps + empty fibre 4 | UNSAT |

Commands:

```text
python3 size_two_cyclic_full_probe.py 8 --a 2 --no-caps
python3 size_two_cyclic_full_probe.py 8 --a 2 --no-caps --empty-fiber 4
python3 size_two_cyclic_full_probe.py 8 --a 2 --directed --empty-fiber 4
python3 size_two_cyclic_full_probe.py 8 --a 2
python3 size_two_cyclic_full_probe.py 8 --a 2 --empty-fiber 4
```

The first two controls show that the exact row/column equations and the
undirected encoding are consistent, including with the selected zero block.
The third reproduces, without translation invariance, the key A/B separator:
full caps and emptiness coexist until reciprocity is restored.  The fourth
shows that at q8 the full reciprocal cap family is already inconsistent even
without selecting an empty fibre.

For comparison, q6 full caps are UNSAT even in the directed control, while
dropping caps is SAT.  Thus reciprocity is the sharp separator at q8, not a
generic property of every small even order.

## Significance and boundary

This is the first bounded evidence directly covering the base-dependent
interface used by the Lean theorem, rather than a translation-invariant
subclass.  It strongly validates the full-cap/global-transpose target and
rules out the possibility that the q8 obstruction was merely circulant.

It remains computational evidence, not a proof.  The immediate theorem hunt
should extract a small constraint core or a colored trace/support identity
from this full model.  The translation-invariant T3/T4 trace separator is a
candidate guide, but its cyclic convolution formulas cannot simply be
assumed for arbitrary blocks.  Any formal lift must use the general matrix
identities `A_tu=A_ut^T` and exact base-resolved row/column partitions.

## Base-dependent transpose core

The option `--reciprocity-core` switches to directed variables, groups the
equations `A_tu=A_ut^T` by unordered fibre pair, and greedily deletes groups.
Deletion checks have a five-second bound; `unknown` conservatively retains a
group, so the output is a sufficient but not necessarily irredundant core.

With empty fibre `4`, the full arbitrary-base q8 contradiction needs only

```text
14, 16, 33, 34, 36, 37, 46, 47, 67.
```

The `3/4/6/7` triangle complex from the translation-invariant audits remains
visible, but the full model also uses transpose blocks `14`, `16`, and the
self-block `33`.  This is the first theorem-shaped block support for the
non-translation-invariant target.

Without the empty-fibre condition the bounded shrink retains 20 of the 21
possible block groups.  Some may remain only because a directed deletion
timed out, but the contrast is still useful: selecting `A_44=0` exposes a
much smaller nine-block reciprocal subsystem.  This agrees with the colored
trace audit, where removing emptiness restored SAT even after all degree-3/4
trace reversal identities were imposed.
