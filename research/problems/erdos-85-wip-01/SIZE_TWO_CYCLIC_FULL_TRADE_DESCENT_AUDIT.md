# Full-code eight-cell trade descent audit

Node: reciprocal cap-preserving descent beneath
`BinarySizeTwoCyclicPackingBound`.

## Exact full-code query

`size_two_cyclic_full_trade_probe.py` builds two complete undirected routing
codes `K,K'` on the same q8 allowed cells.  Both separately satisfy every
exact target-row and absolute-target-column hit equation.  It requires:

```text
K xor K' is incident with exactly eight cells;
every selected cell is incident with a changed edge;
defectRank(K') < defectRank(K).
```

Thus this is no longer a local signed-margin or relaxed-load model: every
unchanged edge is an actual reciprocal dart and both endpoints are full
codes.  The optional `--caps` imposes all same-fibre caps in both codes; at
q8 that query is vacuously UNSAT because the individual all-cap code is
already known not to exist.

## Full extendability is SAT

Without caps, support-eight strict descent is SAT for every q8 hole
representative.  Unbounded examples found ranks

```text
a=0: 176 -> 168
a=1: 172 -> 168
a=2: 184 -> 176
a=3: 174 -> 170.
```

Every witness changes sixteen undirected edge memberships, attaining the
proved minimum of eight removed and eight added edges.  Therefore the sharp
support theorem is attained by actual full reciprocal codes, not only by an
abstract bitrade.

## First bounded support-eight descents

The flag `--max-old-rank K` locates the first rank layer at which this
minimum-size descent is possible.  Direct native-Z3 results are

| `a` | cap-free minimum rank | largest bound with no support-8 descent | first bound with descent | witnessed drop |
|---:|---:|---:|---:|:---:|
| 0 | 78 | 79 | 80 | `80 -> 78` |
| 1 | 64 | 75 | 76 | `76 -> 64` |
| 2 | 64 | 65 | 66 | `66 -> 64` |
| 3 | 88 | 103 | 104 | `104 -> 98` |

These are trade-existence thresholds, not claims that every intervening
integer rank is realized.  In particular the a3 first eight-cell move does
not reach the global minimum; larger support or repeated moves are still
needed.

## Consequence

The cap-free reciprocal realization space genuinely contains sharp
eight-cell rank-lowering trades.  Hence none of the following can be the
missing descent obstruction by itself:

- exact row and column projections;
- entrywise reciprocity;
- cyclic moving holes;
- full outside-code extendability; or
- scalar defect-rank decrease.

The remaining issue is specifically **cap-preserving availability from an
arbitrary nonminimal all-cap code**.  Since no q8 all-cap code exists, that
universal descent statement cannot be tested by exhibiting a q8 source
model.  A proof must use caps to guarantee or obstruct closure before the
already-dead minimum stratum, likely through the reflection-orbit collision
charge rather than generic trade connectivity.

## Selective caps isolate the reflection obstruction

`--cap-fibres` imposes every pair cap in selected endpoint fibres in both
full codes.  At unbounded old rank, support-eight descent has the following
exact q8 pattern under `j(t)=-1-t`:

```text
a=0: orbit {1,6} capped together: SAT
     fibres 2 and 5 separately: SAT, but orbit {2,5} together: UNSAT
     fibres 3 and 4 separately: UNSAT

a=1: orbit {0,7} capped together: SAT
     fibres 2,3,4,5 separately: UNSAT

a=2: orbit {1,6} capped together: SAT
     fibres 0,3,4,7 separately: UNSAT

a=3: every singleton cap fibre: UNSAT.
```

Thus a minimum-support full-code descent can preserve caps on at most one
complete reflection orbit.  Obstruction is genuinely orbitwise: at a0 the
two caps in `{2,5}` are harmless separately but fatal together.  This is
direct bounded evidence that the q-generic reflected deviation charge is
the correct interface between caps and descent, rather than merely a
convenient grouping of endpoint fibres.
