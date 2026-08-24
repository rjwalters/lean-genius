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

## Larger support can escape a blocked singleton cap

The support-eight obstruction is not always a connected-component
invariant.  Repeating the exact full-code query at every support from 9
through 16 leaves four representative blocked patterns UNSAT:

```text
a=0, capped orbit {2,5};
a=1, capped fibre 2;
a=2, capped fibre 0;
a=3, capped fibre 0.
```

But at support 24 the a1/fibre-2 query is SAT, with an explicit full-code
rank drop

```text
144 -> 104.
```

Its support is not accidental: it is exactly the parity half-space

```text
{(x,t) : x+t is odd}
```

inside the 48 allowed q8 cells.  Since the a1 holes have opposite parity,
this selects three of the six allowed difference fibres at every base and
has size `q(q-2)/2 = 24`.  This exposes a concrete candidate for the
q-generic large closure that a cap-preserving descent construction should
study, rather than treating support 24 as an unstructured solver witness.
The probe's `--support-parity odd` option now prescribes this half-space
exactly.  It reproduces the q8 witness in about one second.  The direct q10
analogue (`a=1`, cap fibre 2, support 40) is `unknown` after 300 seconds, so
there is not yet computational evidence that the rank-lowering realization
extends beyond q8.

The support-17 through support-23 queries timed out at 120 seconds, so the
least escaping support is known only to lie in `[17,24]`.  Exact-support
queries 25--28 also timed out and are not inferred from the support-24
witness.

For comparison, the a0/orbit-`{2,5}` and a3/fibre-0 queries are UNSAT at
every exact support 8--28, the entire possible support range.  The a2/fibre-0
query is UNSAT through support 16 and unknown above it at the same timeout.

Therefore reflection-organized caps can force a genuinely nonlocal trade,
but they do not uniformly separate the reciprocal realization space.  A
cap-preserving descent proof must count or construct larger closures; it
cannot restrict without loss to the sharp eight-cell trades.  The two
full-range UNSAT patterns remain evidence for a stronger component
obstruction in some hole/cap configurations, but not a universal one.
