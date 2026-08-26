# H7 common-neighbor encoding audit

Date: 2026-08-26

## Outside source

The closest successful computation, `R(C4,K1,39)=46`, uses common-neighbor
indicator variables for C4-freeness and CaDiCaL.  This audit inspected upstream
commit `86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33`, especially `caseB2.py`.
Its roughly 220,000-clause instances are not directly comparable to H7: a
strong local structure theorem and 144 canonical subcases fix most graph
edges before CNF generation.  Thus the clause count is not evidence that a
generic 46-vertex encoding is intrinsically easier.

One mechanism does transfer exactly.  For each endpoint pair `(u,v)`, introduce
a literal equivalent to `uw AND vw` for every possible common neighbor `w`,
then impose at most one true indicator using a sequential counter.  This is
equivalent to the canonical direct clauses forbidding every pair of common
neighbors, but changes propagation and size substantially.

## H7 implementation and equivalence boundary

`sat49/check_h7_t0_canonical_common_neighbor.py` preserves the canonical
semantic edge variables `1..861` byte-for-byte in row-wise order and reuses the
reviewed compact exact-degree counters.  It replaces only the C4 encoding.

The helper simplifies fixed edges before encoding:

* a false incident edge removes that common-neighbor candidate;
* one fixed-true candidate forces every other candidate false;
* two fixed-true candidates emit the empty clause;
* otherwise, Tseitin equivalences plus sequential at-most-one encode the exact
  common-neighbor bound.

Tests exhaust every assignment of a three-candidate tiny instance and every
existential auxiliary assignment, including forced-true cases.  They also pin
the full H7 shape and semantic edge prefix.  The emitted CNF is deliberately
marked `signal_only`: it is not accepted by the canonical LRAT/Lean pipeline.

## Exact size and bounded signal

For the hard root `cube_F6_t2`:

| encoding | variables | clauses | C4 clauses |
|---|---:|---:|---:|
| canonical compact | 17,633 | 720,825 | 687,260 |
| common-neighbor | 80,010 | 227,577 | 194,012 |

The signal CNF SHA-256 is
`491d45e908645b449d6abf42523ba5244235391c7b417566ccbdeee3d3723942`.

CaDiCaL 3.0.1, one concurrent 60-second comparison:

| encoding | result | conflicts | decisions | propagations | peak RSS |
|---|---|---:|---:|---:|---:|
| canonical compact | no result | 1,796,899 | 2,778,726 | 202,822,221 | 429.20 MB |
| common-neighbor | no result | 1,702,651 | 3,344,120 | 498,819,780 | 153.11 MB |

The alternative cuts clauses by 68% and memory by 64%, but gives no qualitative
60-second gain.  It performs 2.46 times as many propagations and only 5% fewer
conflicts.  Under the campaign's hill-climb rule, this bounded mechanism is cut:
do not extend the run or launch a fleet from this signal alone.

The artifact remains useful if a later proof-producing solver is memory-bound.
Before any UNSAT result may enter the H7 capstone, the alternative encoding
needs either a formal equisatisfiability bridge to the canonical CNF or an
independently verified proof transformation.  No such bridge is claimed here.

