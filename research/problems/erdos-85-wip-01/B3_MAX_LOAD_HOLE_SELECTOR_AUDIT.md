# B.3 maximum-load exceptional-hole selector audit

Status: computational evidence and proof decomposition, not a theorem.

## Surviving selector

For a point `p`, let `F_p = {u : p in B_u}` and

```
D_p = sum (d u) over u in F_p.
```

Restrict to points incident with an exceptional hole and choose among them a
point of maximum `D_p`.  The surviving target is:

> Some maximum-load exceptional-hole point has a reduced full-fiber price
> cover of cost strictly less than `D_p`, with denominator at most six.

The reduced mask is exactly the one consumed by
`false_of_scaledCommonPointFiberPriceCertificate`: outgoing point prices at
the five rows of `F_p`, together with incoming compensation prices at `p`.

## Evidence

- 30 independently generated outer designs passed the weaker exceptional-hole
  selector (branches 3 and 4, 15 each).
- A further 20 independently generated outer designs passed after restricting
  to maximum-load exceptional-hole points (10 per branch).
- All five tracked serious payloads pass the maximum-load restriction:

| payload | branch | max `D_p` | witness |
|---|---:|---:|---:|
| `q9_13f_counterexample.json` | 3 | 27 | `p=4`, scale 1, `26 < 27` |
| `q9_13t_counterexample.json` | 3 | 27 | `p=13`, scale 6, `161 < 162` |
| `q9_gram_fractional_gap_witness.json` | 3 | 27 | `p=18`, scale 1, `26 < 27` |
| `q9_outer_seed_b3s3_triangle_selector_counterexample.json` | 3 | 27 | `p=5`, scale 1, `26 < 27` |
| `q9_branch4_row40_interval_witness.json` | 4 | 29 | `p=19`, scale 1, `28 < 29` |

The fresh generator is not a stable fixture generator across Python processes:
model-construction ordering varies, so seed labels must not be cited as durable
witness identifiers.

For branch 3 there is a further empirical horn.  When the two exceptional
triples intersect, their unique shared point was integrally strict in every
stored fresh example; the serious payloads and durable triangle-selector
counterexample instead have disjoint holes.  The option
`q9_hole_fiber_negation_smt.py --branch 3 --shared-hole-point-only` forces the
intersecting case and asserts the partial-mass negation only at the shared
fiber.  Even with `--residual-type-ledger`, the seed-free instance remained
`UNKNOWN` after 120 seconds.  This is a well-scoped candidate horn, not yet a
solver certificate or proof.

The kernel theorem
`squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center`
now proves the missing exceptional-row equation.  The probe option
`--exact-hole-partition` imposes it literally on each selected partial mass:
the residual block multiplicity at `q` is zero on the hole's U1-core support
and one off that support.  Fixed `13f`/hole 24 is `UNSAT` in 0.3 seconds, but
the unrestricted one-hole branch-3 instance with both the exact partition and
residual type ledger remains `UNKNOWN` after 120 seconds.  The theorem is now
consumed faithfully; solver search, not omission of (13aj), is the remaining
computational limitation.

The formal exceptional-cardinality package further gives exactly six
residual rows per hole, split into three marked-pair and three ordinary-triple
centers.  `q9_exceptional_hole_sixpack_sat.py --hole-reciprocity` couples the
two branch-3 six-packs by symmetric hole-to-hole adjacency; the resulting
outer system is still `SAT` in 9.6 seconds.  The stronger
`--hole-pair-reciprocity` mode couples both holes to all 21 marked-pair rows;
that sharply scoped system is `UNKNOWN` after 120 seconds.  Thus local
six-packs plus hole reciprocity are insufficient, while the first unresolved
agreement boundary is symmetry against the pair rows.

The proved cross-hole C4 law says the two holes share at most one selected
marked-pair center.  `--hole-pair-choice-overlap-cap` adds this constraint.
It is still locally `SAT` in 1.8 seconds, sharply: the witness holes intersect
in one U1 point and agree in exactly one marked support.  Even the targeted
intersecting-hole negation with one shared relation, both exact partitions,
and residual type ledgers remains `UNKNOWN` after 120 seconds.  Thus the cap
is real new structure but does not by itself yield a solver terminal.

The stronger proved cap bounds the intersection of the two full six-row
residual packs by one.  `--hole-full-pack-overlap-cap` consumes it; the local
system remains `SAT` in 1.9 seconds.  Since both residual block unions have
cardinality 15 inside 24 points, their point-set intersection has cardinality
at least six.  Such a point is covered uniquely by a residual neighbor of
each hole, making it a natural double-saturation price candidate.  This
selector passes 9 of 10 independent exact-sixpack models but is refuted by
the tenth: its cover intersection has ten points and none has a strict scaled
cover through denominator six.  Therefore the 15/9 overlap arithmetic plus
the full-pack cap still needs exceptional-to-pair/full-relation agreement.

A joint two-point price survives that counterexample.  For distinct points
`p,q` in the intersection of the two 15-point residual covers, put row price
`1_{F_p} + 1_{F_q}`; overlap rows therefore carry multiplicity two.  In
branch 3 its exact degree target is `D_p + D_q = 54`.  The dedicated exact
probe `q9_joint_overlap_fiber_price_probe.py` restricts point prices to
outgoing coordinates at rows in `F_p union F_q` and incoming coordinates at
`p` or `q`, then reconstructs and verifies its MILP output in integer
arithmetic.  It found a strict scaled joint cover in all ten independent
exact-two-sixpack/full-pack-cap models.  Witness scales were at most six and
costs were respectively `53/54`, `53/54`, `323/324`, `106/108`, `106/108`,
`53/54`, `53/54`, `53/54`, `107/108`, and `215/216`.  A fresh standalone
three-model run also passed at scale one with `53 < 54` in every model.  The
banked theorem `false_of_scaledTwoUnitSupportsPointPriceCertificate` is the
literal actual-relation consumer for these integer certificates.  This is
the strongest surviving branch-3 selector, but remains finite evidence until
existence of the joint cover is proved uniformly.

Minimum exact eligibility load does not rescue branch 3 at this local scope.
Among ten independent exact-two-sixpack/full-pack-cap models, restricting to
the global argmin of `L(p)=sum_{u in F_p} deg_H(u)` produced a strict scaled
cover in only five.  The argmin was unique in nine models, so tie-breaking is
not the issue.  The positive-special restriction may still make minimum load
useful in branch 4, but bare load descent is not a common branch-3 terminal.

The diagnostic option `--print-hole-packs` prints the selected blocks in a
SAT model.  In one hole-reciprocal branch-3 model, an exact denominator-six
scan found a strict cover at only one of the six hole incidences (scale 2,
`53 < 54`); the other five had no scaled cover through denominator six.
Hence even after imposing both exact local six-packs, no pointwise
"every hole point is strict" lemma is available.  The surviving statement is
genuinely an alternative across the two holes and their six incidences.

The original negation assigns an unrelated partial mass to every candidate,
whereas an actual residual graph is one common symmetric relation.
`--shared-relation` corrects that relaxation: it keeps one global fractional
mass, imposes mutual eligibility and all point capacities, exact degrees on
the union of the selected fibers, and both exact hole partitions.  It does
not zero edges outside the fibers.  Fixed `13f` is `UNSAT` in 0.1 seconds of
solving; the unrestricted branch-3 instance with residual type ledgers is
still `UNKNOWN` after 120 seconds.  Thus common-relation coupling is now
represented soundly, but Z3 still does not extract the six-way alternative.

For branch 4, every multi-special hole row in the six tracked models has a
strict special point even though singleton-special rows can fail.  This is a
conditional corpus horn only: global special mass six does **not** imply that
two special occurrences lie in one hole row, and existence of such a row is
still `UNKNOWN`.  The option `--multispecial-hole-row h` forces the conditional
horn and asserts the partial-mass negation only on the special fibers of row
`h`.  The tracked serious witness at row 23 is `UNSAT` in under one second of
solving; the unrestricted row-22 instance with residual type ledgers remains
`UNKNOWN` after 120 seconds.

The cleaner unconditional branch-4 candidate is global: the two punctured
regular classes miss exactly one point of each color, giving six special
occurrences without requiring hole incidence.  All tracked models have a
strict full fiber at one of these global special points.  This selector should
supersede the conditional multispecial-hole horn.  The option
`--global-special-only` encodes its partial-mass negation: the tracked serious
payload is `UNSAT` in 0.3 seconds of solving, while the unrestricted instance
with residual type ledgers remains `UNKNOWN` after 120 seconds.

## Proof decomposition exposed by the load

Every full point fiber has five rows, and each row degree is five or six, so
`D_p = 25 + H_p`, where `H_p` counts the high-degree rows containing `p`.
The outer incidence ledgers give the following observed rigid split, which
should be proved directly from their cardinality identities:

- branch 3: every exceptional-hole point has `D_p = 27`;
- branch 4: some exceptional-hole point has `D_p >= 28` (fresh samples attain
  28 or 29; the tracked branch-4 payload attains 29).

Branch 3 therefore needs the genuinely strict improvement below 27.  In
branch 4 the correct joint target is `C_p < 27 + special(p)` for some global
special point.  The point choice cannot be separated from its cover: in the
tracked branch-4 payload a maximum-load point `p=19` has target 29 but
fractional optimum about 27.4 (and least integral cover 28), so the tempting
stronger bound `C_p <= 27` at that selected point is false.  The positive
special slack still relaxes branch 4 relative to branch 3, but both require a
genuine coupled selector.

## Refuted shortcuts

- Requiring a triangle vertex, a middle-color hole point, raw averaging over
  all points, and unweighted averaging over exceptional-hole incidences all
  have durable or serious counterexamples elsewhere in the B.3 audit trail.
- The stronger claim that every point has full-fiber cover cost at most 27 is
  false.  On ten fresh outer designs, non-hole point optima reached values from
  28 through approximately 29.19, with 12--20 of the 24 points above 27 in
  each design.  Any proof must use the exceptional-hole/max-load structure.

## Remaining theorem gap

Prove, from the outer design plus the exact exceptional-hole DTB complement
partition, that a maximum-load hole point admits the bounded scaled cover.
Once its natural-number weights and positive scale are produced, the banked
actual-relation consumer closes the symmetric fractional residual relation and
hence the B.3 branch.
