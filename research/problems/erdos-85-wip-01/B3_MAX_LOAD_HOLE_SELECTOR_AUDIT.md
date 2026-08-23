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
