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

## Proof decomposition exposed by the load

Every full point fiber has five rows, and each row degree is five or six, so
`D_p = 25 + H_p`, where `H_p` counts the high-degree rows containing `p`.
The outer incidence ledgers give the following observed rigid split, which
should be proved directly from their cardinality identities:

- branch 3: every exceptional-hole point has `D_p = 27`;
- branch 4: some exceptional-hole point has `D_p >= 28` (fresh samples attain
  28 or 29; the tracked branch-4 payload attains 29).

Thus branch 4 only needs a maximum-load hole cover of cost at most 27, whereas
branch 3 needs the genuinely strict improvement below 27.  The exact DTB
complement partition at an exceptional hole is therefore most urgently needed
for branch 3.

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
