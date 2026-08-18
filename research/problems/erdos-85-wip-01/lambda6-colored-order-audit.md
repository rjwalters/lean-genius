# Lambda-six colored-order audit

`check_lambda6_colored_order.py` independently enumerates the same direct
120-variable `R` equations as `check_lambda6_classification.py`.  For every
labeled solution it constructs the forced defect matrix

`D = I + J - H² - R`

and computes degrees in `H ∩ D`.  In a graph realization this intersection
is the triangle-free-colored part of the internal ambient two-factor.
Therefore `orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two`
requires every such degree to be zero or two.

Run from this directory with:

```text
python3 check_lambda6_colored_order.py
```

The exact valid census is:

| internal cycle type | defect class | valid labeled models | colored order |
|---|---:|---:|---:|
| `[10,6]` | bipartite, `t(D)=0` | 2 | 16 |
| `[10,6]` | `t(D)=30` | 2 | 16 |
| `[10,6]` | `t(D)=40` | 2 | 6 |
| `[5,5,3,3]` | bipartite, `t(D)=0` | 120 | 0 |
| `[5,5,3,3]` | `t(D)=30` | 120 | 10 |
| `[5,5,3,3]` | `t(D)=40` | 120 | 10 |

Thus only 6 of the 144 labeled `[10,6]` relation models survive the local
parity condition; all 360 `[5,5,3,3]` models survive it.  In an all-size-16
assembly satisfying the mu-three terminal, commit `a133bb793f` additionally
forces the four component colored orders to sum to 16.  Commit `1e8c1fe3d7`
proves graph-side that the colored support propagates along whole internal
ambient cycles.
