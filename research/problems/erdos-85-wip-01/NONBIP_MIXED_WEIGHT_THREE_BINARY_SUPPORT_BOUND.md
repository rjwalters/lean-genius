# A graph-level support bound for the binary incidence kernel

Node: A.5.3 / NONBIP-MIXED / weight-three triangle-free defect.
Date: 2026-09-06. Status: uniform necessary bound, not branch exclusion.

## Why the complete-design rank theorem cannot be imported

Jungnickel–Tonchev, *Counting Steiner triple systems with classical
parameters and prescribed rank*, Theorem 2.1(ii), states that the dual
binary block code of a rank-deficient **Steiner triple system** on v
points has every nonzero word of weight `(v+1)/2`.
[Primary paper, PDF pp.3–4](https://arxiv.org/pdf/1709.06044).
That hypothesis covers every pair. Our B omits both defect edges and
the pairs reserved for H-neighborhood triples. Even `[H B]` is only a
partial system with leave D. Neither incidence matrix inherits the
complete-design weight formula from this source.

Instead, the following direct argument uses the actual partial design
and triangle-free D, beyond the relaxed matrix counterexamples.

## Hypotheses and the elementary support window

Let q be even, q>=8. Let H be a simple cubic graph on C, where |C|=3q.
Let B be binary with q(q-3) columns of size three and all row sums q-3.
Suppose D is simple and triangle-free and the **integer** identity holds:

```text
H² + BBᵀ = (q-1)I + J - D.
```

The columns of `[H B]` are triples with no repeated pair; the uncovered
pairs are exactly the edges of D. No commutation or cross-completion
hypothesis is needed for the support bound below.

Take a nonzero z in ker(Bᵀ) over F2, with support W and size w. Every
B-triple meets W in zero or two points. Exactly `(q-3)w/2` triples meet W,
since each W-point has replication q-3. Thus w is even. The total number
of triples gives `w<=2q`. Each W-point has q-3 distinct partners in W,
so `w>=q-2`. More precisely, for the residual pair graph
`L=2I+J-D-H²`, the induced graph L[W] is (q-3)-regular.

These elementary observations were independently derived by Sols2/3;
they do not by themselves contradict a nonzero codeword.

## Triangle-freeness improves the upper endpoint

Put `t=2q-w>=0` and `U=C\W`, so `u=|U|=q+t`.
Exactly `(q-3)t/2` B-triples lie wholly in U, and they cover exactly
`3(q-3)t/2` U-pairs. All other B-triples meet U in one point and cover
no U-pair.

For each x in C, put `k_x=|N_H(x) intersect U|`. The H-neighborhood
triple at x covers `binom(k_x,2)` U-pairs. Since 0<=k_x<=3,
`binom(k_x,2)<=k_x`, and cubic regularity gives
`sum_x k_x=3u`. Thus H's triples cover at most 3u U-pairs.
The integer Gram identity makes all these covered pairs disjoint, giving

```text
e(D[U]) >= u(u-1)/2 - 3u - 3(q-3)t/2.
```

Mantel's bound for triangle-free D[U] is `e(D[U])<=u²/4`.
Combining and substituting t=2q-w, u=3q-w yields

```text
u² - 14u - 6(q-3)t <= 0,
w² - 4w <= 3q² + 6q.                              (S)
```

Equivalently `w<=2+sqrt(3q²+6q+4)`. Together with evenness and the
elementary window, this gives the following sample bounds (arithmetic
evaluation of a uniform inequality, not enumeration of graphs):

| q | Minimum nonzero w | Maximum w from (S) and w<=2q |
|---|---:|---:|
| 16 | 14 | 30 |
| 32 | 30 | 58 |
| 64 | 62 | 114 |
| 128 | 126 | 224 |

For w=2q, (S) becomes `q²-14q<=0`. Hence **no support of size 2q exists
when q>14**. In particular, a B consisting entirely of triples with two
points in a fixed 2q-set and one in its q-point complement cannot meet
the integer Gram with triangle-free D. This cuts the natural tripartite
design proposal: if every B-triple takes one point from each of three
q-point parts, any union of two parts would be such a forbidden support.
This conclusion does not require an actual construction of that proposal.

## Remaining scope

This is a prose proof; no Lean formalization is claimed. The polynomial
substitution and table were checked independently with exact arithmetic.
The support intervals remain nonempty. We have not proved that B has full
binary rank, that H fails to preserve its binary kernel, or that every
rank-deficient B is tripartite. Those would be new claims. The exact
modulo-two cross-completion criterion remains in
`NONBIP_MIXED_WEIGHT_THREE_DESIGN_LITERATURE_AUDIT.md`.

The bounded test rules out importing the complete-design weight theorem
and the tripartite repair in this triangle-free branch. It does not justify
another fixed-q construction search or a chain of support-bound wrappers.
