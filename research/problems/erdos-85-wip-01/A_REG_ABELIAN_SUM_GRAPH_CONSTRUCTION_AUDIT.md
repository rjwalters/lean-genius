# A-REG: abelian sum-graph construction check

Node: A.5.3, construction-side challenge to A-REG. Date: 2026-09-06.
Status: uniform exclusions within a construction class; general A-REG open.

## Source and exact construction

Daza--Trujillo--Benavides, *Sidon sets and C4-saturated graphs*,
[primary paper, Sections 2--3](https://arxiv.org/pdf/1810.05262), uses the
strong Sidon convention: all ordered nonzero differences are distinct.
Its sum graph joins distinct x,y when x+y belongs to S. A vertex loses one
of the |S| potential neighbors exactly when 2x belongs to S.

Throughout, q=2^k with k>=1. A Sidon set S of size q in an abelian group G of order q² would give
the desired q-regular C4-free graph if S avoids 2G. Ordinary inverse-closed
Cayley exclusions do not address this sum construction. The arguments below
are direct counting, not conclusions attributed to the source.

## A uniform doubling-coset restriction

Write T=G[2], m=|T|=|G/2G|, h=|T intersect 2G|. Assume q>=2 and
S intersect 2G is empty. Distinct elements of S cannot differ by a
nonzero involution: the reversed ordered pair would give the same
difference. There are q(q-1) distinct nonzero differences, so

    q(q-1) <= q²-m, hence m<=q.                         (1)

Let c_i count S in the m cosets of 2G. The identity coset has c_0=0,
and sum c_i=q. The ordered differences in 2G number exactly
sum c_i(c_i-1). They avoid all h elements of T intersect 2G, including
zero. Therefore

    sum c_i²-q <= q²/m-h.

Cauchy--Schwarz on the m-1 nonidentity cosets gives
sum c_i²>=q²/(m-1). Combining yields the necessary condition

    q² <= m(m-1)(q-h).                                 (2)

In particular q<m(m-1). This rules out an unbounded construction with a
fixed number r of cyclic factors (m=2^r); it does not rule out growing r.

## Complete exclusions supplied by the count

For cyclic 2-groups, m=2 and h>=1. Equation (2) would give
q²<=2(q-1), which is impossible. Thus cyclic square-order groups cannot
give this loopless sum-graph construction.

For exponent at most four, write G=(Z/4)^a times (Z/2)^b. Since |G|=q²,
q=2^(a+b/2) and m=2^(a+b). Equation (1) forces b=0. Now T=2G has size q,
and S has at most one element in each T-coset by the involution argument.
Its size q makes it a transversal, including the identity coset. This
contradicts S intersect 2G being empty. Hence the entire exponent-at-most-
four class is excluded, uniformly in q.

Also, a group with exactly two cyclic factors, both of order at least four,
has m=h=4. Equation (2) becomes (q-6)²+12<=0, so this class is excluded.

## The equality m=q is excluded by relative-difference-set theory

Suppose m=q. The q(q-1) distinct ordered nonzero differences of S avoid
T, and `|G\T|=q²-q=q(q-1)`. Hence they cover every element of G\T
exactly once. In the standard convention, S is an abelian `(q,q,q,1)`
relative difference set with forbidden subgroup T.

Ganley's even-order classification, stated as Theorem 1.1 in
[Zhou, *(2^n,2^n,2^n,1)-relative difference sets and their representations*,
arXiv:1211.2942v2, PDF p.2](https://arxiv.org/pdf/1211.2942), forces
`G` to be isomorphic to `(Z/4)^k` when q=2^k. Zhou attributes this
case to Ganley, *On a paper of P. Dembowski and T. G. Ostrom*,
Arch. Math. 27 (1976), 93–98, and cites
[Jungnickel, *On a theorem of Ganley*, Graphs Combin. 3 (1987),
141–143](https://link.springer.com/article/10.1007/BF01788537), for a
shorter proof. Jungnickel's publisher abstract also states this classification.
The source theorem is used here as a published result, not claimed
Lean-formalized or reproved in this audit.

In that group T=2G. Since S has at most one point in each T-coset and
has q points, it meets every T-coset, including T itself. This contradicts
S intersect 2G being empty. Thus m=q is impossible. Both m and q are
powers of two, so the earlier m<=q improves uniformly to

```text
m <= q/2.
```

Together with (2), a surviving class must satisfy
`sqrt(q)<m<=q/2`. This still leaves growing-rank, higher-exponent
parameters; it does not exclude every abelian sum graph.

## Stop condition and remaining gap

These exclusions do not cover all abelian 2-groups. For example the
necessary numerical conditions allow q=16, m=h=8 (as for Z/8 times
Z/8 times Z/4). This is only a compatible parameter set, not a Sidon set
or graph witness. A growing-rank, higher-exponent construction remains
unresolved, as does any passage from arbitrary graphs to sum graphs.
No group enumeration, Lean formalization, or general branch exclusion is
claimed. Stop this bounded check here rather than enumerate the survivors.

Independent review: Sol1, squad #1423 PASS, checked the primary source,
both capacity inequalities, all three class exclusions, and the remaining
scope. This is a prose result, not a Lean theorem.

## Quotient autocorrelations: a survivor with a forced mixed defect

Follow-up by Sol2, with Sol3's independent uniform survivor calculation.
This tests the full doubling-quotient counts, not Sidon sets or groups.
Assume h=m, so all involutions lie in 2G. Index the coset multiplicities
by the elementary abelian quotient Q=G/2G. For each nonzero t in Q,
ordered differences in its coset number

```text
R(t) = sum_(a in Q) c_a*c_(a+t) <= |2G| = q²/m.        (3)
```

### Exact profile at q=16, m=h=8

Here c_0=0, sum c_a=16, and sum c_a²<=40. All seven nonidentity
counts are positive: with only six occupied cosets, Cauchy would give
sum c_a²>=256/6>40. Put d_a=c_a-2 on the seven nonzero cosets.
Then sum d_a=2 and sum d_a²<=4. The only multisets are

| Nonzero-coset counts | Outcome |
|---|---|
| two 3s and five 2s | fails (3) |
| one 4 and six 2s | survives (3) |
| three 3s, one 1, and three 2s | fails (3) |

For the first profile, the shift joining the two 3-locations has
autocorrelation 34, exceeding 32. For the third, subtract the constant
vector 2 on all eight cosets. The deviation vector has value -2 at 0,
-1 at the 1-location b, and +1 at the three 3-locations. Its sum is zero.
At shift b the ordered 0,b pair contributes 4 to its autocorrelation;
all other contributions are nonnegative. Thus R(b)>=32+4>32.

For the remaining profile, with c_a=4 at a nonzero a,

```text
R(a)=24,              R(t)=32 for t!=0,a.
```

An exact standard-library check of all 168 labeled profiles above leaves
precisely the seven choices for the 4-location. The three-case argument
proves completeness; the finite arithmetic is only a verification.

### Why these counts cannot exclude the whole growing-rank class

For every q=2m with m>=8 and h=m, the same profile

```text
c_0=0, c_a=4, c_t=2 for all t!=0,a
```

has total q, squared mass 4m+8<=5m=q²/m+q-h, and
`R(a)=4m-8`, `R(t)=4m` for every other nonzero t. Thus it passes
both the scalar and full quotient-autocorrelation inequalities uniformly.
This is only a multiplicity profile, not a Sidon construction. It is
not asserted to classify all profiles when q>16.

There is nevertheless a consequence for any actual realization of this
profile. Every coset t+2G with t!=0,a is saturated by the distinct
ordered differences. The defect graph of the sum graph is the Cayley
graph whose connection set is the nonzero differences absent from S-S:
off the diagonal, A² has entry one exactly at represented differences.
All its connection elements therefore lie in

```text
L = pi^(-1)({0,a}),       |L|=2|2G|=4q,
```

where pi:G->Q. Since Q has exponent two, L is a subgroup. Every defect
component is contained in an L-coset, hence has at most 4q vertices.
For q>=16 the defect is necessarily disconnected. At q=16, m=h=8 this
consequence covers every admissible profile by the classification above;
for larger q it applies only to the displayed profile.

Every T-coset is also a clique in the defect graph, because all nonzero
involutions are missing differences. Here |T|=m>=8, so the defect is
nonbipartite. This directs that construction family into NONBIP-MIXED if realized.
It does not exclude mixed defect components, other admissible profiles,
or other abelian group parameters. The scalar/autocorrelation exclusion
route is stopped at its explicit uniform survivor; no realization search
or additional Lean wrapper follows from this calculation.

## Inverse-theorem literature: the missing implication is conjectural

Sol1's follow-up checked [Eberhard--Manners, *The apparent structure of
dense Sidon sets*, Section 5](https://arxiv.org/pdf/2107.05744), published
in Electronic Journal of Combinatorics 30(1) (2023), P1.33. Their strong
Sidon convention agrees with the one here. Conjecture 5.1 proposes an
equivariant projective-plane completion with only o(|G|) added points and
lines. Conjecture 5.2, for dense maximal Sidon sets, instead proposes that
the missing differences, including zero, form a union of O(1) subgroups.
Neither statement is supplied as a theorem. A bounded union of subgroups
is also weaker than the single subgroup required for the RDS argument.

There is a concrete warning against dropping hypotheses: the set
`S={0,1,4,6}` in Z/16 has twelve distinct ordered nonzero differences,
namely `+/-1,...,+/-6`. Its missing-difference set including zero is
`{0,7,8,9}`, which is not a subgroup since `7+7=14` is absent. Thus exact
square-root size alone does not imply a subgroup leave. This finite
example meets 2G, so it is not a loopless sum-graph candidate and does not
refute either asymptotic conjecture. Direct enumeration of its twelve
differences verifies the stated control; no graph census is involved.

The targeted inverse search stops here. What is missing is a proved
completion or subgroup-rigidity implication under the actual loopless
Sidon hypotheses. Even excluding every such sum graph would leave the
separate, unproved passage from arbitrary A-REG graphs to this construction
class. No new Lean theorem or general A-REG exclusion is asserted.

## Nonabelian product-sum graphs reduce to this class

The outside-first screen included Byrne--Tait,
[New constructions and bounds for nonabelian Sidon sets with applications to Turán-type problems](https://doi.org/10.4153/S0008414X26102314)
(2026), whose nonabelian Sidon constructions concern directed extremal
problems. They do not automatically supply an undirected product-sum graph.
The following direct argument explains the obstruction; it is not a theorem
attributed to that paper.

Let G be any group and S a subset. Define the simple graph by

    x adjacent to y iff x != y and xy belongs to S.

Assume this relation is symmetric and the graph is C4-free and connected.
Then **G is abelian**, regardless of whether the raw product relation has
loops.

First, symmetry makes S invariant under conjugation. Indeed, for s in S
and any x, apply symmetry to x and x^{-1}s to obtain x^{-1}sx in S.
If those two vertices coincide, s=x² and the desired conjugate is s itself.
Thus every inner automorphism acts on the simple graph.

For s,t in S put g=s t^{-1}. If g=1 then s=t. Otherwise, when t is
neither 1 nor g, t is a common neighbor of 1 and g: both t and gt=s
belong to S. Conjugation by g fixes 1 and g, so it preserves their common
neighbors. C4-freeness permits at most one such neighbor, forcing

    g t g^{-1} = t.

If t is 1 or g, this equality holds immediately as well. Consequently
s=gt commutes with t. All elements of S therefore commute pairwise, and
H=<S> is abelian. Every neighbor y of x in H satisfies y=x^{-1}s in H.
The component containing 1 is contained in H, so connectedness gives G=H.
Equivalently, noncommuting s,t would explicitly create a C4 on
1,t,g,g t g^{-1}; noncommutation ensures that these four vertices are distinct.

For an A-REG candidate, connectedness is automatic. In a q-regular
C4-free graph each component has at least q(q-1)+1 vertices: the q sets
N(y) minus {x}, y in N(x), are pairwise disjoint and each has q-1 elements.
Two such components require more than q² vertices. Thus a q-regular
C4-free product-sum graph on a group of order q² must be abelian.

There is one further issue before applying the preceding Sidon audit.
The degree at x is |S|-1[x² in S]. Regular degree q therefore has exactly
two possibilities: |S|=q and no square lies in S, or |S|=q+1 and every
square lies in S. For binary q>=4 the second possibility is impossible.
Now write the abelian group additively; its order is a power of two.

If 2G is nontrivial, choose a nonzero involution z in 2G. Since 2G is
contained in S, every pair x,x+z is an edge. Translation by z preserves
all edges because 2z=0. Any other edge xy would give the C4

    x, y, y+z, x+z, x.

Hence C4-freeness forces degree at most one. If 2G is trivial, the group
is elementary abelian and the product-sum graph is an ordinary Cayley
graph with connection set S minus {0}. Two distinct nonzero connections
s,t give the C4 0,s,s+t,t, so degree is again at most one.

Therefore every binary square-order q-regular C4-free graph from this
entire product-sum construction has an abelian ambient group, |S|=q,
and S disjoint from 2G. With no deleted loops, C4-freeness implies that
every nonzero ordered difference in S is unique: representations g=s-t
correspond to common neighbors t of 0 and g. These are exactly the
hypotheses of the preceding abelian audit, including its remaining range
sqrt(q)<|G[2]|<=q/2.

This closes the nonabelian and all-loops variants of this construction
escape. It does not exclude the remaining abelian Sidon class or general
A-REG graphs. Ordinary Cayley graphs (x^{-1}y in S), twisted product
relations, and non-group constructions are outside this reduction.
