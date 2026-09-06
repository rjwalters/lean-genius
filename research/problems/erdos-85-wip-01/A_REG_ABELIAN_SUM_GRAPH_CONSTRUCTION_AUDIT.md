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
