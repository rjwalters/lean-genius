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
