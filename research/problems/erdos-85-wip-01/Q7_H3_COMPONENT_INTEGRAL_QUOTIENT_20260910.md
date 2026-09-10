# H3 defect connectivity via integer neighbor counts — 2026-09-10

Owner: codex-sol-2. **Corrected paper proof: review1592 PASS.** This is an alternative
to the reviewed3-adic/7-adic proofs of H3 defect connectivity. It uses the
integral Perron quotient method from
[sol3's H5 argument](Q7_H5_COMPONENT_INTEGRAL_QUOTIENT_20260910.md)
(review1588 PASS), followed by an exact trace-and-determinant contradiction.
It does not exclude connected H3. No Lean proof or novelty claim is supplied.

## Common setup and integrality

Use the reviewed H3 component classification: the only disconnected
partitions are12+12+22 and, in the triple profile,10+12+24. Set
F=Q(a), a²-7a+3=0 with a>6, and z=a1-t. Each D-component has a positive
Perron vector z_i obtained by restriction. Because CD=DC, write
(Cz_j)|S_i=m_ij z_i, with m_ij in F. Every component in these partitions
has both empty-support and singleton-support vertices.

Write m_ij=alpha+beta*a with rational alpha,beta. For v in S_i, let p_v
be the number of C-neighbors in S_j and q_v their total high-support count.
Irrational coefficient comparison in a p_v-q_v=m_ij(a-t_v) gives

    p_v=alpha+7beta-beta*t_v,
    q_v=alpha*t_v+3beta.

Comparing vertices with t=0 and t=1 makes beta=p_0-p_1 and
alpha=p_0-7beta integers. At t=0, Ct=3 implies0<=3beta<=3, and the
C-degree is7. Therefore, in every ordered component pair,

    alpha in Z, beta in {0,1}, 0<=alpha+7beta<=7.       (1)

This is the essential actual-neighbor-count input missing from the
rational conic relaxation.

## Partition12+12+22

The component norms are g=72a-30 twice and j=130a-48. For a12/22 pair,
write m_12,22=alpha+beta*a and m_22,12=gamma+delta*a. Weighted symmetry
g*m_12,22=j*m_22,12 gives

    alpha=-12beta+21delta, gamma=-3beta+5delta.

Checking beta,delta in{0,1} against(1) leaves only alpha=beta=gamma=delta=0:
the three nonzero choices give alpha+7beta equal to21,-5,16.
Thus the two12-components have no C-edge to the22-component: a zero
quotient entry gives Cz_j=0 on the source, and z_j is strictly positive.
Their union is a closed24-vertex C4-free C-subgraph of minimum degree6,
which is impossible since such a graph needs at least1+6*5=31 vertices.

## Partition10+12+24

In this case the10-component contains the triple-support vertex, three
singleton vertices and six empty vertices. The12-component contains six
singletons and six empty vertices. Norms in this order are

    p=58a-18, q=72a-30, 2q=144a-60.

For the10/24 pair, weighted symmetry gives

    alpha=2beta-6delta, gamma=7beta/2-9delta.

Integrality of gamma forces beta=0; then nonnegativity in(1) forces
delta=0, so both quotient entries vanish.
For the10/12 pair, weighted symmetry gives

    alpha=2beta-3delta, gamma=7beta-9delta.

The only possibilities under(1) are zero or

    (alpha,beta,gamma,delta)=(-1,1,-2,1),
    m_10,12=a-1, m_12,10=a-2.

The nonzero option cannot be rejected from the triple vertex's neighbor
count alone: it requires three empty neighbors in the12-component, which
has six empties. Instead use the entire3-dimensional quotient.

For the12/24 pair the norms are q and2q, so weighted symmetry gives
m_12,24=2m_24,12. Coefficient comparison and beta in{0,1} force both
beta coefficients to vanish. The entries are therefore2y and y for an
integer y in{0,1,2,3}. Let x in{0,1} choose the zero/nonzero10/12 option.
Since the global vector z=z1+z2+z3 satisfies Cz=az, every quotient row sums
to a. Thus its diagonal entries are determined, and the entire quotient is

    M = [x+(1-x)a,       x(a-1),                 0;
         x(a-2),         2x-2y+(1-x)a,           2y;
         0,              y,                     a-y].

The global z line has eigenvalue a. Its orthogonal complement in the
Perron space lies in K and is2-dimensional over F, with C²=bI, b=7-a.
Since Norm_F/Q(b)=3 is not a rational square, b is not a square in F.
Consequently the restriction there has characteristic polynomial X²-b.
It follows that tr(M)=a and det(M)=-ab=-3.

But the displayed matrix has trace(3-2x)a+3x-3y. Irrationality of a gives
x=1 and y=1, leaving the unique matrix

    [1, a-1, 0; a-2, 0, 2; 0, 1, a-1].

Its determinant reduces modulo a²-7a+3 to9-23a, which cannot equal-3
because a>6. This contradiction excludes10+12+24 without local fields.

Both disconnected H3 partitions are therefore impossible. Together with
the reviewed classification, D is connected. The separately reviewed
bipartite-component parity then makes it nonbipartite. This reproduces the
connectivity conclusion without Hensel lifting or p-adic denominator arguments.

## Verification scope

[verify_q7_h3_integral_quotient.py](verify_q7_h3_integral_quotient.py) derives
the three exact linear systems and exhausts bounded integer coefficient
pairs satisfying(1) in both directions, then the full quotient trace and
determinant. Its JSON preserves the cross-entry tuples and unique trace
candidate. The graph-to-Perron reduction, integrality deduction,
positive-weight support argument, trace/determinant restriction, and first
partition two-step counting contradiction are
paper proofs; finite tuple enumeration is not a graph solver or a complete
formalization. No further profile exclusion follows here.

## Lean verification of the final eight quotients

`proofs/Proofs/Erdos85H3IntegralPerronQuotient.lean` proves a stronger final
scalar fact: every x in{0,1}, y in{0,1,2,3} has
tr(M²)>a²+2(7-a), assuming a>6 and a²-7a+3=0. No assumption on tr(M)
or det(M) is needed for this finite step. For y=0,1,2,3 the differences are

- x=0: 16a-20, 10a-11, 4a+16, 61-2a;
- x=1: 10a-11, 8a-10, 6a+9, 4a+46.

All are positive since6<a<7. The actual graph requires equality because
the Perron-space restriction splits its global a-eigenline and a2-space
whose square is(7-a)I. Thus this supplies another final contradiction.
Local Lean compilation and axiom audit passed, with only propext,
Classical.choice and Quot.sound; independent scalar review1594 is pending.
The graph-to-quotient and component classification remain paper arguments.
