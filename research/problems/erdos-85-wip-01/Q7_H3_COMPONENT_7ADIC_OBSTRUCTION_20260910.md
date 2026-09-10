# H3: a 7-adic obstruction to defect components10+12+24

2026-09-10, codex-sol-2. **Pending independent paper review.** This rules out
the candidate disconnected partition10+12+24 if the argument below is
accepted. It does not exclude connected H3 or solve Erdős85. No Lean proof
is supplied, and no shared goal is marked complete. Sol1 independently derived
the same7-adic obstruction in the combined3-adic report (review1584 PASS);
its second basis vector is twice ours, so its diagonal ratio is4 times ours.
This separate presentation and verifier are awaiting review1585.

## Graph-to-form setup

Use the reviewed component decomposition in
[Q7_H1_H3_SQUEEZE_20260910.md](Q7_H1_H3_SQUEEZE_20260910.md).
The partition10+12+24 can occur only in the H3 triple-support incidence
profile. Use the same field F=Q(a), a²-7a+3=0, real a>6, and b=7-a as in
[sol1's reviewed 3-adic argument](Q7_H3_COMPONENT_3ADIC_OBSTRUCTION_20260910.md)
(review1583, paper scope). Its graph-to-form argument applies to this
partition with the following different component Gram form.

For each component S_i, put w_i=a1_(S_i)-t restricted to S_i and zero
elsewhere. These form the3-dimensional rho=a-1 eigenspace of D over F.
The components have (size,per-high incidence,selected high-pair degree)
equal to(10,2,2),(12,2,0),(24,4,0). Thus sum t=3k and sum t²=3k+3r give

    p=||w1||²=10a²-12a+12=58a-18,
    q=||w2||²=12a²-12a+6=72a-30,
    ||w3||²=24a²-24a+12=144a-60=2q,
    G=p+3q=274a-108.

Disjoint support makes the Gram form diag(p,q,2q). All these norms are
positive in the chosen real embedding. The global w=w1+w2+w3 satisfies
Cw=aw. Since C commutes with D and is symmetric, the orthogonal complement
to w in this Perron space is C-invariant and defined over F. As in the
reviewed block proof, it lies in K, so C²=bI there.

## Explicit orthogonal basis

In component coordinates choose

    v1=(0,2,-1),   v2=(3q,-p,-p).

They are orthogonal to(1,1,1) for diag(p,q,2q), and to each other. Their
squared norms are6q and3pqG. Thus the restricted form, up to the nonzero
common scalar6q, is diag(1,delta), where

    delta=pG/2=(29a-9)(274a-108)=50024a-22866.

Norm_F/Q(b)=3 makes b nonsquare in F. Consequently a2-dimensional F-linear
operator with square bI has characteristic polynomial X²-b, hence trace0.
Selfadjointness of C for diag(1,delta) forces its matrix to be
[[u,delta*v],[v,-u]] for some u,v in F. Squaring yields

    u²+delta*v²=b.                                      (1)

No integral or orthonormal basis has been assumed.

## Obstruction at7

The defining polynomial has a simple root a=16 modulo49, reducing to2
modulo7. Hensel lifting embeds F into Q_7 with this residue. In that
embedding,

    b=40 modulo49,       delta=35 modulo49.

In particular b=5 modulo7 is a nonsquare unit and delta has valuation1.
If(1) had a solution, homogenize and multiply by a power of7 to obtain
U,V,Z in Z_7, at least one a unit, with U²+delta*V²=b*Z². Modulo7 the
nonsquare5 forces U,Z both divisible by7. Thus V is a unit. Modulo49,
U² and bZ² vanish but delta*V² does not, a contradiction.
This argument excludes arbitrary7-adic denominators, not merely integer
affine solutions.

## Exact checks and scope

[verify_q7_h3_component_7adic.py](verify_q7_h3_component_7adic.py) checks the
component moment formulas, field reductions, basis orthogonality and norms,
Norm(b)=3, simple Hensel residue, and all117649 residue triples modulo49.
The adjacent JSON records zero primitive solutions. The finite calculation
does not replace the graph-to-form or Hensel arguments; those need paper
review and eventual formalization.

Combined with the reviewed 3-adic exclusion of12+12+22 and the reviewed
component-size list, confirmation of this proof leaves connected46 as the
only H3 defect partition in either incidence profile. That is a connectivity
restriction, not an exclusion of H3 itself. Prior-art novelty is not claimed.
