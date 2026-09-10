# H3: local arithmetic obstructions to disconnected defect graphs

2026-09-10, codex-sol-1. **Independent paper reviews #1583 and #1584 PASS (codex-sol-2).** The two arguments below exclude both remaining disconnected component partitions. They do not exclude connected D or H3 as a whole. No new graph construction is asserted.

## Exact graph-to-form argument

Use the block setup and component balance in `Q7_H1_H3_SQUEEZE_20260910.md`. Put F=Q(a), where a²-7a+3=0 and the real embedding has a>6. Write b=7-a and rho=a-1. Suppose the low defect graph has components S1,S2,S3 of orders12,12,22.

For each component set w_i=a 1_(S_i)-t restricted to S_i, extended by zero. Each w_i is a rho eigenvector of D. They have disjoint support, hence orthogonal Gram matrix diag(g,g,h), where the component support sums and square sums give

```
g = 12a²-12a+6 = 72a-30,
h = 22a²-24a+18 = 130a-48,
G = 2g+h = 274a-108.
```

The global vector w=w1+w2+w3 has Cw=aw. Since CD=DC, the component Perron space is C-invariant. Its orthogonal complement to w is two-dimensional over F and lies in K=ker(B) intersect1-perp: the other fixed D eigenvector in span(1,t) has eigenvalue distinct from rho, and the high-difference image has D eigenvalue-1. Thus C²=bI on that two-dimensional space.

An orthogonal basis of this space is

```
v1=w1-w2,
v2=h(w1+w2)-2g w3.
```

Its Gram matrix is diag(2g,2g*h*G). Consequently, after cancelling the common nonzero scalar2g, the form is diag(1,delta), where delta=hG. The restriction of C is defined over F and selfadjoint for this form. Also b is not a square in F, since its field norm is3. A two-dimensional operator with square bI therefore has trace zero, and its selfadjoint matrix takes the form

```
[[u, delta*v], [v, -u]],     u,v in F.
```

Squaring forces the necessary conic equation

```
u²+delta*v²=b.                                      (1)
```

## Local obstruction

The polynomial a²-7a+3 has a simple root a=4 modulo9 (a=1 modulo3). Hensel lifting gives an embedding F into Q3 with a congruent to4 modulo9. In this embedding

```
b=7-a = 3 (mod9),
delta=(130a-48)(274a-108) = 1 (mod9).
```

Equation(1) is impossible over Q3. If a solution existed, homogenize and multiply (u,v,1) by a power of3 to obtain integral3-adic coordinates U,V,Z with at least one a unit. Reduction modulo3 of U²+delta V²=b Z² forces U,V both divisible by3. Primitivity forces Z a unit. Modulo9 the left side is then0 while the right side is3, a contradiction.

Equivalently, the ternary conic U²+V²=3Z² has no primitive solution modulo9. The attached verifier enumerates all729 residue triples and confirms this, independently of the symbolic Gram computations it also checks.

## The remaining partition10+12+24: obstruction at7

The same Perron-space argument applies to the other possible disconnected triple-support case. In component order10,12,24, the orthogonal norms are

```
h0=10a²-12a+12=58a-18,  g=72a-30,  2g,
G=h0+3g=274a-108.
```

An explicit orthogonal basis perpendicular to the global vector is

```
v1=2w2-w3,
v2=6g*w1-2h0*(w2+w3).
```

The Gram matrix is diag(6g,6g*delta2), where delta2=2h0G. Thus the same selfadjoint square equation requires u²+delta2*v²=b over F.

Now choose the simple root a=16 modulo49, which is a=2 modulo7. Hensel lifting embeds F in Q7 with

```
b=40 (mod49),   delta2=42 (mod49).
```

A primitive homogenized solution U,V,Z over Z7 is impossible. Modulo7 its equation becomes U²=5Z². Since5 is a nonsquare modulo7, both U and Z are divisible by7. Primitivity makes V a unit. Modulo49 the equation would then require42V²=0, which is impossible. The verifier independently enumerates all49³ residue triples and finds no primitive solution.

## Verification and scope

`verify_q7_h3_component_3adic.py` verifies the field reductions for g,h,G, orthogonality and norm ratio of v1,v2, the simple Hensel residue, and the complete primitive mod9 and mod49 obstructions for the two partitions. Its JSON records exact outputs. It does not formalize Hensel lifting or the graph-to-form argument. Independent paper review1583 passed the3-adic argument and review1584 passed the7-adic argument, including the graph-to-form steps. The finite residues are additionally proved in `proofs/Proofs/Erdos85Q7ComponentConicResidues.lean`, which compiled with only `propext` in each theorem's axiom list; this does not formalize the remaining graph or local-field reductions.

Therefore D must be connected for both H3 incidence profiles (reviewed paper-proof scope). Combined with the reviewed even number of bipartite components, D is then nonbipartite. This narrows the residual spectral interval strictly at both ends, but the connected H3 cases remain untouched by this exclusion.
