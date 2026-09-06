# Fixed loopless templates cannot amplify square-order witnesses indefinitely

Node: root strategy, propagation of finite witnesses to an unbounded family.
Date: 2026-09-06. Status: elementary uniform prose proof, no Lean claim.

A possible shortcut to the cofinal drop goal is to replace vertices of a
fixed finite witness by larger sets while keeping all edges over edges of
that witness. This always gives a graph homomorphism to the fixed base.
The following obstruction applies without any balance or equitability
assumption on the replacement sets.

**Theorem.** Let G be a nonempty q-regular simple C4-free graph on n<=q²
vertices, with integer q>=2. If G admits a proper coloring with c colors,
then

```text
q² <= c(c-1)(q-1),          hence q <= c(c-1)-2.        (1)
```

Consequently, if G maps homomorphically to a fixed finite loopless graph H,
then (1) holds with c=chi(H). No fixed such H can support an unbounded
degree family of these graphs. This covers both n=q² and n=q²-1.

## Independent-set count

Let S be a nonempty independent set, with a=|S|. Since q>0, a<n.
For each vertex v outside S put r_v=|N(v) intersect S|. Regularity and
C4-freeness give, respectively,

```text
sum r_v = q a,
sum r_v(r_v-1) <= a(a-1).
```

The second inequality counts ordered distinct pairs in S, each of which
has at most one common neighbor. Cauchy--Schwarz then gives

```text
q² a²/(n-a) <= sum r_v² <= a(a-1)+q a,
q² a <= (n-a)(a+q-1),
a²+(q²-n+q-1)a <= n(q-1).                              (2)
```

Take S to be a largest color class, so a>=n/c. The polynomial on the
left of (2) is increasing for nonnegative a, since n<=q² and q>=2.
Substitute n/c, divide by n>0 and multiply by c² to obtain

```text
c q²-(c-1)n <= c(c-1)(q-1).
```

Its left side is at least q² because n<=q², proving the first part of (1).
Finally `q²/(q-1)=q+1+1/(q-1)`. Since c(c-1) is an integer, the second
part follows, including q=2.

## Consequence and stopping point

A homomorphism to loopless H pulls back any proper coloring of H.
Its vertex fibers are independent, but may have arbitrary sizes; edges
between fibers may be arbitrary subgraphs of the allowed bipartite blocks.
Thus the bound is not limited to balanced blowups or regular covering maps.
Categorical graph products that retain a projection to a fixed loopless
factor are also covered.

This excludes a method of amplifying a finite example; it does not exclude
arbitrary q-regular graphs at square order. A construction whose template
chromatic number grows with q is outside the conclusion, as is a map to a
template with loops. The known polarity family is not contradicted: no
homomorphism to one fixed loopless template has been established for it.
The root still needs an unbounded sequence of actual drop pairs, and no
finite drop alone has been promoted to such a family by this argument.
