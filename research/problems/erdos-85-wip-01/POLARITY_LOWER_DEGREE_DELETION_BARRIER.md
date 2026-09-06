# Lower-degree square witnesses cannot come from moderate polarity deletions

Node: root cofinal-drop divergence, alternative existence jaws from A.1.
Date: 2026-09-06. Status: uniform prose proof; no Lean claim.

The proposed shortcut is to delete vertices from the known q-regular
polarity core on q²-1 vertices, lower the target degree to d, and obtain
a new witness at d²-1 whose nonexistence partner might be easier.
The following bound stops this route throughout a broad degree range.
It is a restriction on this source construction, not on arbitrary graphs.

Let q>=16 be a power of two, and let Gamma have vertex set F_q² minus
zero, with adjacency omega(u,v)=1 for the alternating determinant form.
If a nonempty subgraph H of Gamma has minimum degree at least d, then

```text
|V(H)| >= (q²-1)(d-sqrt(q))/(q-sqrt(q)).                 (1)
```

In particular, if `2 sqrt(q) <= d <= q-1`, then `|V(H)| > d²`.
This includes arbitrary vertex deletions and further edge deletions.

## Proof of the spectral bound

Partition the N=q²-1 nonzero vectors into their q+1 scalar rays, each
of size q-1. Let E be block diagonal with an all-ones block on each ray,
and let A be Gamma's real adjacency matrix. Each vertex has q neighbors.
Distinct independent vectors have exactly one common neighbor; distinct
vectors on the same ray have none. Therefore

```text
A² = q I + J - E.
```

For z perpendicular to the all-ones vector, positive semidefiniteness of E
gives `||Az||² <= q ||z||²`, hence `z^T A z <= sqrt(q) ||z||²`.
For W=V(H), write its indicator as `1_W=(n/N)1+z`. Then
`||z||²=n-n²/N`, and

```text
d n <= 2|E(H)| <= 1_W^T A 1_W
    <= q n²/N + sqrt(q)(n-n²/N).
```

Dividing by n>0 and rearranging proves (1).

For the strict comparison with d², put s=sqrt(q)>=4 and
`F(d)=(q²-1)(d-s)/(q-s)-d²`. This is a concave quadratic, so its
minimum on [2s,q-1] occurs at an endpoint. Direct simplification gives

```text
F(2s)  = s³-3s²+s+1 > 0,
F(q-1)= s²-s-3-1/s > 0.
```

Both are positive for s>=4, completing the proof.

## Scope and stopping point

The original degree q is deliberately outside the excluded interval:
Gamma itself has q²-1 vertices. Degrees below 2 sqrt(q), constructions
using added edges or vertices, and possible drops at orders above d²
remain outside this argument. No claim of arbitrary square-order
nonexistence follows. The remaining general A-REG gap is unchanged.

The low-degree exception is real: if q=r², restricting to
`F_r²` minus zero gives an induced copy of Gamma_r, of degree r and
order r²-1=q-1. Thus a claim excluding all lower-degree square witnesses
would be false. This subfield deletion only recovers an already-known
existence jaw; it supplies no new nonexistence result.

For comparison, retaining d+1 complete scalar rays gives an exactly
d-regular induced subgraph: each pair of distinct rays is joined by a
perfect matching. Its order is `(d+1)(q-1)`, which exceeds d² for
1<=d<=q-1 since the difference is `d(q-1-d)+q-1`.
Thus these immediate lower-degree witnesses also miss the square jaw.

Literature context: [Tait and Timmons, *Small dense subgraphs of polarity
graphs and the extremal number for the 4-cycle*, arXiv:1502.02722,
Lemmas 2.1-2.2](https://arxiv.org/pdf/1502.02722) use the spectrum and
indicator-vector decomposition for full, looped projective polarity
graphs. Their graph has q²+q+1 vertices and row sum q+1; those parameters
are not imported here. The core identity and inequality above are
derived directly. Their edge-count constructions likewise do not by
themselves supply a minimum-degree witness at a specified order.

## Consequence for embedding into a larger polarity plane

The same indicator argument does apply separately to the full, looped
polarity graph P of any projective plane of order r. Lemma 2.1 of the
source above gives row sum r+1 and nonprincipal eigenvalues ±sqrt(r).
Loops contribute one to its adjacency matrix diagonal. For a loopless
subgraph H of P, `2|E(H)| <= 1_W^T A_P 1_W` still holds. Thus

```text
n >= (r²+r+1)(d-sqrt(r))/(r+1-sqrt(r))
  = (r+sqrt(r)+1)(d-sqrt(r)).                           (2)
```

For r>=16 and `2 sqrt(r) <= d <= r-1`, this is strictly greater than d².
Indeed, with s=sqrt(r), the difference is again concave in d; its
endpoint values are `s(s²-3s+1)` and `s²-2s-2`, positive for s>=4.

Consequently a q-regular graph on q² vertices cannot be a subgraph of
a polarity graph of a projective plane of order r satisfying

```text
r >= 16,                  q+1 <= r <= q²/4.
```

In fact the same exclusion holds for an ordinary incidence embedding,
without a polarity, as observed independently by Sol3. Let M be the
point-line incidence matrix of any projective plane of order r. Then
`MM^T=rI+J`, and all row and column sums equal r+1. For point and line
subsets P,L each of size n, subtract their constant indicator components
to obtain x,y of squared norm `n-n²/N`. On the zero-sum spaces M has
operator norm sqrt(r), so

```text
1_P^T M 1_L <= (r+1)n²/N + sqrt(r)(n-n²/N).
```

An injective incidence-preserving embedding of a configuration with
n points, n lines, and at least d incidences per point contributes at
least dn incidences between P and L. Rearrangement gives exactly (2).
Preserving nonincidences is unnecessary for this upper-bound argument.

Apply this to the neighborhood configuration of a q-regular C4-free
graph on q² vertices: there are q² points and q² neighborhood lines,
each of size q. For q>=2 these lines are distinct, because equal
neighborhoods would produce a C4. It follows that this configuration
cannot embed in any projective plane with `r>=16` and
`q+1<=r<=q²/4`, even without extending the neighborhood involution.

The exact same inequality excludes the wider interval

```text
q >= 8,                    q+1 <= r <= (q-2)².         (3)
```

To see this, fix q and put s=sqrt(r). The required lower bound minus
q² is `F(s)=(s²+s+1)(q-s)-q²`. Its derivative is
`-3s²+2(q-1)s+(q-1)`, with one negative and one positive root.
Thus on the positive axis F first increases and then decreases, so its
minimum on `[sqrt(q+1),q-2]` occurs at an endpoint. There the values are

```text
F(sqrt(q+1)) = q-1-2sqrt(q+1) > 0,
F(q-2)       = q²-6q+6 > 0
```

for q>=8. The first inequality follows by squaring positive sides:
`(q-1)²-4(q+1)=q²-6q-3>0` for q>=8. Hence (2) contradicts
n=q² throughout (3). This strengthening is due independently to Sol3;
it uses no assumption that q or r is a square.

This closes the proposed moderately-larger-order embedding escape if
such an embedding is assumed. It does not produce an embedding theorem
for arbitrary A-REG candidates. The same-order case r=q is outside
(2)'s exclusion range; the independent incidence argument below now handles
it for binary q>=4. Orders above (q-2)² are outside these results. No general
nonexistence theorem has been obtained.

## General embedding literature does not supply the missing step

[Moorhouse--Williford, *Embedding finite partial linear spaces in finite
translation nets*, Journal of Geometry 91 (2009), 73--83,
Theorems 1 and 4](https://www.ericmoorhouse.org/pub/embedding.pdf) distinguish
finite nets from finite planes. Theorem 1 embeds every finite partial
linear space into a translation net generated by a partial spread.
For our q² points and q² lines, q=2^k, valid theorem parameters are
`n=q²/2`, `p=2`, `t=2k`, with factorization `t=1*(2k)`.
The ambient vector space is then `V(q²,q²)`, and the net's lines have
size `R=(q²)^(q²/2)=q^(q²)`. This construction is far outside (3), even
if its partial spread could be completed without changing the field.

Such completion is not asserted. Theorem 4 instead obtains a translation
plane over an infinite union of finite fields. The paper's Problem 1
asks for finite projective-plane embeddings; it does not prove them.
Thus this general theorem supplies neither a finite plane nor the small
order bound required by our contradiction. The targeted search stops
here; a specialized small-order embedding theorem remains a missing
hypothesis, rather than an imported consequence.


## Same-order incidence embeddings are excluded

Let q=2^k>=4. A q-regular C4-free graph on q² vertices cannot have its
q²-by-q² neighborhood incidence matrix embedded in a projective plane of
order q. Here an embedding uses distinct plane points for rows and distinct
plane lines for columns, and preserves all 1-entries. It need not preserve
nonincidences, identify the given graph with an induced polarity subgraph,
or extend its self-duality to a plane polarity.

The source input is [de Bruijn--Erdős, *On a combinatorial problem*
(1948), Theorem 1](https://www.renyi.hu/~p_erdos/1948-01.pdf): a noncollinear
finite linear space has at least as many lines as points; equality gives
a near-pencil or a projective plane. The proof below is a direct application,
not a result attributed to that paper about A-REG.

Write W for the q² retained points, M for the q² retained lines, T for
the q+1 deleted points, and L for the q+1 deleted lines. A retained line
must have at least q points of W, because its column in A has q ones.
Thus each retained line meets T at most once. Similarly each retained
point lies on at most one deleted line. In particular every secant of T
belongs to L, so T determines at most q+1 secants.

If T is noncollinear, its secant intersections form a finite linear space
on q+1 points. Each pair lies on exactly one block, all blocks have size
at least two, and distinct secants have distinct blocks. De Bruijn--Erdős
forces exactly q+1 blocks, exhausting L, and one of two equality cases.
The projective-plane case has q+1=r²+r+1 for an integer r>=2. It would
force q=r(r+1), impossible for a power of two since r and r+1 are coprime
and both exceed one.

In the near-pencil case write

    T = X union {p},   X contained in l,   |X|=q,   p not in l.

There is one remaining point r on l. The deleted lines are exactly l and
the q lines px for x in X. Choose u on pr distinct from p and r; such a
point exists since q>=4. All q+1 lines through u are retained. Each meets
T exactly once: pr at p, and every other line through u at its intersection
with X. Each of these retained lines therefore contains exactly q retained
points, forcing its A-column to include all those incidences. All q+1
incidences at u are consequently present in A, contradicting row degree q.

It remains that T is collinear, hence T is an entire plane line l. The
line l is deleted. Any two of the other q deleted lines intersect on l:
an intersection off l would be a retained point on two deleted lines.
Choose two of them, with intersection p on l. Every further deleted line
must pass through p; otherwise its intersections with those two lines
would be two distinct points on l, making it l. Thus L is the entire
pencil of q+1 lines through p, with p on l.

Every retained point now lies on exactly q retained lines, and every
retained line contains exactly q retained points. Hence A includes every
remaining incidence: it is the full biaffine-plane incidence matrix.
Two retained points have no common retained line exactly when their
joining line passes through p. The q lines through p other than l partition
W into q classes of q points. The row-codegree defect is therefore exactly
q disjoint copies of K_q.

For a symmetric graph adjacency matrix A this is its second-order defect D.
The existing theorem `binarySquare_regular_not_allUnit_of_two_pow` in
`Erdos85BinarySquareRegularParity.lean` excludes this all-unit defect.
Thus the assumed incidence embedding is impossible. This new incidence
argument is a reviewed prose proof; it is not yet Lean-formalized.

Together with (3), this excludes ordinary incidence embeddings of A-REG
candidates into every plane of order R with q<=R<=(q-2)², for binary q>=8.
In particular, same-order polarity-graph containment is impossible even
when arbitrary edges of the host may be discarded. The missing root
input is still an embedding or extension theorem for arbitrary A-REG
candidates. The stability theorem does not supply that input by itself,
and no unrestricted A-REG nonexistence conclusion follows.
