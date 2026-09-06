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

## Actual binary control: field characteristic is forced to be seven

The actual q=4 graph stored in
`binary_q4_fixed_free_disconnected_control.py` admits an ordinary incidence
embedding into PG(2,F) **if and only if the field F has characteristic 7**.
In characteristic 7 the embedding even preserves nonincidences. Thus binary
graph degree does not force a characteristic-two coordinatization, even when
the ambient field size is unrestricted. This control has defect components
of sizes 8 and 8: it does not refute a conjecture restricted to q>=8 or to
connected defect, and it says nothing about non-Desarguesian planes.

Here is a direct coordinate proof, independently reproducible with
`python3 research/problems/erdos-85-wip-01/verify_binary_q4_projective_embedding.py`.
Write P_i for row points and L_j for column lines. The four points with
labels 1,3,8,9 form a projective frame: their six pair-lines have distinct
original column labels 10,5,0,7,2,6. This forces every three of the four
points to be noncollinear, even if extra incidences are permitted. Normalize

    P_1=(1,0,0), P_3=(0,1,0), P_8=(0,0,1), P_9=(1,1,1).

Repeatedly join two known points on an original column, or intersect two
known original lines incident with a row point. The verifier specifies a
deterministic sequence of 28 such steps and prints each input pair and output
vector. Every cross product has integer coordinate gcd 1. Consequently it
stays nonzero in every characteristic, and no division or exceptional-prime
assumption is used. Each step is forced in any putative embedding; all 16
points and 16 lines are reached.

In particular the forced vectors include

    P_6=(-5,-4,-2),  L_9=(1,1,-1).

The original graph requires P_6 incident with L_9, while their dot product
is -7. Thus the field must have characteristic 7. The verifier checks that
the other nonzero required-incidence residuals are also +/-7. Conversely,
reducing all forced coordinates modulo 7 gives 16 distinct projective points
and 16 distinct projective lines. All 256 dot products agree exactly with
the original adjacency matrix: zero precisely at its 1-entries. This is a
strong embedding in PG(2,7), hence in PG(2,F) for every characteristic-seven
field, proving both directions.

There is also a shorter characteristic-two obstruction. The frame's three
diagonal points are P_0,P_2,P_4, supported by the six triples

    L_0: {1,2,9}; L_2: {0,3,9}; L_5: {0,1,8};
    L_6: {4,8,9}; L_7: {2,3,8}; L_10: {1,3,4}.

In characteristic two the diagonal points of a projective frame have
coordinates (1,0,1),(0,1,1),(1,1,0), which sum to zero, so they are collinear.
But distinct original columns L_9 and L_1 contain {0,2} and {0,4}, respectively,
forbidding that collinearity. This uses original columns, not artificially
added pair-lines; weakening an embedding to allow extra incidences does not
remove the obstruction.

This is an exact finite control and a prose coordinate argument, not a new
Lean theorem or a general A-REG result. Its PG(2,7) realization lies outside
the same-order q=4 exclusion above. An unrestricted field-representation
theorem for arbitrary A-REG candidates remains unproved.


## Characteristic-zero embeddings are impossible for q>=6

There is a separate uniform obstruction to field representability. For any
integer q>=6, no collection of N=q² distinct points and N distinct lines
in PG(2,F), with F of characteristic zero, can have every designated point
incident with at least q of the designated lines. In particular no weak
incidence embedding of an A-REG candidate exists over such a field. This
argument does not require symmetric incidence or exact column degrees.

First work over the complex numbers. Let t_r count all intersection points
of multiplicity exactly r in the arrangement of N designated lines,
including intersection points outside the designated point set. The primary
source is [Hirzebruch, *Singularities of algebraic surfaces and characteristic
numbers* (1986), Section 6, page 148, equation (9)](https://hirzebruch.mpim-bonn.mpg.de/id/eprint/79/1/74_Singularities%20of%20algebraic%20surfaces.pdf).
It proves

    t_2 + (3/4)t_3 >= N + sum_{r>=5} (2r-9)t_r

provided t_N=t_{N-1}=t_{N-2}=0. We will use its weaker consequence

    t_2 + t_3 >= N + sum_{r>=5} (r-4)t_r.              (4)

The exceptional high-concurrency cases are excluded directly. If r lines
meet at X, choose a designated point Y different from X. At most one of
those r lines contains Y. Since Y lies on at least q designated lines,
there must be at least q-1 lines outside the pencil. Thus

    r <= N-q+1 <= N-5,

which verifies the source hypotheses.

Each of the N designated points has multiplicity at least q, and they
are distinct. The line-pair identity counts every pair exactly once:

    sum_{r>=2} binom(r,2)t_r = binom(N,2).

The designated points therefore consume at least N*binom(q,2) pairs.
None is a double or triple point, so the remaining pair budget implies

    t_2 + t_3 <= binom(N,2) - N*binom(q,2)
              = N(q-1)/2.

On the other hand, the designated points alone contribute at least
N(q-4) to the sum in (4), and all other terms in that sum are nonnegative.
Consequently (4) implies

    N(q-1)/2 >= N + N(q-4) = N(q-3),

hence q<=5, contradicting q>=6. Extra incidences only increase the
multiplicities, so preserving nonincidences was never assumed.

For an arbitrary characteristic-zero field, the finitely many homogeneous
coordinates of a putative realization generate a finitely generated
extension of the rationals. Such a field embeds into the complex numbers:
choose algebraically independent images of a finite transcendence basis,
then extend across the finite algebraic extension. This preserves all
incidences and the nonzero minors witnessing distinct points and lines,
reducing to the contradiction above.

This is a prose consequence of the cited complex-geometric theorem, not a
Lean formalization or an unrestricted A-REG nonexistence theorem. It rules
out characteristic-zero coordinatization uniformly, but does not supply
coordinatization, exclude positive-characteristic fields, or apply to
arbitrary non-Desarguesian planes. The q4 characteristic-seven control above
is consistent with this obstruction and is outside its degree range.
