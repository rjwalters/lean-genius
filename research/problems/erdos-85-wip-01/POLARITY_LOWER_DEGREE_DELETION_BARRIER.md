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

This closes the proposed moderately-larger-order embedding escape if
such an embedding is assumed. It does not produce the embedding. An
ordinary incidence embedding of the neighborhood configuration is not
enough: the neighborhood involution must extend to the plane polarity
so that the original adjacency is contained in its polarity graph.
Neither that extension nor an embedding theorem for arbitrary A-REG
candidates is established here. The same-order case r=q is also outside
(2)'s exclusion range and requires the separate existing completion
obstruction. No general nonexistence theorem has been obtained.
