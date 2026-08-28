# Size-two odd-torsion escape audit

Node: `A-REG-NONBIP / NONBIP-MIXED`; divergence round 97.

## 1. Setup

Let `C` be a defect component of normalized weight two, so

`|C|=2q`.

Write `K=A[C,C]` and, for every other defect component `E`, write
`B_E=A[E,C]`.  Put

`L_C=(q-1)I-D[C]`.

The full selector column block `A[:,C]` is an unsigned incidence matrix for
the `q`-regular complement

`H_C = complement(D[C])`.

Indeed every ambient row has exactly two neighbors in `C`, and the packing
Gram says that every `H_C` edge occurs in exactly one such row.  The rows in
`C` give the internal two-factor `K`; the rows in the other components give
the exterior owner factors `B_E`.

## 2. Exact common-kernel theorem

Fix an odd prime `p`.  Since `p` does not divide `|C|=2q`, every nonconstant
class in `ker(L_C mod p)` has a unique representative `v` with
`sum_C v=0`.

> **Size-two odd-torsion escape.**  If `v != 0`, then at least one exterior
> block satisfies `B_E v != 0`.

Here is the proof.  Suppose instead that every `B_E v=0`.  Embed `v` in the
full ambient space, supported on `C`.  The diagonal block of

`A^2=(q-1)I+J-D`

and `L_Cv=0`, `sum v=0` show that `A^2v=0`.  But `Av` is supported on `C`
and equals `Kv` there.  Therefore every block of `A` kills `Kv`:

```text
K(Kv)=0,
B_E(Kv)=0 for every E != C.
```

The owner-incidence coverage now says that `(Kv)_x+(Kv)_y=0` on every edge
`xy` of `H_C`.  The graph `H_C` is connected: it is `q`-regular on `2q`
vertices, while every connected component of a `q`-regular simple graph has
at least `q+1` vertices, so two components would require more than `2q`
vertices.

Thus either `Kv=0`, or `H_C` is bipartite and `Kv` is a full-support
alternating vector.  The second case is impossible.  A connected bipartite
`q`-regular graph on `2q` vertices has two shores of size `q` and must be
`K_{q,q}`.  Its complement on distinct vertices is `K_q disjointUnion K_q`,
whereas `D[C]` is connected by definition.  Hence `Kv=0`.

Now all blocks, including `K`, kill `v` itself.  Repeating the same
owner-incidence argument forces `v=0`, a contradiction.

### Why the full square matters

The tempting intermediate inference `K^2v=0 => Kv=0` is false uniformly in
finite characteristic when an internal cycle length is divisible by `p`.
The proof above avoids semisimplicity completely: `A^2v=0` transports `Kv`
back through **all** reciprocal blocks, and connectedness of the owner union
then kills it.

## 3. Critical-prime propagation

The intertwining identity

`L_E B_E = B_E L_C`

shows that every nonzero `B_Ev` obtained above lies in `ker(L_E mod p)`.
Its coordinate sum is zero.  If `p` does not divide `m_E`, it cannot be a
nonzero constant vector, because `|E|=q m_E` and `p` is odd.  It then gives
nonconstant `p`-torsion for `E`.  If it is a nonzero constant vector, the
same sum equation instead forces `p | m_E`.  Consequently:

> Every odd prime occurring in the nonconstant critical kernel of a
> size-two component also occurs in at least one other local factor
> `m_E tau_E`: either in `tau_E`, through a nonconstant critical class, or
> directly in the normalized weight `m_E`.

For the exact `q=4` control, each internal block is `C_8` adjacency and the
cross block is injective on its two-dimensional zero space over every odd
prime.  At `p=7` it also maps the full two-dimensional nonconstant critical
kernel isomorphically to the other component, agreeing with the earlier Smith
audit.

## 4. What this does and does not close

This is the first support-sensitive propagation theorem in the mixed
nonbipartite branch.  It rules out an odd prime supported on exactly one
factor `m_C tau_C` when that component has normalized weight two.

It is not yet a square-class terminal.  Nonzero propagation does not prove
that the induced critical-group maps are isomorphisms, nor that the sum of
the local `p`-adic tree valuations is even.  In particular, a prime may occur
on three or more components or with unequal higher valuations.  Therefore
the theorem does not by itself contradict

`q^(r+2) product_C(m_C tau_C)`

being a square.

The next consumer must strengthen support propagation to one of:

1. an adjoint pairing of the odd-primary elementary divisors;
2. an even-cycle structure on the component propagation graph; or
3. a local theorem producing an odd critical prime unique to a size-two
   component.

Absent one of these, retain the escape theorem but do not claim a
componentwise square class.
