# NONBIP-CONNECTED: mod-4 harmonicity falsifier

## Question cut

Let `q = 8`, let `D` be a connected `(q-1)`-regular graph on `q^2`
vertices, and let `ell : V(D) -> Z/4Z`.  Does

```text
(D + I) ell = (sum ell) 1  (mod 4)
```

force `ell` to be constant?

This is the exact consequence obtained from the proposed local residue
`A k = 4 1 (mod 8)` after writing the even triangle-free degree as
`k = 2 ell` and using `A^2 = (q-1)I + J - D`.  A positive answer would
have replaced the stronger, still-open assertion that `k` is preserved on
every `D`-edge.

## Explicit countermodel

It does not force constancy.  Take the Cayley graph on `Z/64Z` with
connection set

```text
S = {+1,-1,+2,-2,+3,-3,32}.
```

This graph is simple, connected (because `1 in S`), and 7-regular.  Define

```text
ell(x) = 0 if x is even, 1 if x is odd.
```

For even `x`, the four offsets `+/-1,+/-3` land at odd vertices and the
closed-neighborhood sum is `4`.  For odd `x`, the vertex itself and the
three parity-preserving offsets `+/-2,32` contribute `4`.  Thus

```text
((D + I) ell)(x) = 0 (mod 4)
```

at every vertex.  Also `sum ell = 32 = 0 (mod 4)`, so the displayed
harmonicity equation holds exactly, while `ell` is nonconstant.  The
associated natural-valued profile `k = 2 ell` takes the allowed even values
`0` and `2`, both in `[0,q]`.

The construction is checked by:

```bash
python3 - <<'PY'
n = 64
S = (1, -1, 2, -2, 3, -3, 32)
ell = [x % 2 for x in range(n)]
assert len({(x + s) % n for s in S}) == 7
assert all(sum(ell[(x + s) % n] for s in (0,) + S) % 4 == 0
           for x in range(n))
assert sum(ell) % 4 == 0
assert len(set(ell)) == 2
print("verified")
PY
```

## Consequence for the proof route

Connectedness, odd regularity of `D`, the natural range/parity of `k`, and
the mod-4 closed-neighborhood equation are insufficient.  Any attempt to
replace edgewise propagation using this equation must retain additional
ambient information about `A` (for example, that `D` is the 0-common-
neighbor child of a `(q^2,q,1,0)` Deza graph).  Pure graph-Laplacian or
maximum-principle arguments on `D` cannot close the selected terminal.

