# H7 characteristic-square module audit

## Proposed invariant

Over `GF(2)`, the characteristic polynomial of every even-order symmetric
zero-diagonal matrix is a square.  Applying this to the 42-by-42 low block
`C`, together with the forced integral factorization

```text
char_C(x) = x^6 (x^2-7x+7) r(x),
```

shows that the residual factor supplies another copy of
`x^2+x+1` in the characteristic polynomial modulo two.  Divergence round 72
proposed turning that factor into an additional low-weight vector satisfying

```text
(C^2+C+I)v = 0.
```

Such a vector outside the fixed quotient might support a coding/weight
contradiction with C4-freeness.

## Bounded exact test

`sat49/probe_h7_characteristic_square_module.py` reuses the independently
banked F6/type2 Boolean witness satisfying every exact degree equation, every
mask unit, and all 15,680 quadratic C4 constraints.  It reconstructs `C`,
checks its characteristic polynomial has only even powers modulo two, and
performs exact binary elimination on `C^2+C+I`.

The two known fixed vectors are `1` and the indicator of the 14 singleton
low vertices.  Indeed `C` maps the singleton indicator to `1`, while degree
parity maps `1` to their sum, giving the fixed irreducible two-dimensional
module.  The witness returns

```text
rank(C^2+C+I) = 40
kernel dimension = 2
kernel = span{1, singleton-indicator}
```

There is **no additional kernel vector at any weight**.

## Why the inference failed

The repeated irreducible factor in the characteristic polynomial need not
split into two eigenspaces in characteristic two.  A non-semisimple primary
block can extend the fixed module: its characteristic multiplicity grows
without increasing `ker(C^2+C+I)`.  Symmetry does not imply semisimplicity in
characteristic two.  Thus the characteristic-square theorem supplies only a
generalized module, not the proposed residual codeword.

## Verdict

**Cut.**  The exact relaxation model realizes the smallest possible kernel,
namely the already-known fixed span.  Therefore no minimum-weight enumeration
or C4 contradiction can start from the proposed extra vector.  Revisit only
with an independent theorem forcing semisimplicity of the relevant primary
component; the characteristic-square identity alone is insufficient.
