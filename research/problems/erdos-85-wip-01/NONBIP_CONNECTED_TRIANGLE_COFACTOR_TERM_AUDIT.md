# NONBIP-CONNECTED triangle cofactor-term audit

## Question

The denominator-free Schur target is

```text
H^T adj(M) 1 = 0.
```

For a triangle `{a,b,c}`, this says that the three adjugate row sums cancel.
Divergence round 74 proposed proving it by a sign-reversing involution on the
individual nonzero determinant/cofactor terms owned by those three roots.
Such a pairwise involution can work only if positive and negative terms have
the same multiplicity separately at every absolute weight.

## Exact faithful falsifier

`nonbip_connected_triangle_cofactor_term_control.py` constructs `M` from the
banked faithful q=4 control and expands every nonzero permutation term in all
cofactors contributing to the first triangle's three adjugate row sums.  It
checks the expansion against SymPy's exact adjugate.  The row sums are

```text
(384, 384, -768),
```

so the required triangle total is indeed zero.  But its term census is

```text
absolute weight 128:  positive 52, negative 46
absolute weight 256:  positive 42, negative 45.
```

Thus there are six excess positive terms of weight 128 and three excess
negative terms of weight 256.  The aggregate cancellation is
`6*128 - 3*256 = 0`; it is intrinsically weighted two-to-one at this level.

## Verdict

**Pairwise term involution cut; cofactor target survives.**  No
weight-preserving sign-reversing involution on individual Sachs/cofactor terms
can establish even the first faithful triangle identity.  A valid
combinatorial proof must group terms in unequal-size packets, use a weighted
flow, or derive the adjugate identity before full permutation expansion.  This
does not refute `H^T adj(M)1=0`, which holds exactly on the control, and does
not weaken the positive triangle-Schur calibration.
