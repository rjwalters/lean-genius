# Colored block trace-reversal audit

## Exact block interface

Index the base-resolved adjacency by difference fibres and write `A_tu` for
the `q x q` block from source fibre `t` to target fibre `u`.  Its rows and
columns are base coordinates.  The four relevant hypotheses are:

```text
A_tu = A_ut^T                                      (reciprocity)
sum_u A_tu = J - X^t - X^(t+1)                    (target-row hits)
sum_u A_tu X^u = J - I - X^(-1)                   (target-column hits)
offdiag(sum_u A_tu A_tu^T) <= 1                   (full cap in fibre t).
```

An empty fibre is the zero diagonal block `A_tt=0`.  The shift convention in
the weighted equation depends on whether columns act on the left or right;
the coefficient statement is unambiguous: after relabeling target base `y`
as absolute target column `y+u`, every column except offsets `0,-1` is hit
once.

The scalar Gram and two-block fourth moment do not use global reciprocity in
an essential way:

```text
tr(A A^T B B^T) = ||A^T B||_F^2.
```

This identity holds for arbitrary directed blocks and therefore cannot
separate the directed SAT control from the reciprocal UNSAT system.

## First genuinely reciprocal colored identities

For a closed color word, define

```text
T3(t,u,v)   = tr(A_tu A_uv A_vt),
T4(t,u,v,w) = tr(A_tu A_uv A_vw A_wt).
```

Entrywise block transpose implies reversal symmetry:

```text
T3(t,u,v)   = T3(t,v,u),
T4(t,u,v,w) = T4(t,w,v,u).
```

Unlike scalar norms, these identities retain every intermediate fibre and
are not valid for a general directed block family.  In the
translation-invariant probe, the normalized triangle trace is the cyclic
convolution

```text
sum_(r,s) E(t,u,r) E(u,v,s) E(v,t,-r-s),
```

and the four-cycle trace has the analogous three-displacement convolution.

The probe now supports:

- `--dump-triangle-reversal`, which prints directed triangle asymmetries;
- `--impose-triangle-reversal`, which drops edge reciprocity but imposes all
  `T3` reversal equalities;
- `--impose-four-cycle-reversal`, similarly for all `T4` equalities; and
- `--trace-reversal-core`, which imposes both families and prints the tracked
  core when they are inconsistent; and
- `--trace-reversal-group-core`, which greedily shrinks the identities after
  grouping them by degree and starting fibre.

## Decisive q8 A/B refinement

Use every nonzero-separation cap on all allowed fibres at `q=8,a=2`, with
fibre `4` empty.

```text
directed blocks only                         SAT
directed + every T3 reversal                SAT
directed + every T4 reversal                SAT
directed + every T3 and every T4 reversal   UNSAT
entrywise reciprocal blocks                 UNSAT
```

The base directed witness has 18 triangle asymmetries.  They include the
minimal transpose-core colors:

```text
T3(4,3,7)=1,  T3(4,7,3)=0,
T3(3,4,7)=0,  T3(3,7,4)=1.
```

Imposing all triangle reversals allows a different directed model; imposing
all four-cycle reversals alone also allows one.  Imposing both degree-three
and degree-four reversal families is UNSAT in about one minute.  The raw
tracked core is large, so this is not yet a small certificate, but it is the
first tested condition strictly weaker than entrywise reciprocity that still
separates the all-cap empty-fibre system from the directed control.

Grouping by degree and starting fibre gives the much smaller greedy
irredundant core

```text
all T4 reversals based at fibre 3,
all T4 reversals based at fibre 4,
all T3 reversals based at fibre 6.
```

Removing any one of these three families restores SAT relative to the final
deletion order.  This is theorem-shaped: empty fibre `4`, capped predecessor
`3`, and partner fibre `6` carry the low-degree trace obstruction, although
the individual color words have not yet been minimized.

The trace mechanism still consumes the **full cap family**.  Replacing all
caps by the exact q8 three-cap MUS `(3,1),(4,1),(4,3)`, while retaining every
degree-three/four reversal identity, is SAT.  Thus this separator belongs to
the corrected full-cap branch and does not revive the selected-cap subtree.

It also uses the **empty fibre essentially**.  With all q8 cap families and
all `T3`/`T4` reversal identities still imposed, deleting only
`--empty-fiber 4` restores SAT.  This distinguishes the trace mechanism from
the stronger translation-invariant observation that entrywise reciprocity
plus all caps is already UNSAT without an empty fibre.  The low-degree trace
subsystem is therefore aligned with the actual non-translation-invariant
merger target: it combines full caps with the selected zero diagonal block.

## Consequence and next theorem

Colored low-degree trace reversal is therefore a live mechanism, while any
single trace degree is insufficient.  The proof target should not be a
single fourth-moment inequality.  It is an interaction theorem of the form:

> Exact two-hole row/column partitions, full same-fibre caps, and an empty
> diagonal block cannot satisfy *both* the colored triangle- and four-cycle
> reversal identities induced by a self-transpose block family.

The q8 result is only a translation-invariant bounded certificate.  Before
formalization at general `q`, the next bounded tasks are (1) shrink the three
surviving groups to individual color words and (2) test the combined
degree-3/4 identities at q10/q12 using grouped or lazy constraints.  A proof
must keep the closed color word;
augmenting over intermediate fibres collapses back to the scalar identities
already cut.
