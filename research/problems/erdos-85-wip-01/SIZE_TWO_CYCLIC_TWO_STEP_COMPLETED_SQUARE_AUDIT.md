# Size-two cyclic two-step completed-square audit

## Question

Can the q8 interaction between colored triangle and four-cycle reversal be
the expansion of a nonnegative square involving one-step and two-step block
walks?  This is attractive because such a square has degree at most four and
therefore fits the translation-orbit moment lift.

Write `S=(A_tu)` for the block adjacency matrix and

```text
B_ts = (S^2)_ts = sum_u A_tu A_us.
```

For a reciprocal code, `A_tu^T=A_ut`, hence `B_ts^T=B_st`.

## The useful exact expansion

For every ordered pair of fibres `(t,s)` and every scalar `lambda`,
reciprocity gives

```text
||B_ts - lambda A_ts||_F^2
  = sum_(u,v) tr(A_tu A_us A_sv A_vt)
    - 2 lambda sum_u tr(A_tu A_us A_st)
    + lambda^2 tr(A_ts A_st).
```

Thus the square is exactly

```text
all colored T4 words based at t and passing through s
  - 2 lambda * all colored T3 words based at t and passing through s
  + the one-step edge count.
```

There is no product of averaged marginals: every summand is a local closed
walk, so its simultaneous-base orbit average is eligible for the non-TI
moment lift.  This is the clean algebraic reason that degrees three and four
appear together.

The same formula holds with nonnegative weights `w_ts` and can therefore be
localized at the q8 grouped-core anchors.  Candidate multipliers should be
searched first among small integers and `lambda in {1,2}`.

## Antisymmetric-path variant is tautological

The initially tempting defect

```text
D_ts = B_ts - B_st^T
```

vanishes identically under entrywise reciprocity.  Consequently
`||D_ts-lambda A_ts||^2` collapses to `lambda^2||A_ts||^2`; its apparent
mixed trace terms cancel before any hit, cap, or empty-fibre equation is
used.  It cannot be the obstruction.  This is distinct from the raw
edge-transpose-energy cut, but has the same fatal tautology.

## Missing closure for the surviving square

The square `||B_ts-lambda A_ts||^2` is nontrivial, but the currently banked
projection laws determine only the action of `S` (and hence `S^2`) on two
special fibre-index vectors.  They do **not** determine a selected block's
Frobenius norm.  Likewise, the full same-fibre cap controls off-diagonal
entries of the diagonal two-step block

```text
B_tt = sum_u A_tu A_tu^T,
```

but gives no comparable entrywise bound for `B_ts` when `t != s`.  Therefore
an arbitrary weighted sum over the three q8 start groups leaves uncontrolled
cross-fibre two-step norms.  The empty equation `A_ee=0` removes the linear
term only at `(e,e)`; it does not evaluate `||B_ee||^2` or relate it to the
predecessor and partner blocks.

So the completed-square idea yields the right mixed T3/T4 grammar, but **does
not yet close** from the known projection and cap equations.  A valid next
step must supply one of:

1. a telescoping weight system whose cross-fibre `||B_ts||^2` terms cancel,
2. a new global double count evaluating their weighted sum, or
3. a cap-slack SOS certificate showing that the uncontrolled remainder has
   a fixed sign.

Without one of these, choosing weights from the finite q8 core merely hides
the missing global identity and is not a q-generic proof.

## Bounded verdict

- **Survives:** the one-step/two-step square explains exactly why a genuine
  certificate may need both colored degrees three and four, and it is
  division-free and moment-lift eligible.
- **Cut:** antisymmetrizing the two-step path is a reciprocity tautology.
- **Open terminal:** no known projection/cap identity closes the remaining
  cross-fibre two-step norms.  Do not formalize the expansion alone; the next
  useful result must eliminate that remainder.
