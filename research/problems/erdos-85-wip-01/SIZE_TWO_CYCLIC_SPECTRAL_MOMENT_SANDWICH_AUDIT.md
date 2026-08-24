# Size-two cyclic global spectral-moment sandwich audit

## Candidate

Apply a scalar spectral inequality to the reciprocal global block matrix
`S=(A_tu)`, using exact hits for `tr(S^2)`, caps for an upper bound on
`tr(S^4)`, and the empty diagonal block for a triangle/fourth-moment deficit.

## Immediate aggregation warning

Summing a colored reversal identity over **all** color words loses the
separator.  For every square directed matrix `K`, without reciprocity,

```text
tr(K^m) = tr((K^m)^T) = tr((K^T)^m).
```

Thus total scalar closed-walk reversal is a tautology even on the directed
SAT controls.  The q8 probe already shows that the obstruction needs selected
start-color families and both word lengths; a proof using only the three
numbers `tr(S^2), tr(S^3), tr(S^4)` cannot retain that information.

This does not by itself rule out using symmetry/PSD in addition to scalar
moments, so the proposed upper and lower inputs must still be checked.

## The fourth-moment upper bound does not follow from the caps

For symmetric `S`,

```text
tr(S^4) = ||S^2||_F^2
        = sum_(t,s) ||(S^2)_ts||_F^2.
```

The full cap family in the packing interface bounds off-diagonal entries of
the **same-source-fibre return blocks** `(S^2)_tt`: two vertices in fibre `t`
have at most one common coded target.  It supplies no corresponding bound on
the cross-fibre blocks `(S^2)_ts`, `t != s`.  Those uncontrolled nonnegative
terms occur in `tr(S^4)`, so the cap inequalities do not give the advertised
global upper bound.

This is the same remainder exposed by the two-step completed-square audit,
now after full color aggregation.  A bound that simply drops the cross-fibre
terms goes in the wrong direction for an upper sandwich.

## The empty block does not pin the odd moment

The equation `A_ee=0` forbids edges whose two endpoints both lie in the empty
fibre.  It does not forbid triangles that visit `e` once and use two other
fibres.  Consequently it neither forces `tr(S^3)=0` nor determines a fixed
deficit in `tr(S^3)`.  Exact hit equations redistribute the missing internal
edges among cross-fibre blocks while preserving the global degree/edge mass.

Likewise, if exact hits fix all global degrees, the standard identity
`tr(S^2)=sum_v deg(v)` is unchanged by which diagonal fibre block is empty.
The empty-fibre information is therefore invisible to the quadratic scalar
moment and not determined at the cubic moment.

## Verdict

The proposed scalar spectral sandwich is **cut in its global form**:

1. total trace reversal is automatic for directed matrices;
2. same-fibre caps do not upper-bound the cross-fibre contribution to
   `tr(S^4)`; and
3. one empty diagonal block does not pin `tr(S^3)`.

A spectral/PSD route remains possible only with fibre projectors or a
pair-rooted flag moment matrix.  Such a refinement is no longer a scalar
`tr(S^k)` argument: it must preserve selected color starts and explicitly
control or cancel the cross-fibre two-step norms.  The existing generic
sixth-moment toolkit cannot be applied verbatim until that missing colored
input is supplied.
