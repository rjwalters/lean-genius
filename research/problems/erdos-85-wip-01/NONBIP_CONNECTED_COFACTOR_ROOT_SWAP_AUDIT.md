# NONBIP-CONNECTED cofactor root-swap audit

Status: bounded falsification after divergence round 74, 26 August 2026.
This cuts the cheapest canonical involution on the cleared cofactor target,
not the target itself and not all rooted Sachs involutions.

## Target and proposed switch

For invertible triangle core `M`, put

```text
c = adj(M) 1.
```

The reviewed Schur terminal is exactly `H^T c=0`: for every A-triangle
`{a,b,c}`, the three corresponding adjugate row sums cancel.  By Cramer's
rule, the coordinate at a root `r` is the determinant of `M` with column `r`
replaced by the all-ones column.  Its Leibniz terms are therefore natural
rooted cycle-cover objects.

The simplest owner switch takes a term rooted at one triangle vertex `r`,
chooses the lexicographically first other triangle vertex `s`, and swaps the
output column labels `r` and `s` in its permutation.  A column transposition
reverses permutation sign.  Retain the switch only when the new rooted term
is supported and its complete integer weight is the negative of the old
weight.  If the same selector returns to the original term, this gives the
desired canonical sign-reversing involution.

## Immediate exact counterexample

`nonbip_connected_cofactor_root_swap_q4.py` constructs `M` from the banked
fixed-point-free q=4 control and tests the first triangle `(0,1,5)`.  It fails
on the very first supported term: the identity permutation in the determinant
rooted at 0 has weight `-128`, but swapping column 0 with either triangle
column 1 or 5 produces no opposite-weight supported term in the corresponding
rooted determinant.

```text
triangle=(0, 1, 5); checked_terms=1
counterexample=('no_valid_swap', root=0, permutation=identity, weight=-128)
```

The obstruction is structural: the diagonal monomer choices at the two
non-root triangle vertices are nonzero, while moving the dense replacement
column changes which diagonal/core entries must support the term.  A bare
root-column transposition does not preserve rooted cofactor support or weight.

## Remaining scope

The integer identity `H^T adj(M)1=0` still holds on all 256 q4 controls and
remains the precise q-generic gap.  A viable termwise proof needs a larger
alternating path/cycle surgery that also repairs the displaced core entries;
it cannot merely rotate or transpose the root label inside its triangle.
This agrees with the signed perfect-matching audits: canonical one-toggle
selectors fail even though a global sign-reversing pairing exists.
