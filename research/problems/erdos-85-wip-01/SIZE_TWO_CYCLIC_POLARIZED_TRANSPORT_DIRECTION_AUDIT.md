# SIZE-TWO-CYCLIC: polarized transport direction audit

## Two branches require different terminals

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The corrected-terminal divergence mixed two logically different settings.

### Full-cap branch

In a full `SizeTwoCyclicSameDifferenceCode`, every nonzero separation is
capped.  A fixed source pair with two distinct common targets is already an
immediate contradiction; there is no need to transport that double support
to another valuation.  The empty-fibre lower bound supplies many
single-target pair incidences, not necessarily a double target for one
pair.  The missing operation here is therefore **merging** two collision
tokens onto one fixed source pair.  The collision Levi-cycle route is shaped
for this problem: it retains a connected family of single tokens and asks
whether consecutive-hole geometry forces a chord/4-cycle.

An exterior-square encoding records the desired double target exactly, but
under the cap all those coefficients vanish.  To advance the full-cap branch
it must explain why the empty-fibre incidence cycle forces a nonzero
exterior-square coefficient; merely defining `Lambda^2 K` does not do so.

### Designated-cap branch

In the reduced four/five-cell subsystem, a double support may occur at an
*uncapped* separation and must be moved to a designated capped separation.
Here transport is appropriate.  To reach the antipodal separation `q/2` in
`Z/(2^k)`, the natural dynamics is

```text
d -> 2d,
```

which **increases** `v2(d)` until the unique nonzero element of maximal
valuation is reached.  Halving/pullback moves in the opposite direction and
does not by itself explain termination at the antipode.

This direction also gives the clean binary/q12 distinction.  For every
nonzero `d` in `Z/(2^k)`, repeated doubling reaches `q/2` immediately before
zero.  In `Z/12`, the odd component can persist: for example

```text
5 -> 10 -> 8 -> 4 -> 8 -> ...
```

never reaches the antipode `6`.  This matches the q12 five-cell escape,
where the selected antipodal support is empty but double supports occur at
neighboring uncapped shifts 5 and 7.

## Sharpened candidate

The designated-cap theorem to test is an **intact doubling transport**:

```text
if Support(t,d) contains two distinct target cells and d is not antipodal,
then the consecutive-hole/reciprocity identities produce a fibre t' such
that Support(t',2d) contains two distinct target cells,
unless an already-designated cap is violated.
```

The two target cells must remain distinct and owned by one fixed new source
pair.  A linear XOR derivative, a valuation histogram, or two separately
transported cells does not suffice.  The exterior-square/Hadamard-product
formulations from divergence round 11 are suitable algebraic containers for
this exact claim; coherent halving is useful only if dualized into this
forward doubling statement.

## Bounded falsifier

For every double tuple support in a model, compare its two target cells with
all double supports at separation `2d`, recording the candidate fibre map
forced by reversal.  Reject intact doubling as soon as the cells split
between different owner pairs, merge to one cell, or disappear without a
designated cap violation.

The q8 three-cap calibration is only an endpoint check because its observed
double supports are already antipodal.  The q12 model is a negative control
for binary termination, not necessarily for one local doubling step.  A q16
SAT witness with tuple supports is the first decisive test of the proposed
local transport in the intended binary family.
