# Transpose-defect energy audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Candidate

For a directed TI relaxation define the transpose defect

```text
S(t,u,r) = E(t,u,r) - E(u,t,-r).
```

The integer energy

```text
Energy = (1/2) sum_(t,u,r) S(t,u,r)^2
```

is exactly the number of failed unordered block-transpose equations.
Reciprocity says `Energy=0`.  Divergence round 14 proposed proving a positive
lower bound from hits, caps, and the empty block, then rewriting the energy
through colored T3/T4 reversal defects.  The optimistic version predicted
that trace reversal would progressively annihilate this energy.

## Exact optimizer

The TI probe now has two diagnostic options:

- `--dump-transpose-defect` prints the failed directed equations and their
  fibre-pair distribution;
- `--minimize-transpose-defect` performs exact bounded SAT minimization of
  the unordered mismatch count.

The minimizer binary-searches a pseudo-Boolean upper bound.  A solver
`unknown` is treated as failure, never as an UNSAT lower bound, so a printed
minimum is certified by SAT at that value and UNSAT below it.  Long T4
optimizations are stopped under the campaign's bounded-probe rule.

## q8 full-cap empty-fibre results

Use all caps on every allowed fibre at `q=8,a=2` and make fibre 4 empty.
With no trace constraints, the exact minimum is

```text
minimum transpose defect = 4 unordered equations.
```

One minimum model has its eight directed disagreements (two orientations per
equation) on fibre pairs

```text
(0,4), (1,3), (3,7), (4,6).
```

Impose every colored triangle reversal identity.  The system remains SAT,
but the exact minimum becomes

```text
minimum transpose defect = 6 unordered equations.
```

A minimum model distributes these disagreements over

```text
(0,0), (0,3), (1,3), (4,6), (4,7), (7,7).
```

Therefore T3 reversal does not drive the directed system closer to
reciprocity in transpose-defect energy.  It raises the minimum from four to
six.  The proposed identity "T3 kills the cubic cross term, T4 kills the
quartic term, hence Energy=0" cannot be correct in this simple monotone form.

T4-only and T3+T4-without-empty minimizations reached `unknown` inside a
bounded run and were terminated.  Ordinary satisfying models (without
optimization) had respectively 26 and 20 unordered transpose defects, but
those values are not minima and are recorded only as scale diagnostics.

## Interpretation

The trace constraints are not approximate entrywise reciprocity under this
natural metric.  They constrain closed-walk statistics while allowing, and
in the T3 case forcing, a more distributed set of edgewise transpose
failures.  This agrees with invariant theory: low word traces control an
orbit-level representation, not fixed-label equality of tuple entries.

The actual mixed T3/T4 contradiction with an empty fibre can still admit an
SOS certificate, but its positive quantity is not the raw Frobenius norm
`sum ||A_tu-A_ut^T||^2`.  A surviving energy must live on path flags or a
moment Gram matrix where degree-one and degree-two objects interact.

## Verdict

The raw transpose-defect-energy candidate is **cut**.  Exact q8 optimization
refutes the claimed monotone relation between T3 reversal and distance from
reciprocity.  Divergence candidate 14.1, the length-one/length-two path Gram,
remains logically distinct because its norm is on two-step collision flags
rather than on edgewise transpose defects.
