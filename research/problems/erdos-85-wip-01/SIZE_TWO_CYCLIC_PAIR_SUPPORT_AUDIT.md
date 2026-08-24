# SIZE-TWO-CYCLIC: fixed-pair common-target support audit

## Correct nonlinear datum

The agreement cap is violated only when one fixed source pair owns two
distinct common target cells.  Aggregate defect histograms and a bare
collision witness forget this requirement.  In the translation-invariant
probe, normalize the pair to source cells `(0,t)` and `(d,t)`.  Its precise
common-target support is

```text
Support(t,d) = {(u,r) : E(t,u,r) and E(t,u,r-d)}.
```

Here `(u,r)` denotes the target cell of difference fibre `u` and base `r`.
The cap at `(t,d)` is exactly `|Support(t,d)| <= 1`.

The probe option `--dump-pair-supports` prints every nonempty support,
including its 2-adic shift level.  This is the smallest diagnostic that
retains the fixed row pair and the accumulated target support demanded by the
corrected three-cap terminal.

## q8 calibration

At `q=8, a=2`, retain the three short caps

```text
(0,1), (0,2), (4,1).
```

The reduced translation-invariant model is SAT, but its only supports of
cardinality two are antipodal:

```text
Support(0,4) = {(7,2),(7,6)}
Support(3,4) = {(3,2),(3,6)}
Support(4,4) = {(4,2),(4,6)}
Support(7,4) = {(0,2),(0,6)}.
```

In particular the selected middle fibre `t=4` has two common targets for the
fixed antipodal source pair.  Adding the single cap `(4,4)` makes this reduced
system UNSAT immediately.  This is a more precise translation-invariant
terminal than merely proving that the middle induced graph is nonempty.

This does **not** yet prove that the three caps force the displayed supports
in the full non-translation-invariant code.  It is a bounded structural
calibration and a target for a base-resolved theorem.

## q12 escape

At the natural `q=12, a=1` order-four geometry, all four short caps plus an
empty middle fibre are SAT.  The tuple census has 65 nonempty fixed-pair
supports with valuation-layer mass

```text
{v2=0:48, v2=1:30, v2=2:7, v2=3:7}.
```

Support sizes reach five at `(t,d)=(8,1)` and four at `(7,6)`, while many
other double supports are distributed across unrelated fibres and shifts.
Thus a theorem that merely forces *some* double support is not binary-specific
and cannot close the desired cap.  The transport must force two targets for a
particular capped pair, or inject an already accumulated support into a lower
2-adic level without changing its source-pair owner.

Adding the selected fifth antipodal cap `(middle,6)` is still SAT, but the
tuple data explains the escape precisely: `Support(6,6)` is empty, while
`Support(6,5)` and `Support(6,7)` each contain three targets.  The model exports
the forbidden double support to unselected neighboring separations.

Therefore this is a countermodel to the five-cell reduction, **not** a full
same-difference-code countermodel.  Imposing the cap at every same-fibre
separation returned `unknown` at 120 seconds in the 610-orbit-variable q12
translation-invariant model.  A theorem that uses all separations remains
logically live and need not be binary-specific; the present evidence only
refutes terminals that retain the selected short/antipodal caps.

## Reproduction

```text
python3 size_two_cyclic_translation_invariant_probe.py 8 --a 2 \
  --cap 0:1 --cap 0:2 --cap 4:1 --dump-pair-supports

python3 size_two_cyclic_translation_invariant_probe.py 8 --a 2 \
  --cap 0:1 --cap 0:2 --cap 4:1 --cap 4:4

python3 size_two_cyclic_translation_invariant_probe.py 12 --a 1 \
  --cap 0:1 --cap 0:3 --cap 6:1 --cap 9:3 --empty-fiber 6 \
  --dump-pair-supports
```

The q16 SAT/UNSAT control remains decisive.  If SAT, rerun it with
`--dump-pair-supports`; the result tests the corrected tuple-level terminal
directly rather than a marginal proxy.
