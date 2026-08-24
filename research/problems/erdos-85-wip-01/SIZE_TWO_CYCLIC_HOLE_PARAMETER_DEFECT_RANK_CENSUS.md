# q8 hole-parameter defect-rank census

Node: cap-free reciprocal defect amplification beneath
`BinarySizeTwoCyclicPackingBound`.

## Quantity and scope

For a source cell `p`, let

```text
r(p) = number of allowed target fibres receiving no neighbour from p.
```

Because every source has total degree `q-2` into `q-2` target fibres,
`r(p)` is also its total positive block-load excess.  This audit uses exact
row/column hits and full reciprocity, but **no same-fibre caps**.  The pure
Boolean probe flag `--max-total-defect-rank K` asks whether

```text
sum_p r(p) <= K.
```

At q8 the unordered consecutive deleted pair `{a,-1-a}` has four
representatives `a=0,1,2,3`; hence the following sweep covers every hole
placement rather than only the two previously used controls.

## Exact q8 minima

Direct Z3 solves give:

| `a` | deleted fibres | largest UNSAT bound | first SAT bound | minimum `sum r` |
|---:|:---:|---:|---:|---:|
| 0 | `{0,7}` | 77 | 78 | **78** |
| 1 | `{1,6}` | 63 | 64 | **64** |
| 2 | `{2,5}` | 63 | 64 | **64** |
| 3 | `{3,4}` | 87 | 88 | **88** |

Every unrestricted cap-free instance is SAT, including `a=0,3`; the larger
numbers are genuine minimum-rank effects, not nonexistence of reciprocal
routings.  Representative commands are

```text
python3 size_two_cyclic_full_probe.py 8 --a 0 --no-caps \
  --max-total-defect-rank 77        # unsat
python3 size_two_cyclic_full_probe.py 8 --a 0 --no-caps \
  --max-total-defect-rank 78        # sat

python3 size_two_cyclic_full_probe.py 8 --a 3 --no-caps \
  --max-total-defect-rank 87        # unsat
python3 size_two_cyclic_full_probe.py 8 --a 3 --no-caps \
  --max-total-defect-rank 88        # sat
```

The a1/a2 threshold 64 was independently cross-checked through the sound
pure-Boolean DIMACS path and Kissat in the propagation audit.  The new a0/a3
values are native-Z3 bounded evidence.

## Consequences for the proof split

The candidate uniform theorem

```text
sum_p r(p) >= q^2
```

survives all q8 hole placements, but equality is highly nonuniform: it is
attained only for the middle deleted pairs `{1,6}` and `{2,5}`.  The boundary
placements already have additive excess 14 and 24 before any cap is used.

Therefore an equality classification followed by a cap contradiction must
retain the hole parameter.  At q8 the reflection-orbit selective-cap work is
needed only in the equality-admitting a1/a2 cases.  Conversely, a proof of
the uniform `q^2` bound should not assume equality geometry visible in those
two witnesses; a0/a3 show that reciprocity can force substantially more
ramification.

The asymmetry `78 != 88` also warns against treating all consecutive deleted
pairs as translates in the normalized coordinates.  Translation of fibre
labels does not preserve the simultaneous source-row and absolute-column
hole equations without changing other labels, so it is not a valid symmetry
of this fixed cyclic routing problem.

## Caps at the true minimum rank

The selective flag `--cap-fibres` tests the cap terminal at the actual a0/a3
minimum rather than at the unattainable rank 64.

At `a=0`, `sum r<=78`, every one of the six singleton cap-fibre queries is
UNSAT.  Hence every minimum-rank model violates the cap in every endpoint
fibre.

At `a=3`, `sum r<=88`, singleton cap fibres 0,2,5,7 are UNSAT, while 1 and 6
are SAT.  Imposing both cap fibres `{1,6}` remains SAT.  Under the reflection

```text
j(t) = -1-t,
```

the orbits are `{0,7}`, `{1,6}`, `{2,5}`.  Thus every minimum-rank model is
cap-bad at both members of the two outer reflection orbits; the middle orbit
can be wholly cap-good.

Together with the a1/a2 exact-rank cap discriminator, all four q8 hole
placements support one uniform minimum-stratum terminal:

> Every cap-free minimum-defect-rank model violates both cap families in at
> least one full reflection orbit `{t,j(t)}`.

This is bounded evidence, not a classification theorem.  It materially
widens the reflection-orbit target beyond the `sum r=q^2` equality cases:
the same shape persists when the cap-free minimum is 78 or 88.
