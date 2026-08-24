# SIZE-TWO-CYCLIC: separation-orbit core of the `q = 8` parity obstruction

## Question

`AgreementAt t` caps common neighbours for every nonzero translation between
two sources in fibre `t`.  At `q = 8` there are four undirected source
separations, represented by `1,2,3,4`.  Which of those shifts actually carry
the loopless parity-class contradiction?

The direct graph probe's `--c4-separation d` option retains only the selected
undirected separation orbits.  All runs here retain every allowed fibre in
one parity class and vary the separation subset.

## Minimal cores

For the critical parameter `a = 2`, both parity classes have the unique
inclusion-minimal UNSAT separation set

```text
{1,2,4}.
```

Every proper subset is SAT.  The other three-element subsets `{1,2,3}`,
`{1,3,4}`, and `{2,3,4}` are also SAT.  Thus separation `3` can be deleted
entirely, but each of `1`, `2`, and the antipodal separation `4` is essential.

The same `{1,2,4}` restriction is UNSAT for both parity classes at each of
`a = 1,2,3`.  The exceptional parameter `a = 0` has, for both parity classes,
the unique minimal core

```text
{1,3,4}.
```

There every proper subset and every other three-element subset is SAT.

Representative command:

```bash
python3 size_two_cyclic_exact_graph_probe.py 8 --a 2 \
  --c4-pair-mode same-difference \
  --c4-difference 0 --c4-difference 4 --c4-difference 6 \
  --c4-separation 1 --c4-separation 2 --c4-separation 4 \
  --quiet-model --timeout-ms 180000
```

This returns UNSAT; deleting any one `--c4-separation` flag returns SAT.

## Fibre-resolved minimal core at `a = 2`

The probe also accepts individual cap groups as
`--c4-fiber-separation t:d`.  Resolving the even parity obstruction into its
nine fibre/separation groups produces the following five-group MUS:

```text
(t,d) = (0,1), (0,2), (4,1), (4,4), (6,2).
```

These five groups together are UNSAT, while deleting any one is SAT.  In
particular, the antipodal cap is needed only in the middle fibre `t=4`, not
throughout the parity class.  The reflected odd MUS is

```text
(t,d) = (7,1), (7,2), (3,1), (3,4), (1,2),
```

and again every one-group deletion is SAT.

Minimizing the excess in the deleted group gives an exact defect vector for
the even MUS:

| deleted group `(t,d)` | minimum separation-`d` excess in fibre `t` |
|---|---:|
| `(0,1)` | `8` |
| `(0,2)` | `8` |
| `(4,1)` | `4` |
| `(4,4)` | `2` |
| `(6,2)` | `4` |

Each value is certified by SAT at the displayed cap and UNSAT one below.
Minimum witnesses consist of whole reversal orbits of codegree-two source
pairs: eight pairs for the first two groups, four for the next and last, and
the two antipodal pairs already seen at `(4,4)`.  Consequently the five-cell
terminal is not merely forcing one repeated target label; its local defects
come in the rigid orbit sizes `8,8,4,2,4`.

By `CollisionDuplicateDuality`, the same excess counts repeated target labels
inside reverse routing blocks.  Hence every four-cell deletion forces positive
reverse-duplicate load in precisely the missing cell.  This is a covering
profile, but the unequal orbit sizes do not themselves give a uniform
five-cell conservation identity: the generic exclusion still needs an
inequality forcing at least one of those five duplicate patterns twice.

## Consequence and stop

The q8 parity target does not need full `AgreementAt` on all shifts.  It needs
the antipodal shift plus two short shifts, with a genuine parameter split:
`a=0` uses the odd short shifts `{1,3}`, while `a=1,2,3` use `{1,2}`.
Therefore a proof that treats all nonzero translations symmetrically carries
substantial slack, and a purported uniform three-shift proof must account for
the `a=0` exception.

At the harder `a=2` parameter the actual finite obstruction is smaller still:
five cap groups arranged across three fibres, with the unique half-turn group
at the reflected middle fibre.  This is now a concrete ternary interaction
pattern rather than a generic parity-class extremal problem.

This is exact finite evidence, not a q-generic theorem.  The promising formal
refinement is a separation-resolved version of the parity block balance or
codegree count, centered on the involution shift `q/2` and the two
parameter-selected short shifts.  No such identity is proved here.
