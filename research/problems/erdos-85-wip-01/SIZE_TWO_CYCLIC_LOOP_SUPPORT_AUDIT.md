# SIZE-TWO-CYCLIC: diagonal-support audit at `q = 8`

## Question

The reduced reciprocal relation is symmetric but need not be loopless.  The
three same-difference common-neighbour constraint families at source
differences `0,2,4` are jointly inconsistent, although every pair is
consistent.  Is that failure already explained by incompatible demands on
the number or location of diagonal entries?

## Probe

`size_two_cyclic_exact_graph_probe.py` now accepts `--loop-count-cap N` and
`--loop-profile`.  A loop is a chosen diagonal entry of the symmetric
relation; its difference fibre is `y-x (mod q)` for the corresponding cell
`(x,y)`.

All runs below used

```text
q=8, a=1, --c4-pair-mode same-difference, --allow-loops
```

and retained only the displayed source-difference families.  Satisfiability
with a loop cap, together with unsatisfiability at the preceding cap, gives:

| retained families | minimum loop count |
|---|---:|
| `{0}` | `0` |
| `{2}` | `0` |
| `{0,2}` | `0` |
| `{4}` | `8` |
| `{0,4}` | `8` |
| `{2,4}` | `16` |

The boundary checks were direct Z3 checks.  In particular, `{4}` and
`{0,4}` are UNSAT with cap `7` and SAT with cap `8`; `{2,4}` is UNSAT with
cap `15` and SAT with cap `16`.  The unrestricted triple `{0,2,4}` remains
UNSAT even though all diagonal entries are available.

One minimum-loop model for each constraint set containing `4` had the
following loop profile:

```text
{4}:   total=8,  by_difference={2:2, 3:2, 4:2, 5:2}
{0,4}: total=8,  by_difference={2:2, 3:2, 4:2, 5:2}
{2,4}: total=16, by_difference={2:4, 3:4, 4:4, 5:4}
```

These profiles are witnesses, not yet a proof that every minimum model is
balanced.

## Outcome

The naive diagonal-support explanation stops here.  Family `0` costs no
additional loops when added to family `4`, while family `2` raises the exact
minimum by eight; nevertheless the triple is impossible with an unlimited
loop budget.  Thus total loop count cannot by itself certify the target
contradiction.

The sharp `8 -> 16` jump is still a useful structural clue.  A viable next
lemma would have to refine loop count into positions (or orbitwise incidence)
and show that family `0` forbids every placement by which `{2,4}` attains its
minimum.  Before attempting that proof, enumerate or block minimum
`{2,4}` models and test whether their loop profiles and cyclic translates are
forced; the single balanced witness above is not enough.
