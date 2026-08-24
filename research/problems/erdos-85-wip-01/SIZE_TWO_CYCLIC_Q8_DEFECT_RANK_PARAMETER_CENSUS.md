# q8 defect-rank parameter census

Node: quantitative cap-free amplification toward
`BinarySizeTwoCyclicPackingBound`.

## Exact result

For a source `p`, let `r(p)` be the number of target fibres receiving no
edge from `p`.  Exact degree makes this equal to the total positive block
excess at `p`.  Under exact row/absolute-column hits and loopless
reciprocity, with no same-fibre caps, the minimum of `sum_p r(p)` at q8 is:

```text
reflection parameter a    holes {a,-1-a}    minimum sum r
0                         {0,7}                    78
1                         {1,6}                    64
2                         {2,5}                    64
3                         {3,4}                    88
```

The four rows exhaust the unordered reflection-hole pairs.  In each row the
lower threshold is UNSAT and the displayed threshold is SAT.  The pure
Boolean option `--max-total-defect-rank` was used.  Both sides for `a=0` and
`a=3` were independently exported through the theory-atom validator and
checked with Kissat (exit 20 below the threshold, exit 10 at the threshold),
in addition to native Z3.

Representative commands are:

```text
python3 size_two_cyclic_full_probe.py 8 --a 3 --no-caps \
  --max-total-defect-rank 87 --dimacs /tmp/q8a3-rank87.cnf
kissat /tmp/q8a3-rank87.cnf                 # UNSAT

python3 size_two_cyclic_full_probe.py 8 --a 3 --no-caps \
  --max-total-defect-rank 88 --dimacs /tmp/q8a3-rank88.cnf
kissat /tmp/q8a3-rank88.cnf                 # SAT
```

## The a=3 extremal profile

One rank-88 witness is periodic by base parity.  At every base the six
source fibres have ranks

```text
{1,1,2,2,2,3},
```

so the base contributes 11 and the global source-rank distribution is

```text
rank 1: 16 sources
rank 2: 24 sources
rank 3:  8 sources.
```

This is not merely the rank-64 profile with a few displaced exceptional
sources.  Loads of three occur, and the high-rank source fibre changes with
base parity.  The stronger cap-free amplification is therefore already a
base-resolved reciprocal phenomenon.

## Consequence for the prospective theorem

The conjectural q-generic inequality

```text
sum_p r(p) >= q^2
```

survives every q8 reflection parameter, but its equality classification
must distinguish the hole phase.  Equality is attained only for `a=1,2`;
the outer phases `a=0,3` have strict margins 14 and 24 respectively before
any cap is imposed.

Accordingly, the reflection-orbit cap-coupling pattern found in the q8
rank-64 witnesses is an equality-branch mechanism, not a universal normal
form for every parameter.  A uniform proof can split cleanly:

1. prove the cap-free rank bound and classify which hole phases can attain
   equality;
2. use one- or two-reflection-orbit cap coupling only in those equality
   phases;
3. retain the strict cap-free margin for the other phases as the next rung
   of the amplification ladder.

The bounded census is evidence for this split, not its q-generic proof.
