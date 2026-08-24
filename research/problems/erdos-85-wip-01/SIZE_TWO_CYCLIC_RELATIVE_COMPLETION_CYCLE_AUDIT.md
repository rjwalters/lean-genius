# Relative two-hole completion cycle audit

## Question

For a fixed source fibre `t`, its route from base `x` is a partial
permutation from target rows to target columns.  Its missing rows are
`x+t,x+t+1`, and its missing columns are `x-1,x`.  There are exactly two
ways to complete it to a permutation.  Could the signs or cycle types of
the four pairs of completions at bases `0,d` force two genuine common
target cells for the fixed source pair?

The probe now has `--dump-relative-completions`.  For each `t,d` it builds
both completions at both bases, computes the four relative permutations,
and prints their fixed-point counts, signs, and cycle types.  It separately
prints `genuine`, the number of fixed rows outside both pairs of missing
rows.  These are exactly the actual common target cells, not completion
artifacts.

## Bounded checks

The q=8 three-cap SAT control was run with

```text
python3 size_two_cyclic_translation_invariant_probe.py 8 --a 1 \
  --cap 0:1 --cap 0:2 --cap 4:1 \
  --dump-relative-completions --timeout-ms 300000
```

and the q=12 five-cap empty-middle countermodel with

```text
python3 size_two_cyclic_translation_invariant_probe.py 12 --a 1 \
  --cap 0:1 --cap 0:3 --cap 6:1 --cap 6:6 --cap 9:3 \
  --empty-fiber 6 --dump-relative-completions --timeout-ms 300000
```

Both are SAT.  In every row at both orders, the signs of the four relative
permutations are

```text
[even, odd, odd, even].
```

This is tautological: changing either completion swaps the two missing
columns, hence composes that permutation with one transposition.  It uses
neither the hit pattern nor the consecutive placement of the missing rows.

More decisively, the same sign pattern occurs for q=8 source pairs with
only one genuine common target and for pairs with two, three, or four
genuine common targets.  The completion fixed-point counts do not repair
this loss: artificial fixed points on the union of the four missing rows
vary with the completion.  For example the q=8 output contains

```text
relative fiber=0 shift=4 genuine=2 fixed=[2,3,3,4] signs=[0,1,1,0]
relative fiber=0 shift=3 genuine=1 fixed=[1,1,1,1] signs=[0,1,1,0]
```

and many further one-target rows with the identical sign vector but
different cycle types.  The q=12 model exhibits the same phenomenon at
larger support sizes.

## Verdict

The bare relative-permutation sign/fixed-point route is **cut**.  Completion
sign is generic two-hole bookkeeping and cannot force the required second
genuine target.  Full cycle type is model-dependent and supplies no parity
constraint on genuine fixed points after the artificial hole rows are
removed.

A completion argument could only become relevant again with an additional
colored invariant that distinguishes genuine fixed rows from repaired hole
rows.  That is already the polarized/exterior-square problem, not a cheaper
permutation-sign terminal.  The surviving directions remain coherent
dyadic halving and the full-cap collision-Levi shortest-cycle route.
