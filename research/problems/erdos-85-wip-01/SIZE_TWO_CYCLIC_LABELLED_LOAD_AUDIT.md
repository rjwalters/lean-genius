# Labelled fibre-load equality audit

This tests the equality branch of divergence round 16's full-support route.
Unlike scalar moments, it retains every source/target fibre label.

For an allowed source fibre `t` and target cell `v`, define

```
k_t(v) = number of neighbours of v whose source lies in fibre t.
```

The zero-collision equality case is `k_t(v)=1` for every `t,v`.  It implies
full internal support, and its same-fibre common-target collision energy is
zero.  The full probe now exposes this condition as
`--uniform-fibre-loads`.

## Exact contradiction under reciprocity

Write `D` for the `q-2` allowed differences and let `A_tu` be the q-by-q
adjacency block from source fibre `t` to target fibre `u`.

Uniform loads say every column of every `A_tu` has sum one.  Reciprocity
gives `A_ut=A_tu^T`; applying uniform loads to `A_ut` says every row of
`A_tu` also has sum one.  Hence each block is a permutation matrix.  Write
its row permutation as

```
p_tu(x) = target base reached from source base x.
```

For fixed `(x,t)`, exact target-row hits say the multiset of `p_tu(x)` over
`u in D` is every residue except `x+t` and `x+t+1`.  Exact absolute-column
hits say the multiset of `p_tu(x)+u` is every residue except `x` and `x-1`.
Subtracting the two sums in `Z/q` gives

```
sum_(u in D) u = 2(t+1).                                  (1)
```

The left side is independent of `t`.  Thus any two allowed differences
`t,s` obey

```
2(t-s)=0  in Z/q.                                         (2)
```

For `q>=6`, deleting only two residues from the q-cycle leaves two
consecutive allowed residues, so (2) would give `2=0 mod q`, impossible.
The q=4 instance can be checked directly (its allowed pair is also not
separated by q/2 under the admissible parameters).  Therefore reciprocal
uniform fibre loads are impossible for every relevant `q`.

This uses reciprocity essentially: without it, uniform column loads do not
give row sums for the same block.  The probe calibration agrees:

```
reciprocal: q=4 UNSAT; q=8 a=1,2,3 UNSAT; q=10 UNSAT;
            q=12 UNSAT; q=16 a=1 UNKNOWN at 120 seconds.
directed:   q=8 a=1 SAT; q=8 a=2,3 UNSAT;
            q=10 a=1,2,3 SAT; q=12 a=1,2 SAT.
```

The symbolic argument, not the finite verdicts, closes the equality case.

## Remaining terminal gap

The full cap gives only

```
sum_v choose(k_t(v),2) <= choose(q,2),
```

not zero collision energy.  Since `sum_v k_t(v)=q(q-2)` equals the number
of target cells, every excess load is balanced by a zero, but the cap allows
many such deviations.  The named packing exclusion still needs a stability
or descent theorem: from any nonuniform labelled load family satisfying all
caps, produce either a forbidden second common target or a new code with
smaller total collision energy.  The equality endpoint of such a descent is
now rigorously impossible by (1)--(2).

## Positive-variance first moment

There is a useful identity before taking the equality case.  Let
`b_tu(x)` be the number of neighbours from source `(x,t)` into target fibre
`u`.  Subtracting the sums of the exact target-row and absolute-column
multisets gives, for every source,

```
sum_(u in D) u * b_tu(x) = 2(t+1)                 in Z/q. (3)
```

Also `sum_u b_tu(x)=d`.  If `e_tu(x)=b_tu(x)-1`, then

```
sum_u e_tu(x) = 0,
sum_u u*e_tu(x) = 2(t+1) - sum_(u in D)u.                 (4)
```

Reciprocity identifies these block-row deviations with the target-load
deviations counted by `V`.  However, (4) alone is quantitatively too weak.
Exact integer dynamic programming, including `b_tt(x)>=1` from full internal
support, gives minimum squared deviation two for essentially every `(x,t)`
(and sometimes zero at q=10).  The resulting global lower bounds versus the
cap upper bound are

```
q=6:   48 <= V <= 120
q=8:   96 <= V <= 336
q=10: 120 <= V <= 720
q=12: 240 <= V <= 1320
q=16: 448 <= V <= 3360.
```

Thus the first labelled moment supplies only order `q^2` pressure against an
order `q^3` cap budget.  Higher pair-rooted correlations or a normalization
that decreases `V` are genuinely necessary; Cauchy--Schwarz applied to (3)
cannot close the terminal.
