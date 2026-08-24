# Size-two cyclic global sharp-defect circulation audit

## Candidate terminal

In a collision-minimal positive-variance code, one hopes every source cell
has the sharp profile with one duplicated and one missing target fibre.  The
banked displacement and reciprocity theorems then give a global cocycle on
the aggregate missing-defect counts.  Full internal support adds the new
condition that a source can never miss its own fibre.  Could these aggregate
conditions already be inconsistent?

## Exact integer relaxation

Let `D` be the allowed difference fibres and put

```text
delta_t = 2(t+1) - (q(q-1)/2 + 1)  in Z/q.
```

For `t,u in D`, let `f_t(u)` be the number of bases in source fibre `t`
whose sharp profile misses target fibre `u`.  The duplicate is then
`u+delta_t`.  The tested integer system is:

```text
f_t(u) >= 0;
sum_(u in D) f_t(u) = q;                       (q source bases)
f_t(t) = 0;                                    (full internal support)
f_t(u) = 0 if u+delta_t is not in D;           (duplicate remains allowed)

f_t(u-delta_t) + f_u(t)
  = f_u(t-delta_u) + f_t(u)                    (sharp cocycle)
```

where a shifted term is zero when its preimage is outside `D`.  The last
line is exactly the count-level content of the banked theorem
`sizeTwoCyclicSharpDefect_cocycle`.

## Bounded verdicts

Z3 finds integer solutions at all tested orders:

```text
q=8,  a=2    SAT
q=8,  a=1    SAT
q=12, a=1    SAT
q=16, a=1    SAT
```

For example, at `q=8,a=2`, order the fibres as
`D=(0,1,3,4,6,7)`.  One solution is

```text
f =
[0 4 0 0 0 4]
[4 0 0 4 0 0]
[0 0 0 4 4 0]
[0 4 4 0 0 0]
[0 0 4 0 0 4]
[4 0 0 0 4 0].
```

Every row sums to eight, every diagonal entry is zero, every positive entry
has its displaced duplicate inside `D`, and all cocycle equations hold.  The
q12/q16 solutions similarly concentrate counts on one, two, or four allowed
missing fibres; their existence shows that increasing the binary order does
not remove the relaxation.

## Verdict

Aggregate sharp-defect circulation is **cut**, even after adding full
internal support and the exact displacement law.  It cannot supply the
positive-variance amplification theorem.

What the relaxation forgets is precisely the base-resolved realization:
which two source bases form each duplicated pair, which target cell owns
that pair, and the cap requirement that the same source pair cannot acquire
a second owner.  A surviving mechanism must therefore retain the owner
hypergraph or an equivalent degree-six/multi-source flag tensor.  Further
linear algebra on the count matrix `f_t(u)` cannot prove the packing
exclusion.
