# Global two-hole completion holonomy audit

## Candidate

Divergence round 12 proposed completing every partial route and choosing its
parallel/cross bit coherently across all cells.  Perhaps transpose
reciprocity imposed nontrivial `Z/2` holonomy on those choices, with a
collision cycle forcing an inconsistency unless two labels merged.

This candidate is false before any collision or cap information is used.

## Canonical reciprocal completion

Write a cell as `(x,t)`, meaning absolute coordinates `(x,x+t)`.  Its route
omits target rows

```text
x+t, x+t+1
```

and target columns

```text
x-1, x.
```

The parallel completion adds the two artificial neighbours

```text
P0(x,t) = (x+t,   -t-1),
P1(x,t) = (x+t+1, -t-1).
```

Here the second coordinate is again the target difference.  If the globally
forbidden differences are `{a,-1-a}`, then the involution
`t |-> -t-1` preserves that set and therefore also preserves its complement.
Thus both artificial targets are valid cells whenever `(x,t)` is valid.

More importantly, the all-parallel choice is already reciprocal.  Put
`u=-t-1`.  Parallel completion at the first target gives

```text
P0(x+t,u) = (x-1,t),
P1(x+t,u) = (x,t),
```

and at the second target gives

```text
P0(x+t+1,u) = (x,t),
P1(x+t+1,u) = (x+1,t).
```

Hence each of the two artificial edges out of `(x,t)` occurs in the reverse
direction at its target.  Taking the parallel completion at **every** cell
produces a globally symmetric two-regular artificial graph.  This works for
every modulus and every allowed two-hole pair, with no use of binary
arithmetic, the agreement caps, an empty fibre, or the real route entries.

There are no artificial loops for even `q`: equality with `P0` would require
simultaneously `t=0` and `2t=-1`, while equality with `P1` would require
`t=-1` and `2t=-1`; both are impossible modulo an even number.

## Verdict

The completion-choice holonomy branch is **cut**.  Its putative obstruction
class is identically zero because the canonical all-parallel section is
globally reciprocity-compatible.  In particular, a self-paired fibre or
owner-pair locus cannot force a second target merely by applying the
completion involution: the completion symmetry exists independently of the
real collision tokens.

A future completion argument would have to couple the artificial section to
the *actual* route entries or to the full-cap collision labels.  Merely
requiring global transpose symmetry, even over the entire moving-hole
family, adds no constraint.  The surviving round-12 candidates are therefore
the integer divided/symmetric-square boundary identity and genuinely global
duplicate/missing-resolver circulation, not completion-bit parity.
