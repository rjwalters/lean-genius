# Howell-design and strong-orthomorphism audit

Date: 2026-08-24

Scope: `BinarySizeTwoCyclicPackingBound`; goal #36 outside-literature pass

## Verdict

Howell designs give a close language for one part of the cyclic routing
object: partial permutation matrices with pairwise overlap at most one are
packing arrays, and Howell designs are equivalently pairs of orthogonal
one-factorizations.  Their starter-adder constructions also isolate a
striking binary-order obstruction.  A **strong orthomorphism** `Y` of an
abelian group requires all three maps

```text
Y,  Y + I,  Y - I
```

to be permutations.  Anderson--Gross cite the Hall--Paige theorem that a
group with cyclic Sylow-2 subgroup has no strong orthomorphism.  Thus
`Z/(2^k)` is exactly on the nonexistence side.

This theorem does **not** apply directly to the size-two cyclic code.  The
obvious candidate is formally false: inside every routing block,
`P_(x,t)` is a two-punctured partial permutation but
`P_(x,t)-I = targetDifference(x,t,-)` is not injective when `4 | q`, by

```text
SizeTwoCyclicReciprocalPermutationCode.
  not_injective_targetDifference_of_four_dvd.
```

Consequently a proof which calls one completed routing block a strong
orthomorphism silently adds a false Costas/autocorrelation hypothesis.  The
Hall--Paige obstruction can survive only if reciprocity assembles a *new*
map on reverse-fragment components across several blocks.

## Exact one-fiber comparison

Fix a difference fiber `t`.  In absolute coordinates the code supplies `q`
two-punctured partial permutation matrices `M_(x,t)`, one for each base `x`.
The row holes of `M_(x,t)` are `{x+t,x+t+1}` and its column holes are
`{x,x-1}`.  For distinct bases,

```text
|M_(x,t) intersect M_(x',t)| <= 1.
```

This is the permutation-packing aspect of a Howell design.  But it is not an
`H(s,2n)` as stated in the literature: the symbols/base matrices have moving
two-row and two-column holes, while a Howell symbol must occur exactly once
in every row and column.  Filling the two holes completes each `M_(x,t)` to
a permutation, but there are two completions and neither the agreement cap
nor reciprocity canonically chooses one.  The completed permutations also
need not preserve the pairwise-overlap bound at the inserted cells.

The more important mismatch is that Howell pair uniqueness is internal to
one array.  Routing reciprocity sends an entry of `M_(x,t)` to an entry of a
generally different `M_(y,s)`, with both new indices depending on the entry.
It is therefore not one of the two fixed one-factorizations attached to a
single Howell array.

## Why the tempting strong-orthomorphism map fails

Write the relative routing permutation as

```text
P_(x,t)(r) = r + targetDifference(x,t,r).
```

If its two holes could be filled so that `P`, `P-I`, and `P+I` were all
permutations, this would be a strong orthomorphism of `Z/q` and Hall--Paige
would immediately exclude every `q=2^k`.  However the kernel-checked
noninjectivity theorem above concerns two surviving rows, so filling the
holes cannot repair `P-I`.  This kills the single-block route before any
completion choice is made.

It also explains why ordinary starter, Costas-array, optical-code, and
Howell bounds miss the observed q=8 obstruction: those theories impose
internal difference uniqueness, whereas the cyclic code forces internal
difference collisions and must transport them through reversal.

## Surviving bounded question

The only non-refuted Hall--Paige-shaped candidate is global.  Fold at
`q=2m`, decompose each block into its two canonical boundary paths, and use
reciprocity to connect every lifted path dart to the reverse dart in another
block.  If the resulting reverse-fragment components admit a canonical
index set `G` and transition map `Y`, then test whether the same-difference
agreement cap forces `Y`, `Y+I`, and `Y-I` to be injective.

This is deliberately a conditional target, not a conjecture yet.  A bounded
q=8 probe must first produce the component set and candidate `Y` without a
choice of path orientation or hole completion.  Stop immediately if either
choice changes the injectivity verdict.  Only after that test would the
strong-orthomorphism theorem supply a plausible q-generic terminal.

## Literature

- B. A. Anderson and K. B. Gross, *Starter-adder methods in the construction
  of Howell designs*, J. Austral. Math. Soc. Ser. A 24 (1977), 375--384,
  especially Definition 4 and Theorems 7--8.
- M. Hall and L. J. Paige, *Complete mappings of finite groups*, Pacific J.
  Math. 5 (1955), 541--549.

The useful contribution of this literature pass is therefore a sharp
no-go: do not identify a routing permutation or its target-difference map
with a strong orthomorphism.  Any valid use of Hall--Paige must be a new
multi-block reverse-fragment construction and must pass the choice-free q=8
test first.
