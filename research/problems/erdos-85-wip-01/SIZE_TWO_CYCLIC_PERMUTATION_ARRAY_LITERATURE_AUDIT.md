# Size-two cyclic permutation-array literature audit

## Candidate import

Each source cell defines a two-hole partial permutation from admissible target
rows to admissible absolute target columns.  The cap says that two sources in
one difference fibre agree in at most one **precise target cell**.  Could a
standard permutation-code bound exclude all `q(q-2)` source cells?

## Available sharp ordinary bound

For a code `C subset S_n` of full permutations with minimum Hamming distance
at least `n-1` (equivalently, any two permutations agree in at most one
position), the standard Singleton/double-count bound is

```text
|C| <= n(n-1).
```

Equality is equivalent to a sharply 2-transitive set and hence to a
projective plane of order `n`.  A convenient primary reference is J.
Bierbrauer and K. Metsch, *A bound on permutation codes*, Electronic Journal
of Combinatorics 20(3) (2013), Proposition 3:
<https://citeseerx.ist.psu.edu/document?doi=1480a427283a6a1e9670154d4fdaea502bd60677&repid=rep1&type=pdf>.

The general Singleton analogue and its sharply transitive equality case are
also summarized by Peter Cameron:
<https://maths.qmul.ac.uk/~pjc/preprints/permcode.pdf>.

## Why it does not apply sharply enough

There are two independent gaps.

First, the code objects are partial permutations with two **moving** domain
and codomain holes.  Completing those holes to permutations can create new
agreements, so the same-fibre cap on genuine route cells does not imply that
the completed permutations have distance at least `q-1`.  Prior completion
audits found no canonical cap-preserving choice.

Second, even under the favorable false assumption that all `q(q-2)` source
cells formed one ordinary distance-`q-1` permutation code of length `q`, the
bound would read

```text
q(q-2) <= q(q-1),
```

leaving slack `q`.  Applying it separately to each of the `q-2` source
fibres is much weaker still: each class has only `q` words.

The sharp equality/projective-plane classification is therefore irrelevant;
the packing interface is below the extremal size where it activates.

## Missing strengthened theorem

What would be useful is not an ordinary permutation-array bound but a
**self-dual labelled partial-permutation bound** that simultaneously uses:

1. the two affine moving row holes and the two affine moving column holes;
2. reciprocity between source-fibre/target-fibre blocks;
3. pairwise agreement at most one only within each labelled source fibre;
4. full internal support; and
5. the exact load-variance identity and cap ceiling.

No theorem with this hypothesis pattern appeared in the permutation-array,
MOLS, or sharply-transitive literature located in this pass.  Classical
results forget precisely the block labels and reciprocity that distinguish
the q8 reciprocal UNSAT system from its directed SAT relaxation.

## Verdict

Generic permutation-code/Singleton/Delsarte imports are **cut**.  They cannot
close the positive-variance branch and should not be cited as a substitute
for the missing pair-rooted amplification inequality.  A literature route
revives only if an explicitly self-dual, moving-hole partial-permutation
theorem is found.
