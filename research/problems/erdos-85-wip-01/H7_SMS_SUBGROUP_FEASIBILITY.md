# H7 SMS subgroup feasibility

Date: 2026-08-26

This is the bounded source-level follow-up to
`H7_SMS_PIVOT_AUDIT.md`.  It tests whether stock SAT Modulo Symmetries
(SMS) can soundly use the relabeling symmetry already proved for the
canonical H7 empty-cube problem.  It does not run H7 and does not authorize
another binary split.

## Versions inspected

* SMS `63958bd09a871e484c59270a1d0f22d482dc5770`;
* LeanSMS `f5e95289e85fd7b019e768ef759a11f736802f30`.

There is no local `smsg` installation.  The upstream source was inspected
without installing it into the workspace or system.

## Exact group required by H7

Before an empty-sector mask is fixed, the proved relabeling is the diagonal
action of `S7` on all three low-vertex roles:

* seven empty-support vertices;
* fourteen singleton-support vertices, indexed by `Fin 7 x Fin 2`;
* twenty-one pair-support vertices, indexed by `Sym2 (Fin 7)`.

This is one group of order `7! = 5040`, not three independently permutable
blocks.  For the current hard parent `cube_F6_t2`, the mask is
`1048903`, with edges

```text
(0,1) (0,2) (0,3) (1,2) (1,4) (5,6)
```

Its labeled orbit has size 1260 and its stabilizer in `S7` has order 4.
Those four induced permutations, acting simultaneously on all 42 low
vertices, are the exact group available inside this cube.

## What stock SMS can express

`smsg` exposes `--initial-partition`, implemented in `src/options.cpp` as a
sequence of contiguous block sizes.  The minimality checker then searches all
permutations preserving block membership.  Thus `--initial-partition 7 14 21`
uses

```text
S7 x S14 x S21
```

of order

```text
22448266013011335649028997120000000
```

rather than the diagonal `S7`, and is unsound.  Refining the partition cannot
encode the correlations between the three actions.  The public command-line
interface has no arbitrary permutation-group, generator, or subgroup option.

The source contains a `MultipleMinimalityChecker`, but the stock graph solver
does not expose a multilayer command-line mode that restricts permutations to
automorphisms of a fixed layer.  More importantly, merely fixing a relational
template as unit clauses is not sound: stock minimality still considers a
permutation that moves that labeled template.  The resulting domination
clause can discard a satisfying assignment even though its permuted graph
violates the fixed-template units.

## LeanSMS boundary

LeanSMS can check that a learned clause is a genuine lexicographic domination
clause for its recorded permutation (`verifyDominationFull`).  Its general
impossibility argument then uses invariance of the encoded graph property
under graph isomorphism.  Checking domination alone does **not** prove that an
H7 canonical formula is invariant under the recorded permutation.

Consequently, feeding stock SMS output to LeanSMS does not close the gap:
each recorded permutation must additionally be proved to be induced by an
allowed high-label relabeling (and, for a fixed cube, to stabilize its mask).

## Verdict and smallest sound implementation

The proposed fixed-template experiment is **not feasible with the stock SMS
CLI**.  Running `smsg -v 42`, using `--initial-partition 7 14 21`, or adding a
fixed second layer would all permit unjustified permutations.

A sound bounded prototype needs both of these changes:

1. a subgroup-aware minimality checker whose candidates are the explicit
   induced permutations from the mask stabilizer (four for `cube_F6_t2`), or
   a checker that first proves preservation of the relational template;
2. a Lean-side gate that rejects every symmetry certificate unless its
   42-vertex permutation is exactly induced by a `Fin 7` permutation which
   stabilizes the bound empty mask.

For `cube_F6_t2`, enumerating four permitted permutations is simpler and less
risky than teaching the checker a general colored-template automorphism
algorithm.  This is the recommended next tiny-instance prototype.  Until both
gates exist, no SMS-learned clauses should be appended to the canonical CNF.

