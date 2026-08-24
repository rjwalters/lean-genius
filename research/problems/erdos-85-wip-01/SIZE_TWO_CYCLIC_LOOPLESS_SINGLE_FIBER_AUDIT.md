# Loopless single-fiber exclusion audit

## Target and scope

The exterior-graph consumer already supplies `Loopless`.  It is therefore
enough to exclude, for each binary-relevant `q`, a reciprocal two-hole code
with `AgreementAt t` for one suitably chosen allowed difference `t`.  This is
strictly weaker than the loop-permitting `BinarySizeTwoCyclicPackingBound`.

The finite data do **not** support exclusion for every allowed `t`.  Using
`size_two_cyclic_exact_graph_probe.py` with exact row/column laws, symmetry,
looplessness, and a common-neighbor cap only inside the named difference
fiber gives:

| `q`, `a` | single capped fibers that are UNSAT | single capped fibers that are SAT |
|---|---|---|
| `4`, `1` | none | `0,2` |
| `6`, `1` | `0,2,3` | `4` |
| `8`, `1` | `3,4` | `0,2,5,7` |

For example:

```text
python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 \
  --c4-pair-mode same-difference --c4-difference 4 --quiet-model
# unsat

python3 size_two_cyclic_exact_graph_probe.py 8 --a 1 \
  --c4-pair-mode same-difference --c4-difference 0 --quiet-model
# sat
```

The `q=4` exception is compatible with a theorem beginning at `q>=8`.  Two
`q=10` controls (`t=4,5`) returned `unknown` at 120 seconds and provide no
evidence either way.  No extrapolation from the small table is claimed.

## Literature gate

Three nearby theories were checked before pursuing a new argument.

1. Hall--Paige/complete mappings exclude a *full* orthomorphism of a cyclic
   even group.  Here every routing map is two-punctured, and the banked theorem
   `not_injective_targetDifference_of_four_dvd` already shows that its target
   differences repeat.  Thus it cannot be completed to the injective object
   to which Hall--Paige applies.
2. Costas arrays impose uniqueness of every displacement vector inside one
   permutation.  `AgreementAt t` instead bounds intersections between the
   `q` translated, punctured permutations.  Ordinary Costas nonexistence or
   enumeration therefore has the wrong quantifiers.
3. Partial-transversal completion theorems for cyclic Latin squares concern
   completing one punctured transversal.  They do not impose reciprocal
   coupling among a family of `q` such transversals.

References consulted: Hall--Paige, *Complete mappings of finite groups*,
Pacific J. Math. 5 (1955), 541--549; *A random Hall--Paige conjecture*;
K. Drakakis, *A review of Costas arrays*, J. Applied Math. 2006; and
Kuhl--McGinn--Schroeder, *Completing partial transversals of Cayley tables of
Abelian groups*, EJC 28(3) (2021), P3.60.  None states the needed reciprocal
two-hole family theorem.

## Candidate mechanisms and bounded reduction

The initial mechanism list was: punctured Hall--Paige completion; line-label
parity; an involution quotient/Moore bound; a Gram-rank obstruction; forced
translation of the duplicate target difference; and polynomial/permanent
identities.  Existing countermodels or banked results cut three immediately:

* generic packing/Gram bounds are too weak at the available density;
* line parity alone survives SAT single-fiber controls;
* Hall--Paige cannot be invoked because target-difference injectivity is
  false in every fiber.

The two honest successors are therefore:

1. **Fiber selection.** Prove that reciprocity makes the forced duplicate
   target difference visit a distinguished allowed fiber `t` (the small data
   suggest, but do not prove, a half-turn/central choice).
2. **Reversal-local collision.** On that fiber, combine the fixed-point-free
   route-reversal involution with `AgreementAt t` to force two translated
   source matchings to share two targets.

The banked parity theorem
`sizeTwoCyclicTargetDifferenceMultiplicity_diagonal_sum_even` is a necessary
input to (2), but not a terminal: SAT controls at `q=8,t=0,2,5,7` satisfy it.
Any next parity statement must distinguish the selected fiber rather than
sum over all line labels.

## Stop result

No standard complete-mapping, Costas-array, or partial-transversal theorem
directly closes the loopless single-fiber target.  The finite target must be
stated existentially in `t`, not universally.  Further useful work should
attack fiber selection or a selected-fiber reversal invariant; another
unlabelled collision total is not informative.
