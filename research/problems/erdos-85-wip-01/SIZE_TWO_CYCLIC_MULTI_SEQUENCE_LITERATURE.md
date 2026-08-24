# Multi-sequence correlation translation for the size-two cyclic code

## Scope

This note audits the multi-sequence literature route to
`BinarySizeTwoCyclicPackingBound`.  It is separate from the Costas and
orthomorphism route: the latter asks for distinct differences *inside one*
permutation, while the reduced code bounds agreements *between different*
base-source permutations.

The verdict is negative but precise.  Frequency-hopping, optical-orthogonal,
and group-divisible packing languages each retain one part of the structure,
but none retains the particular combination on which the q=6/q=8 UNSAT
instances depend: moving two-point holes, one prescribed alignment per source
pair, and reciprocal coupling across difference fibers.

## Absolute-coordinate form

Fix an allowed difference `t`.  For each base source `x`, write the routing
edge belonging to relative row `r` as

```text
y = x+r,
z = x+P_(x,t)(r).
```

Thus `P_(x,t)` becomes a partial permutation matrix `M_(x,t)` on the common
`Z/q × Z/q` row-column torus.  Its exact holes are

```text
row holes:    {x+t, x+t+1},
column holes: {x,   x-1}.
```

It has `q-2` entries.  If `x' = x+d`, the Lean structure
`SizeTwoShiftedPermutationAgreement` is exactly a common edge of
`M_(x,t)` and `M_(x',t)`: its second relative row is `r-d`, so both absolute
rows equal `x+r`, and `column_eq` says that the absolute columns agree.
Consequently

```text
|M_(x,t) ∩ M_(x',t)| ≤ 1             (x ≠ x').
```

For every fixed `t`, the reduced code is therefore a packing of `q`
two-punctured partial permutation matrices with translated holes.  The
reciprocity axiom does not live inside this one packing.  It sends the dart

```text
(x,t) --r--> (x+r,s)
```

to the reverse dart

```text
(x+r,s) --(-r)--> (x,t),
```

and hence couples the packings belonging to different `t` and `s`.

## Frequency-hopping sequences: the missing shifts

An FHS set controls periodic Hamming correlations over cyclic time shifts.
The Peng--Fan bounds are lower bounds on the maximum nontrivial Hamming
correlation after ranging over the relevant sequence pairs and shifts.  See
Chen--Lin--Ling--Liu, *Three new classes of optimal frequency-hopping
sequence sets*, arXiv:1605.03454, and Bao--Ji, *Frequency hopping sequences
with optimal partial Hamming correlation*, arXiv:1511.02924.

The absolute-coordinate sequence attached to `M_(x,t)` has two erasures and
alphabet `Z/q`.  For the pair `x,x+d`, the code bounds the single alignment
dictated by `d`.  It supplies no bound for the other `q-1` cyclic shifts of
that same pair.  Equivalently, after returning to relative rows it compares

```text
P_(x,t)(r)  with  d + P_(x+d,t)(r-d),
```

and no analogous inequality is assumed with an independent shift parameter.
Therefore Peng--Fan double counting cannot be instantiated: the correlations
over which its average is taken are mostly unconstrained here.  Adding them
would strengthen `SizeTwoCyclicSameDifferenceCode`, not re-express it.

Average-Hamming-correlation results have the same issue.  Uniformly
distributed FHS sets attain the usual average bound (Chung--Yang,
arXiv:1108.3415), whereas the size-two terminal must distinguish a highly
structured reciprocal family from aggregate-uniform controls already known
to be feasible.  Those bounds forget exactly the cross-fiber location data.

## Optical orthogonal codes: autocorrelation is false here

Optical orthogonal codes translate auto- and cross-correlation constraints
into internal and external difference multiplicities of subsets of a cyclic
group.  Huczynska--Ng, *Optical orthogonal codes from a combinatorial
perspective*, arXiv:2411.06955, gives the modern dictionary and explicitly
separates the two correlation parameters.

The cross-correlation side resembles the agreement-at-most-one law, but the
autocorrelation side requires internal difference control for each codeword.
That is not merely unproved in the routing code.  The kernel-checked theorem

```text
SizeTwoCyclicReciprocalPermutationCode.
  not_injective_targetDifference_of_four_dvd
```

shows that whenever `4 ∣ q`, every routing fiber has two distinct rows with
the same target difference.  Hence the natural autocorrelation-one/Costas
specialization is false for every binary parameter in the terminal.  OOC
Johnson-type bounds cannot be transferred without deleting the forced
collisions that reciprocity must exploit.

## Holey and group-divisible packings: reciprocity is absent

The fixed-`t` family can also be viewed as a packing with two transverse
hole systems.  Holey group-divisible packings require blocks to meet each
group and hole sparsely and require eligible pairs to occur at most once;
this is the correct broad language for the moving row/column exclusions.
The literature uses precisely this translation to construct cyclic
multi-dimensional optical orthogonal codes; see, for example, the definition
and construction program in *Maximum w-cyclic holey group divisible
packings and their application to three-dimensional optical orthogonal
codes*, Discrete Mathematics 345 (2022).

This language is deliberately permissive.  It controls pair incidence and
leaves, not a fixed-point-free involution on routed darts which changes the
difference-fiber color.  Even-order holey and group-divisible packings are a
construction source, so their ordinary divisibility and leave bounds do not
exclude the binary parameters.  Encoding each routing edge as a size-two
block simply recovers the pairwise agreement ledger already known to be one
factor `q` too weak.

## Stop verdict and surviving object

No surveyed theorem applies directly:

| Literature object | Retained feature | Missing or false hypothesis |
|---|---|---|
| FHS set | cross-sequence Hamming agreement | bounds require all cyclic shifts; only one prescribed shift per source pair is controlled |
| partial-correlation FHS | windows and erasures | still averages a full shift family, absent here |
| OOC / external difference family | cyclic external differences | internal/autocorrelation bound is false by forced target-difference collision |
| holey group-divisible packing | moving groups/holes and pair packing | reciprocal dart involution across colors is absent |
| divisible-design graph | vertex classes and common-neighbor counts | requires exact classwise codegrees, while the reduced code has only upper bounds |

The honest external name for the terminal is therefore a **reciprocal
group-divisible packing of two-punctured partial permutations**.  Its novel
input is not another pair-count bound.  It is that every forced collision in
one partial permutation reverses into two routed darts in another difference
fiber, and the same source-pair agreement cap must hold simultaneously in at
least three fibers.  This matches the q=8 CNF observation that one- and
two-fiber restrictions are satisfiable while three selected fibers are not.

A useful next theorem must express that multi-fiber collision transport.
Applying a standard FHS, OOC, or group-divisible packing bound without first
proving the missing shift/reciprocity hypothesis would silently strengthen
the Lean structure and is invalid.
