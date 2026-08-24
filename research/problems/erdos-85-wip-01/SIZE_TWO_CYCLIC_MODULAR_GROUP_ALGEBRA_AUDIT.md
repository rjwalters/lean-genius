# Binary cyclic routing: group-algebra linearity gate

Node: `A-REG-NONBIP / BinarySizeTwoCyclicPackingBound`.

Status: goal #36 scope audit.  This note decides whether the full dyadic
transition tower is supplied automatically by repeated-root cyclic-code
theory.  It does not prove the packing bound.

## Ambient module

Let `q=2^k`, `G=Z/q`, and

```text
R = F_2[G] = F_2[z]/(z^q-1) = F_2[epsilon]/(epsilon^q),
epsilon = z+1.
```

Simultaneous translation `(x,y) -> (x+c,y+c)` acts on the allowed routing
cells and on unordered routing relations.  The binary vector space on these
relations is therefore a permutation `R`-module.  Reciprocity is built into
the unordered-edge coordinates and is `R`-stable.  If each exact row/column
hit equation is reduced modulo two, the resulting parity equations form an
`R`-stable affine linear system.  Differences of two parity solutions form an
`R`-submodule, so the epsilon-adic filtration legitimately applies to this
linear shadow.

This is exactly what the existing augmentation-valuation probe measures.  A
two-route collision at separation `d` has epsilon-adic depth `2^v2(d)`, and
translation carries the complete family of parity equations through all
levels at once.

## The exact routing object is not a code or affine submodule

The graph-free routing axioms contain two load-bearing constraints that are
not linear over `R`.

First, an allowed source has **exactly one** target in each permitted row and
column, not merely an odd number.  In edge variables this is

```text
sum_c e_(u,(r,c)) = 1                         over Z,
```

whereas the `R`-linear shadow retains only the same equation modulo two.  The
mod-two equation also permits 3, 5, ... hits.  Addition of two exact routing
objects gives 0 or 2 hits in each such row, so exact objects are not closed
under the module operation.  They lie inside an affine parity coset as a
constant-weight/permutation slice.

Second, the common-neighbour cap is the quadratic integer inequality

```text
sum_w e_(u,w) e_(v,w) <= 1.                  (GA1)
```

It is a correlation/support condition, not a parity check.  Reduction modulo
two remembers only the parity of the correlation and cannot distinguish one
common neighbour from three.  Neither addition in the permutation module nor
multiplication by a general element of `R` preserves `(GA1)`.

Consequently the set cut out by reciprocity + exact hits + cap is
translation-invariant, but it is **not** an `R`-submodule and the constraints
do not endow it with an affine-coset structure.  It is only a support-restricted
subset of the affine parity coset.  Translation symmetry must not be confused
with module linearity.

## What repeated-root cyclic-code theory does and does not give

Castagnoli--Massey--Schoeller--von Seemann, *On Repeated-Root Cyclic Codes*,
IEEE Trans. Inform. Theory 37 (1991), 337--342,
doi:10.1109/18.75249, develops the Hasse-derivative/ideal structure for
linear cyclic codes with repeated roots.  It applies directly to the parity
relaxation above and packages all epsilon-adic graded pieces without building
separate quotient graphs.

It does **not** enforce the permutation-weight slice or the quadratic
correlation cap.  Thus the squad's q8 finding has the expected algebraic
interpretation: every first-level/graded relaxation can be satisfiable while
the simultaneous exact support constraints are inconsistent.  The missing
information is extension data only in the loose sense that all levels must be
realized by one 0/1 constant-weight relation; it is not supplied by the ideal
classification of `R`.

The honest nonlinear interface is a family of correlation polynomials.  For
source vertices `u,v`, package the common-neighbour products into

```text
C_(u,v)(z) = sum_w e_(u,w)e_(v,w) z^(label(w)) in R.
```

The cap requires the integer support weight of each designated correlation
to be at most one.  Augmentation valuations of `C_(u,v)` can detect at which
dyadic separation a collision appears, but no valuation alone bounds that
weight.  A q-generic terminal would therefore need a theorem about
**constant-weight repeated-root cyclic objects with bounded correlations**,
or an equivalent difference-family/partial-orthomorphism theorem.  Ordinary
repeated-root code structure is only the ambient linear language.

## Verdict and stop rule

The proposed shortcut

```text
full routing axioms -> R-submodule -> repeated-root classification
```

is **stopped at the first arrow**.  The valid replacement is

```text
exact routing objects
  subset of an R-affine parity coset
  intersected with constant-weight and quadratic correlation constraints.
```

This still clarifies the next mechanism: consume all dyadic valuations of the
correlation family simultaneously while retaining integer support weight.
Do not build another theorem classifying ideals of `R`; that would classify
only a relaxation already known to admit models.  Revive the algebra route
only with a named correlation/difference-family theorem or a bounded probe
showing that the three core caps force an impossible epsilon-adic support
profile.

## Standard constant-weight correlation bounds: scale audit

Optical orthogonal codes and frequency-hopping sequences supply named bounds
for constant-weight families with correlation at most one.  The ordinary
Johnson bound still cannot be the missing terminal, even after strengthening
our hypotheses substantially.

Ignore the fact that the actual packing theorem caps only designated
same-fibre source pairs, and instead impose the common-neighbour cap on every
pair.  The neighbourhood vectors would then form a constant-weight binary
code with

```text
length N = q(q-2),
weight w = q-2,
family size M = q(q-2),
pairwise intersection <= 1.
```

For correlation one the Johnson packing bound is

```text
M <= floor(N/w * floor((N-1)/(w-1))).              (GA2)
```

At these parameters, `N/w=q` and, for `q>=8`,

```text
floor((N-1)/(w-1))
  = floor((q^2-2q-1)/(q-3))
  = q+1.
```

Thus `(GA2)` permits `q(q+1)` codewords, whereas the routing family has only
`q(q-2)`.  The gap is `3q`, in the wrong direction.  The actual partial cap is
weaker still, so neither the Johnson bound nor a bound depending only on
`(N,w,lambda,M)` can contradict the routing parameters.

This stops the generic optical-orthogonal-code shortcut.  A usable correlation
theorem must additionally consume the simultaneous one-per-row and
one-per-column structure, reciprocity, and the three designated difference
fibres.  In design language it must be a bound for partial permutation arrays
or cyclic difference matrices, not an ordinary constant-weight code bound.

## Permutation-array bounds: scope audit

Each source neighbourhood is a partial permutation matrix with `q-2` ones:
one hit in every permitted row and column, with two prescribed missing rows
and columns.  The same-fibre common-neighbour cap says that the `q` partial
permutations in a designated source fibre agree in at most one retained cell.
This invites the Hamming permutation-array bound.

For full permutations of length `q`, agreement at most one is distance at
least `q-1`.  When `q` is a prime power the sharp value is

```text
M(q,q-1) = q(q-1),
```

realized by a sharply two-transitive affine family.  The elementary general
upper bound is the same `q(q-1)`.  Our capped family has only `q` members in
one difference fibre.  Even the fictional strengthening that completed and
simultaneously capped all `q(q-2)` source neighbourhoods remains below the
generic maximum by `q`.

The actual comparison is weaker in two further ways: the cap is imposed only
within selected difference fibres, and completing the two holes may introduce
new agreements not controlled by the routing cap.  Therefore ordinary
permutation-array bounds cannot contradict these parameters.  A useful
theorem would have to classify a near-maximal *union of translated
two-punctured arrays* with reciprocity linking the arrays and with caps on
specified fibres.  That is substantially more structured than an
`(n,n-1)` permutation code; no such classification was found in this pass.

Primary scale reference: the standard sharp result `M(q,q-1)=q(q-1)` for
prime-power `q`, via Latin squares/affine permutations; see Bereg--Levy--
Sudborough, *Constructing Permutation Arrays from Groups*, Des. Codes
Cryptogr. 87 (2019), 2105--2128, and its summary of the Deza--Frankl bound.

This stops the generic permutation-array shortcut.  The phrase “partial
permutation array” remains useful vocabulary, but the missing theorem must
consume the translation-labelled hole pattern and reciprocity, not only
Hamming distance and family size.

## Packing-array bounds: orientation and scale audit

Stevens--Mendelsohn, *Packing Arrays*, Theoret. Comput. Sci. 321 (2004),
125--148, doi:10.1016/j.tcs.2003.06.004, is the closest named design-theory
framework found in the outside search.  A packing array has `b` rows and `k`
columns over a `g`-symbol alphabet, with every ordered symbol pair appearing
at most once in every pair of columns.  The paper also studies disjoint rows
and translates the objects to matchings and resolvable pairwise balanced
designs.

The orientation needed here gives no useful bound.  In one capped source
fibre, the `q` partial permutations become at most

```text
b = q,  k = q-2,  g ≈ q-2.
```

Even the elementary two-column packing ceiling `b ≤ g²` is then enormously
slack: `q ≤ (q-2)²` for `q ≥ 4`.  Stronger disjoint-row bounds from the same
framework control the number of common fixed columns, not the reciprocal
moving-hole pattern.

Trying to place all `q(q-2)` source blocks into one packing array is invalid:
their two deleted row positions and two deleted column positions translate
with the source base and difference fibre, so there is no single common set
of `q-2` columns or one fixed alphabet on which the packing-array axiom holds.
Padding the holes restores common columns but introduces uncontrolled symbol
agreements, exactly the completion problem already noted above.

Thus the named packing-array theory does not supply the required nonlinear
three-cap inequality.  A usable result would need to be a *cyclic moving-hole
packing array with reciprocal block transpose*, which is strictly more
structured than the published packing-array parameter bounds.  The outside
search found no theorem of that form.
