# Stage-1 service spectrum

## Mathematical scope

This directory's `(4,4,4,4)` model belongs to the exact `d = 16`,
minimum-layer `s = 0` branch.  The four entries are the reduced orders of
the four used second-order-defect components, hence their actual orders are
four copies of `12`.  The upstream graph facts used by the encoder are the
`degree_sixteen_zeroLayer_*` lemmas, including the used-component order
package, the cycle-cover interface, the row split, and the common-neighbor
partition.

The scope is deliberately narrower than the whole zero-layer branch.  The
exact arithmetic census in `census_v5_table.txt` leaves 62 of the 231
reduced-order partitions as survivors of that relaxation, and `(4,4,4,4)`
is one of them.  Consequently a verified UNSAT result for the symbolic
model excludes the corrected zero-layer `(4,4,4,4)` service class only.  It
does not by itself exclude the other zero-layer partitions, either the
`s = 2` or `s = 4` degree-sixteen branches, or the ambient Erdős 85
problem.  The `s = 2` and `s = 4` branches are instead eliminated by the
separate Lean theorems `false_of_degree_sixteen_twoLayer` and
`false_of_degree_sixteen_fourLayer`, with
`degree_sixteen_remaining_zeroLayer` reducing the surviving degree-sixteen
analysis to `s = 0`.  Thus a future verified `(4,4,4,4)` UNSAT certificate
would leave 61 arithmetic-survivor zero-layer partitions to resolve.

### Phase-zero cube is a gauge contradiction

The three-way anchor split at `tau[(0,0),2]` is exhaustive, but its phase-zero
cube contains no substantive H-lift case.  The per-row gauge already fixes
`tau[(0,0),1] = 0`, while the Stage-1 row-residue law requires the three
linked phases to be pairwise distinct modulo three.  Adding
`tau[(0,0),2] = 0` therefore gives an immediate unit-propagation
contradiction.  The two substantive orientation cubes are phases one and
two.

A second split at `tau[(1,0),2]` has the same degenerate phase-zero child
and two substantive children.  All four substantive grandchildren must be
solved and certified.  Simultaneous reflection or swapping components two
and three conjugates both anchor residues, but the required copy re-sorting
changes which physical orphan is copy zero in an assignment-dependent way;
it does not give an intra-parent `q1`/`q2` CNF isomorphism.  Swapping omitted
and used types zero and one gives a semantic bijection between the crossed
grandchildren `p1q2` and `p2q1` after regauging and canonical re-sorting, but
that map is likewise not a fixed literal permutation.  Their verdicts are
therefore a useful independent cross-check, not a replacement for either
DRAT certificate or leaf in the exhaustive phase tree.

The two recursive phase-zero children are now certified as well.  Their
exact CNF hashes are `05fd617a3bdb93059bb718c703d822ea3403ef1be5a8d0e7cfd35bfcda72ce26`
under `p1` and `d526d71b94f1c590d1cc481f1647064cf5732030e342ee165e3c60a3cbcbce98`
under `p2`.  Kissat returned UNSAT for both and `drat-trim` returned
`s VERIFIED`.  The certificate/proof SHA-256 pairs are respectively
`e29c11dcb32814ba1f4fbdbdd3f43b1fa86bdc2ae9a04a50b8d2863343c5d0de` /
`a0f3c9e95d229b187a2d40a6935900904a906a049f0511f828bd9cc99de2379e`
and
`7bd4e743923b8f06bc992694dabc5f243291c0b74d0c27dd2d87b570022332d8` /
`2e76bdc5d60825ac7964e825c8a4a9b0f5b3d693b3539b1293c7b5f591219a6c`.
These leaves again certify only the gauge contradiction; the four
phase-one/phase-two grandchildren are the substantive cases.

Splitting those grandchildren once more at `tau[(0,0),3]` does not create
two new orientations per leaf.  The same row already has first-link phase
zero and `tau[(0,0),2]=p`, so pairwise distinct residues force the only
substantive third phase to be `3-p`: phase zero and phase `p` are gauge-row
contradictions.  All eight such degenerate depth-three leaves are DRAT
certified.  For the four nonzero repeated-phase leaves `p1q1r1`, `p1q2r1`,
`p2q1r2`, and `p2q2r2`, the certificate SHA-256 values are respectively
`f2f0b17355f334b4e8cf7adc8bb15e55151598670167bbd648831349474caf72`,
`ff9080e07e6fdd8c461a0836ebfb9a17744fe40400d01b52f5517b7308b36590`,
`0031d1592211191cdf182f467895cf6a62088c202673e990eb91439a937f2bf7`,
and `2175f0a0e0b971c5684d8a7e3eb6947188175f94a05817ee9ca2c8753361fc03`.
Consequently only four depth-three leaves remain mathematically
substantive: `p1q1r2`, `p1q2r2`, `p2q1r1`, and `p2q2r1`.

Each of those four leaves is further partitioned by the residue modulo three
of the exact twelve-phase variable `tau[(0,1),2]`.  This is not an invocation
of the three-literal anchor splitter: variables 18385 through 18396 form the
exact twelve-value one-hot domain, and the three child clauses are
`{0,3,6,9}`, `{1,4,7,10}`, and `{2,5,8,11}` in phase-value notation.  The
residue splitter verifies the twelve-literal one-hot clause and all 66 exact
pair exclusions before emitting these three exhaustive children.

The residue-zero child is a row-residue contradiction in all four spaces and
is now DRAT certified.  In the leaf order above, the exact CNF hashes are
`68c2fbf1a223cca2d2c5a4b2d2d7d594da7d52a5db55d050f354d7115b01c906`,
`f3bef2c43ebbbf1e55c1379185c0273a31e2e91e334250784d5cd0d1937260ba`,
`7dd3913ee6d6c74601a8f4bf60a3f5c0f764bef1a967b6e2ba2026fe834df7d0`,
and `70549ac36b5bfadaab4a0ef3bcfd26a9a0c8e4bed9532f40f0bb084369bb7554`.
Their certificate SHA-256 values are respectively `6663731cedcf885ac336e04057d6aa716e5efa172d7c9eeb51e4bdae8c0aab39`,
`361c4b510a2b532757bdfa5bfbe2fb6940da728de4a579c23249e8f141560619`,
`44835b53e0f085e64067de213e44b846fea0ef397c17d6ea32ba3b4cff8fd182`,
and `3e0297d367564e1a9abaf8fae95044099be7188aaa63617ee50326e0532f22e9`;
all four proof reruns were independently accepted by `drat-trim`.  The eight
residue-one/residue-two children remain the substantive search frontier.

The residue children can in turn be split exhaustively into their four exact
phase values.  For `p1q1r2`, the sorted-copy and pair-injectivity constraints
make exact values 1, 10, and 11 impossible.  Fresh proof-logged reruns for
those three leaves are DRAT verified and stored self-contained on the durable
volume.  Their exact CNF hashes for `(residue,value) = (1,1), (1,10), (2,11)`
are respectively
`57c96ab68325e073c6a01c5f1ca576b2461cc03417deec052c09e9da449a3907`,
`c07389f92e8319efbb7d418ec6d9cafc312f4a184fb6dc2fa48802b542f55790`,
and `1439c4f4fc4e5ac18b63dd49f461b01de65ab4a7600772bcb9ca0b505fcf4c87`.
The certificate/proof SHA-256 pairs are
`453ce25d613c65bafe9794397cfefcdb5cca046dbf4aa572152b936efc9d0952` /
`f9a30dd0f2ed1f310e2eee8f2b313c535fb1a5f73b3bf51c702e3a080df10800`,
`39d297d9524e065a286eb8e3d3054d8adc014fa186a9b06a73bc409eebbb6c8e` /
`d8e95180e580e3a2519eaca5062b89ad76d021af42202eb613a6c26c9178b7ed`,
and `2d554cfe7092a42f4d59c5c7f2c727a3e3b837023af2b54150baa5b68371631c` /
`1037fd71287a77161c550e07d794e691e37ed96855bc9ff249abcfbc5cef4ae8`.
These are structural dead-value leaves only; the five remaining exact values
under `p1q1r2` and all unresolved leaves under the other three parents still
require independent verdicts and certificates.

This degenerate cube nevertheless has a canonical certificate for exhaustive
parent aggregation.  Its CNF SHA-256 is
`dcf242a538b09b6ac2da4b70c043d1c58a2a1bcca5b8ea78a4dd1359a1238f40`;
Kissat returned UNSAT and `drat-trim` returned `s VERIFIED`.  The canonical
certificate JSON SHA-256 is
`5c4b8f69ed121947210ebe228b928a06f71200912e73e0377ba9a07ee39df86e`.
An independently extracted original-clause core has exactly three clauses:
two from `stage1_phase_onehot_gauge_row_residues` and the cube unit, with no
clauses from any graph-theoretic encoder family.  Thus this certificate must
not be interpreted as evidence for a mathematical obstruction beyond the
gauge normalization.

For every corrected `(4,4,4,4)` Stage-1 witness, the graph
`A = D ∪ S` on the 16 orphan `C12` blocks has the same spectrum.  This is
not an experimental invariance: it follows from a four-column Gram matrix in
each Fourier character of `Z/12`.

Write `tau[o,e]` for the link phase from orphan block `o` to used component
`e`.  At a twelfth root of unity `z`, let `v_e` be the 16-vector whose
`o`-entry is `z^tau[o,e]` when `o` links to `e`, and zero otherwise.  The
Fourier block of the service graph is

```
S_z = sum_e v_e v_e* - 3 I.
```

Indeed, its off-diagonal `(o,p)` entry is the sum of
`z^(tau[o,e]-tau[p,e])` over shared used components, exactly the service
shifts, while the subtracted diagonal removes the three self-incidences.
Adding the orphan-cycle defect graph gives

```
A_z = (z + z^-1 - 3) I + V V*,   V = [v_0 v_1 v_2 v_3].
```

The Stage-1 pair-profile law says that, for each distinct used-component
pair `e,f`, the eight co-linked orphans have phase differences
`tau[o,e]-tau[o,f]` equal to the eight residues not divisible by three,
once each.  Consequently the `4 × 4` Gram matrix `V*V` has diagonal 12 and
constant off-diagonal

```
C(z) = sum_{0 <= r < 12, 3 does not divide r} z^r.
```

Its eigenvalues are `12-C(z)` with multiplicity three and `12+3C(z)` with
multiplicity one.  The remaining twelve eigenvalues of `V V*` are zero.
For `z^12=1`,

```
C(1) = 8,
C(z) = -4  if z != 1 and z^3 = 1,
C(z) = 0   otherwise.
```

Combining the twelve characters yields the exact, phase-independent
spectrum

```
35^1, 12^6, 10^8, 9^8, (9+sqrt(3))^8, (9-sqrt(3))^8,
7^4, 3^3, (-1)^12, (-2)^24, (-3)^24, (-4)^26, (-5)^12,
(-3+sqrt(3))^24, (-3-sqrt(3))^24.
```

For an H-lift, the common-neighbor equations give
`H^2 = 12 I + J - A`.  Hence the spectrum of `H^2` is fixed as well: 169
on the all-ones line and, on its orthogonal complement,
`12 - lambda(A)`.  The rational H-eigenvalue sign imbalances

```
a = mult_H(4) - mult_H(-4),
b = mult_H(3) - mult_H(-3)
```

are forced by `tr(H)=0` and `tr(H^3)=6*328=1968` to `a=-4`, `b=1`.
This is consistent, so the first and third moments alone are not the final
contradiction, but all further analytic work may start from this fixed
factorization rather than quantify over the service phases.

## Cube-root kernel and the omitted-type quotient

At either nontrivial cube root `z`, the four Fourier columns `f_e` satisfy
`sum_e f_e = 0` and span the three-dimensional `A`-eigenspace at 12.
Since `H` is symmetric and `H^2` vanishes there, `H f_e = 0`.  For every
vertex and used component `e`, its H-neighbors in blocks linked to `e`
therefore split equally among the three colors `x+tau[o,e] mod 3`.

Let `r_e(v)` count H-neighbors of `v` in the 48 vertices whose blocks omit
`e`.  Since H has degree 13, the kernel balance says

```
r_e(v) = 1 mod 3,        sum_e r_e(v) = 13.
```

The possible unordered profiles are initially
`[10,1,1,1]`, `[7,4,1,1]`, and `[4,4,4,1]`.  They are separated by an
exact cherry count.  Inside one omitted-type class there are 48 defect
edges and `6*3*12 = 216` service edges.  Thus exactly

```
binom(48,2) - 264 = 864
```

pairs have one H-common-neighbor, and
`sum_v binom(r_e(v),2) = 864`.  Summing over the four types gives 3456.
The three profiles contribute respectively 45, 27, and 18 to the local
four-type cherry sum; because `3456 = 192*18`, equality forces
`[4,4,4,1]` at every vertex.  For each `e`, exactly 48 vertices have
`r_e(v)=1`; call that sparse fiber `X_e`.

Write `O_e` for the omitted-type classes and identify a class with its
indicator vector.  The profile law is

```
H O_e = 4*1 - 3*X_e.
```

The service construction also gives `A O_e = 8*1 + 3*O_e`.  Applying
`H^2 = 12I+J-A` to `O_e` then gives the dual identity

```
H X_e = 4*1 - 3*O_e.
```

Both balanced four-partitions therefore have the same three-dimensional
contrast space, namely the entire `H^2=9` eigenspace.  Equality of the
indicator spaces implies `X_e = O_{pi(e)}` for a permutation `pi`.
Symmetry of H makes `pi` an involution.  The fixed H-sign split at squared
eigenvalue 9 is `(+3)^2,(-3)^1`, so on contrasts `-3 P_pi` has precisely
those signs.  Hence `pi` is a product of two disjoint transpositions.

After relabeling the four types, `pi=(0 1)(2 3)` and H has the exact
equitable quotient

```
Q = 4 J_4 - 3 P_pi.
```

In particular, every vertex has one neighbor in its paired omitted class
and four neighbors in each of the other three classes.  The edges between
each paired pair of 48-vertex classes form a perfect matching.

## Immediate paired-class geometry

Let the paired classes be `(O_0,O_1)` and `(O_2,O_3)`.  The quotient gives
the following exact regular pieces of H:

* each induced graph `H[O_a]` is 4-regular on 48 vertices;
* `H[O_0,O_1]` and `H[O_2,O_3]` are perfect matchings;
* each of the other four bipartite class-pair graphs is 4-regular on both
  sides.

All these graphs inherit C4-freeness from H.  Identify two paired classes
through their perfect matching `m`.  Their two internal 4-regular edge sets
are disjoint under this identification: if both `uv` and `m(u)m(v)` were
edges, those edges together with the two matching edges would form a C4.

Moreover, a triangle containing a paired matching edge cannot have its
third vertex in either endpoint class.  A vertex in one endpoint class has
only its matched neighbor in the other.  Thus every non-triangle-free
matching edge has its unique common neighbor in one of the two classes of
the other paired pair.  Equivalently, matching edges outside the service
graph are in bijection with triangles whose type pattern uses one vertex
from a paired pair and one vertex from the other pair.

## Fixed mixed overlap moments

Because `A = 12I + J - H^2`, the two matrices commute and their mixed
moments are fixed by the same sign split.  On the all-ones line their
eigenvalues are `(13,35)`.  On the rational `H=±4` sector, `A=-4` and the
sum of the H-eigenvalues is `4*(-4)=-16`; on the `H=±3` sector, `A=3` and
the H-eigenvalue sum is `3*1=3`.  All irrational sign-paired sectors cancel
from expressions odd in H.  Therefore

```
tr(H A)   = 13*35   + (-16)*(-4) + 3*3    = 528,
tr(H A^2) = 13*35^2 + (-16)*16   + 3*3^2  = 15696.
```

The first identity says that exactly `528/2 = 264` H-edges are also
zero-common-neighbor A-edges.  Equivalently, the other `1248-264=984`
H-edges lie in their unique triangles, giving `984/3=328` triangles as
required by `tr(H^3)=1968`.  The second identity is the common-A-neighbor
ledger

```
sum_{uv in E(H)} |N_A(u) intersect N_A(v)| = 7848.
```

These totals are service-independent and can be decomposed across the four
paired quotient classes, in particular separating the 96 paired matching
edges from the four internal and four unpaired bipartite pieces.

More generally, every mixed moment with one odd `H` factor is fixed:

```
tr(H A^k) = 13*35^k - 16*(-4)^k + 3*3^k       (k >= 0).
```

Indeed, the irrational H-sign pairs still cancel, while the principal,
`±4`, and `±3` sectors have the same three H-sums `13`, `-16`, and `3`.
For `k=0,...,8` the exact values are

```
0, 528, 15696, 558480, 19504272, 682801488,
23897389776, 836411128080, 29274379049232.
```

For each `k >= 1`, half of this trace is the sum over unordered H-edges of
the number of A-walks of length `k` joining their endpoints.  Thus the
overlap and common-A-neighbor ledgers are merely the first two members of a
full service-independent walk-moment sequence.

## Same-block common-neighbor profile

The exact-cover residue law also fixes `A^2` pointwise inside every orphan
`C12` block.  For two vertices at cyclic distance `d=1,...,6`,

```
(A^2)_{x,x+d} = 3, 4, 6, 3, 3, 6.
```

For each of the three unordered pairs among the block's linked components,
the other seven co-linked blocks contain the exact-cover profile differences.
At distances `1,...,6` this contributes respectively

```
1, 1, 2, 1, 1, 2
```

service-common neighbors per component pair.  At distance six the two
component orientations land in the same target block but at two distinct
vertices, so both count.  Summing the three component pairs gives
`(3,3,6,3,3,6)`.  The two defect-cycle neighborhoods have one common
vertex exactly at cyclic distance two, producing `(3,4,6,3,3,6)`.

This identity is independent of all Stage-1 phases.  In particular, the two
sparse centers forced into one block have an explicit distance-sensitive
A-common-neighbor count, which can now be combined with the entrywise
`HA=AH` mixed-neighbor balance.

## Mixed-count Frobenius ledger

The square identity also fixes the second moment of the entrywise mixed
counts.  Since `H` and `A` commute and are symmetric, `HA` is symmetric and

```
tr((HA)^2) = sum_{x,z} (HA)_{x,z}^2
           = sum_{x,z} |N_H(x) intersect N_A(z)|^2.
```

Using `H^2 = 12I + J - A`, A-regularity of degree 35, and the exact
service spectrum,

```
tr(A^2)   = 192*35 = 6720,
tr(J A^2) = 192*35^2 = 235200,
tr(A^3)   = 74880,
tr(H^2 A^2) = 12*6720 + 235200 - 74880 = 240960.
```

Thus the mixed-count matrix has row sum `13*35 = 455`, total squared mass
`240960`, and diagonal equal to the local `H intersect A` degree.  At least
24 diagonal entries are one by the global overlap/parity ledger, supplying
a quantitative constraint on the sparse rows containing the two forced
same-block centers.

## Same-block cubic and mixed-row inner products

The Fourier/Gram calculation fixes one further pointwise profile.  Put
`K=VV*` and `alpha=z+z^-1-3`, so `A_z=alpha I+K`.  At a fixed orphan row,

```
(A_z^3)_{oo} = alpha^3 + 9 alpha^2
               + 3 alpha (K^2)_{oo} + (K^3)_{oo}.
```

The three Gram cases `C(z)=8,-4,0` give

```
((K^2)_{oo}, (K^3)_{oo}) = (84,2928), (48,768), (36,432),
```

respectively.  In the cube-root case, the three row phases sum to zero;
in the generic case the Gram matrix is `12I`; and at `z=1` the row is three
ones.  Exact inverse Fourier transform therefore gives diagonal value 390
and the same-block off-diagonal profile

```
(A^3)_{x,x+d} = 264, 180, 229, 180, 180, 228   (d=1,...,6).
```

This is phase-independent, not a sampled-witness observation.  Now set
`B=HA=AH`.  From `H^2=12I+J-A` and `JA^2=35^2 J`,

```
B^2 = H^2 A^2 = 12 A^2 + 35^2 J - A^3.
```

Consequently the inner products of the two mixed-count rows belonging to
same-block vertices at cyclic distance `d=1,...,6` are exactly

```
(B^2)_{x,x+d} = 997, 1093, 1068, 1081, 1081, 1069.
```

The diagonal cubic value is 390, while `(A^2)_{xx}=35`, so this also upgrades
the global Frobenius ledger to a pointwise identity:

```
sum_z B_{xz}^2 = (B^2)_{xx} = 12*35 + 35^2 - 390 = 1255
```

for every row.  Thus the two forced sparse rows both have sum 455 and squared
norm 1255.  Their squared Euclidean row-distance, at `d=1,...,6`, is

```
516, 324, 374, 348, 348, 372.
```

Equivalently, each integral row `b` has the exact shifted deviation budget

```
sum_z (b_z - 2)(b_z - 3) = 1255 - 5*455 + 6*192 = 132.
```

Every integer outside `{2,3}` contributes at least two to this nonnegative
sum.  Therefore at least `192-66=126` entries of every mixed-count row are
exactly two or three; this concentration bound is also Lean-formalized.

There is also a forced zero set.  If `H_{xz}=1`, then `B_{xz}=0`: otherwise
a summand `H_{xy}A_{yz}=1` would make `x` a common H-neighbor of the
zero-common-neighbor A-pair `(y,z)`.  Every row therefore has at least its
thirteen H-neighbor positions equal to zero.  Those zeros consume at least
`13*6=78` units of the shifted budget.  Any additional nonzero entry at
least ten would consume at least `(10-2)(10-3)=56`, contradicting
`78+56>132`.  Hence

```
0 <= B_{xz} <= 9
```

for all entries, and each row has between 13 and 22 zeros.  Both the
H-edge vanishing lemma and the budget-to-nine arithmetic cap are
Lean-formalized.

For two same-block centers, the opposite row has an exact mass on each
forced-zero support.  Indeed,

```
sum_{u in N_H(x)} B_{zu} = (B H)_{zx}
  = (H^2 A)_{zx} = 12 A_{zx} + 35 - (A^2)_{zx}.
```

At distances `1,...,6` these masses are

```
44, 31, 29, 32, 32, 29.
```

The same numbers count A-edges between `N_H(x)` and `N_H(z)`.  Each
individual H-neighborhood is A-independent, since any two of its vertices
already have their common H-neighbor `x`.  The six support-mass values are
included in the exact audit and their residue arithmetic is Lean-formalized.

Together with diagonal mixed count one at both centers, this turns their
unspecified same-block separation into six explicit integer row-ledger cases.

## Type and color masses of every mixed row

The quotient and cube-root actions also determine how each row's mass 455 is
distributed.  Let `O_e` be an omitted-type indicator, `pi=(01)(23)`, and
`B=HA`.  From

```
A O_e = 8*1 + 3*O_e,       H O_e = 4*1 - 3*O_{pi(e)},
```

one obtains

```
B O_e = H A O_e = 116*1 - 9*O_{pi(e)}.
```

Thus every mixed row has type-class masses `(107,116,116,116)`, with 107
in its uniquely paired target class.  These sum to 455.

There is a finer, overlapping family of twelve constraints.  For the color
indicator `c_{e,r}` and linked-type indicator `L_e=1-O_e`, exact color balance
gives

```
H c_{e,r} = 3*1 + O_{pi(e)},       H L_e = 9*1 + 3*O_{pi(e)}.
```

Applying `H` to `A c_{e,r}=12c_{e,r}-3L_e+8*1` yields

```
B c_{e,r} = 113*1 + 3*O_{pi(e)}.
```

In particular, two centers in the same omitted type have row difference
whose sum is zero separately on all four type classes and on all twelve
component-color fibers.  These structural constraints survive the aggregate
two-row moment relaxation that otherwise admits all six distance cases.

## Fourth moment and signed service energy

The same diagonal-block calculation one power higher uses

```
(A_z^4)_{oo} = alpha^4 + 4 alpha^3 K_oo
  + 6 alpha^2 (K^2)_oo + 4 alpha (K^3)_oo + (K^4)_oo.
```

The additional `(K^4)_{oo}` values in the `C(z)=8,-4,0` cases are
`105024,12288,5184`.  Exact inverse Fourier transform gives

```
(A^4)_{x,x+d}, d=0,...,6:
10023, 7920, 7438, 7992, 7273, 7272, 7992.
```

Let `q=e_x-e_z` for the forced same-block pair and let `delta=q^T B` be its
mixed-row difference.  Since `B A B=H^2 A^3=12A^3+35^3J-A^4` and `q^T J=0`,

```
delta A delta^T = q^T (12A^3-A^4) q.
```

At cyclic distances `1,...,6` these signed service energies are exactly

```
-1182, -130, -198, -460, -462, -174.
```

Equivalently, the sums of `delta_u delta_v` over unordered A-edges are
`-591,-65,-99,-230,-231,-87`.  Unlike the aggregate row moments, this
forces a substantial sign interaction along the explicit service graph.

The same Fourier/Gram calculation continues without new phase data.  Since

```
delta A^k delta^T = q^T (12 A^(k+2) - A^(k+3)) q,
```

the complete moment rows for `k=0,...,6` at same-block distances `1,...,6`
are

```
d1: 516, -1182, 14282,  7610, 578818, 2530930, 33790878
d2: 324,  -130, 10440, 52430, 681420, 5734298, 58358040
d3: 374,  -198, 13654, 53786, 851346, 6463858, 70899854
d4: 348,  -460, 11160, 37832, 676776, 5291984, 59501760
d5: 348,  -462, 11186, 36986, 676450, 5185138, 58858110
d6: 372,  -174, 13104, 53910, 804276, 6240618, 67005144
```

In particular the even moments are exact squared norms
`||A delta||^2`, `||A^2 delta||^2`, and `||A^3 delta||^2`.  The audit derives
the required same-block profiles of every power `A^2,...,A^9` from the three
character Gram spectra, so these identities hold throughout the corrected
Stage-1 phase class rather than only for the baseline witness.

## Certified sparse defect-edge exclusion

The possibility that a degree-one overlap center uses one of its two
same-block defect neighbors is excluded uniformly over the corrected
Stage-1 phase class.  After lossless normalization of paired types, candidate
block, coordinate, and defect direction, the local symbolic CNF quantifies
over all link phases and one candidate 13-vertex H-neighborhood.  It enforces
the corrected phase laws, A-independence, paired-component 4/4/4 color
balance, and the pinned defect neighbor as the center's unique A-overlap.

The sequential-counter instance has 34,554 variables and 186,315 clauses,
with SHA-256
`32d286cb91d4a712ddc11aceb108a5853bcf3ebaab83878e6a0616515f3657ad`.
CaDiCaL returned UNSAT and its 79 MB DRAT proof was accepted by `drat-trim`
with `s VERIFIED`.  The proof SHA-256 is
`f75a9c07cb15bf24e0d48d727b190bf5683efd5ffb2cf4c68b8b3e6d41b36ba1`.
The manifest, compact certificate report, independent SAT verifier, and
durable proof provenance are preserved with the encoder.

Consequently every overlap-degree-one center has its unique triangle-free
H-neighbor outside the two defect-cycle neighbors in its orphan block.

## Certified paired-color preservation for sparse overlaps

The preceding exclusion admits a stronger uniform form.  Leave the unique
service overlap existential, and ask for the bad branch in which it either
omits the center's paired component or has a different paired-component
color from the center.  All other local conditions are unchanged: the
candidate H-neighborhood has size 13, is A-independent, and has exact 4/4/4
balance in the paired component.  No defect-neighbor pin is used.

The sequential-counter instance has 35,097 variables and 188,651 clauses,
with SHA-256
`cb059967c26519da275ed71c5718c29ab5b58c4941645e29ca6a5671ff0e8f80`.
CaDiCaL returned UNSAT, and `drat-trim` independently accepted the proof with
`s VERIFIED` after 26,673,807 resolution steps.  The proof SHA-256 is
`b6c372b4a9cbd6b934dab7b3e6f7251ff74cfee396fe7a41b83efe2b6d9bfb13`.

Thus the unique overlap of every overlap-degree-one center includes the
paired component and has the same paired color as the center.  Since either
same-block defect step changes that color modulo three, the earlier
defect-edge exclusion follows immediately.
