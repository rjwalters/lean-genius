# B.3 maximum-load exceptional-hole selector audit

Status: computational evidence and proof decomposition, not a theorem.

## Surviving selector

For a point `p`, let `F_p = {u : p in B_u}` and

```
D_p = sum (d u) over u in F_p.
```

Restrict to points incident with an exceptional hole and choose among them a
point of maximum `D_p`.  The surviving target is:

> Some maximum-load exceptional-hole point has a reduced full-fiber price
> cover of cost strictly less than `D_p`, with denominator at most six.

The reduced mask is exactly the one consumed by
`false_of_scaledCommonPointFiberPriceCertificate`: outgoing point prices at
the five rows of `F_p`, together with incoming compensation prices at `p`.

## Evidence

- 30 independently generated outer designs passed the weaker exceptional-hole
  selector (branches 3 and 4, 15 each).
- A further 20 independently generated outer designs passed after restricting
  to maximum-load exceptional-hole points (10 per branch).
- All five tracked serious payloads pass the maximum-load restriction:

| payload | branch | max `D_p` | witness |
|---|---:|---:|---:|
| `q9_13f_counterexample.json` | 3 | 27 | `p=4`, scale 1, `26 < 27` |
| `q9_13t_counterexample.json` | 3 | 27 | `p=13`, scale 6, `161 < 162` |
| `q9_gram_fractional_gap_witness.json` | 3 | 27 | `p=18`, scale 1, `26 < 27` |
| `q9_outer_seed_b3s3_triangle_selector_counterexample.json` | 3 | 27 | `p=5`, scale 1, `26 < 27` |
| `q9_branch4_row40_interval_witness.json` | 4 | 29 | `p=19`, scale 1, `28 < 29` |

The fresh generator is not a stable fixture generator across Python processes:
model-construction ordering varies, so seed labels must not be cited as durable
witness identifiers.

For branch 3 there is a further empirical horn.  When the two exceptional
triples intersect, their unique shared point was integrally strict in every
stored fresh example; the serious payloads and durable triangle-selector
counterexample instead have disjoint holes.  The option
`q9_hole_fiber_negation_smt.py --branch 3 --shared-hole-point-only` forces the
intersecting case and asserts the partial-mass negation only at the shared
fiber.  Even with `--residual-type-ledger`, the seed-free instance remained
`UNKNOWN` after 120 seconds.  This is a well-scoped candidate horn, not yet a
solver certificate or proof.

The kernel theorem
`squareOrderNine_threeHigh_secondProfile_exceptional_unmarked_exact_center`
now proves the missing exceptional-row equation.  The probe option
`--exact-hole-partition` imposes it literally on each selected partial mass:
the residual block multiplicity at `q` is zero on the hole's U1-core support
and one off that support.  Fixed `13f`/hole 24 is `UNSAT` in 0.3 seconds, but
the unrestricted one-hole branch-3 instance with both the exact partition and
residual type ledger remains `UNKNOWN` after 120 seconds.  The theorem is now
consumed faithfully; solver search, not omission of (13aj), is the remaining
computational limitation.

The formal exceptional-cardinality package further gives exactly six
residual rows per hole, split into three marked-pair and three ordinary-triple
centers.  `q9_exceptional_hole_sixpack_sat.py --hole-reciprocity` couples the
two branch-3 six-packs by symmetric hole-to-hole adjacency; the resulting
outer system is still `SAT` in 9.6 seconds.  The stronger
`--hole-pair-reciprocity` mode couples both holes to all 21 marked-pair rows;
that sharply scoped system is `UNKNOWN` after 120 seconds.  Thus local
six-packs plus hole reciprocity are insufficient, while the first unresolved
agreement boundary is symmetry against the pair rows.

The proved cross-hole C4 law says the two holes share at most one selected
marked-pair center.  `--hole-pair-choice-overlap-cap` adds this constraint.
It is still locally `SAT` in 1.8 seconds, sharply: the witness holes intersect
in one U1 point and agree in exactly one marked support.  Even the targeted
intersecting-hole negation with one shared relation, both exact partitions,
and residual type ledgers remains `UNKNOWN` after 120 seconds.  Thus the cap
is real new structure but does not by itself yield a solver terminal.

The stronger proved cap bounds the intersection of the two full six-row
residual packs by one.  `--hole-full-pack-overlap-cap` consumes it; the local
system remains `SAT` in 1.9 seconds.  Since both residual block unions have
cardinality 15 inside 24 points, their point-set intersection has cardinality
at least six.  Such a point is covered uniquely by a residual neighbor of
each hole, making it a natural double-saturation price candidate.  This
selector passes 9 of 10 independent exact-sixpack models but is refuted by
the tenth: its cover intersection has ten points and none has a strict scaled
cover through denominator six.  Therefore the 15/9 overlap arithmetic plus
the full-pack cap still needs exceptional-to-pair/full-relation agreement.

A joint two-point price survives that counterexample.  For distinct points
`p,q` in the intersection of the two 15-point residual covers, put row price
`1_{F_p} + 1_{F_q}`; overlap rows therefore carry multiplicity two.  In
branch 3 its exact degree target is `D_p + D_q = 54`.  The dedicated exact
probe `q9_joint_overlap_fiber_price_probe.py` restricts point prices to
outgoing coordinates at rows in `F_p union F_q` and incoming coordinates at
`p` or `q`, then reconstructs and verifies its MILP output in integer
arithmetic.  It found a strict scaled joint cover in all ten independent
exact-two-sixpack/full-pack-cap models.  Witness scales were at most six and
costs were respectively `53/54`, `53/54`, `323/324`, `106/108`, `106/108`,
`53/54`, `53/54`, `53/54`, `107/108`, and `215/216`.  A fresh standalone
three-model run also passed at scale one with `53 < 54` in every model.  The
banked theorem `false_of_scaledTwoUnitSupportsPointPriceCertificate` is the
literal actual-relation consumer for these integer certificates.  This is
the strongest surviving branch-3 selector, but remains finite evidence until
existence of the joint cover is proved uniformly.

The joint effect is not merely the sum of two individually strict fibers.
The probe's `--genuine-only` mode computes exact primal and dual optima for
every overlap-point single fiber, then excludes every pair having a strict
single member.  A fresh exact model still has a joint witness at `p=9,q=21`:
its denominator-two cost is `107 < 108`, while the separate exact optima are
`27` and `136/5`, both certified non-strict by matching rational dual lower
bounds.  The fibers share exceptional row 22, but the joint certificate uses
36 units on incoming `p,q` coordinates and 71 on outgoing fiber-row
coordinates, with weights through four.  Thus the tempting construction
"merge two tight 27-covers at their shared hole and save one unit" is too
simple; the uniform proof must capture a genuinely joint covering or Hall
deficiency.

The exact continuous optimum in that genuine model is `747/14 < 54`.
`--details` now reconstructs both the primal point prices and the LP-dual
eligible-edge packing as rationals and checks feasibility and equality of
their objectives.  The matching dual has 96 nonzero edges and denominators
through fourteen, so the optimum is not explained by a tiny supported Hall
witness.  The denominator-two integer cover is a slightly weaker but much
cleaner `107/2`; a uniform explicit cover construction or an argument using
integrality of the actual residual relation may be more promising than
formalizing the full LP optimum.

The first cross-row retention step also survives.  Adding the exact residual
complement partitions for all eight normalized diagonal triple rows leaves
the branch-3 system SAT and the joint selector passed three independent
strengthened models, at scale one with costs `53`, `52`, and `53` below 54.
The probe exposes this as `--diagonal-rows`.  Imposing both diagonal rows and
all rows of the other two regular triple classes remained `UNKNOWN` after
120 seconds, rather than producing a countermodel or an infeasibility
certificate.  Thus diagonal agreement alone does not explain strictness;
the first unresolved structural boundary is simultaneous agreement across
all triple-center rows.

Per-class staging shows why the combined search is hard rather than
immediately contradictory.  `q9_exceptional_hole_sixpack_sat.py
--regular-class 1` (and symmetrically class 2) can impose just one
non-diagonal regular class.  Ten independently generated exact-hole outers
all failed this extension after being fixed, each in under half a second,
so extendible outers are rare.  Nevertheless the seed-free system with one
class is SAT: with both hole reciprocity and the full-pack cap it solved in
about 98 seconds, while either cross-hole ingredient separately solved in
51--59 seconds.  The class-1 model has a scale-one joint witness `53 < 54`;
the symmetric class-2 run has a scale-two witness `107 < 108`.
Thus one full regular class sharpens the model but does not close branch 3;
the still-unresolved boundary genuinely couples both non-diagonal classes.

The staged cross-class test is sharper.  The standalone
`q9_regular_class_extension_probe.py` first generates an outer admitting one
entire regular class under both cross-hole constraints, freezes every outer
class/block/core variable, and asks for the other class.  In the class-1 to
class-2 direction the source solved SAT in 93 seconds and the fixed extension
was UNSAT in 0.35 seconds.  Symmetrically, a class-2 source solved in 80
seconds and its class-1 extension was UNSAT in 0.33 seconds.  This is strong
evidence for a direct incompatibility between the two exact regular-class
complement partitions, not merely a sampling artifact.  It is not yet a
solver certificate or theorem: the simultaneous seed-free system remains
UNKNOWN, and other one-class source models may conceivably extend.

The fixed-target failure is row-local, not an eight-row matching artifact,
but it uses the residual row-type ledger rather than bare Gram packing.
The staged probe now independently backtracks over the exact five-neighbor
constraints for each target-class block.  On the class-1 source, target
class-2 rows `{5,12,22}`, `{6,8,18}`, and `{7,13,19}` have no permitted
exact typed pack, while its other five rows do.  On the class-2 source,
exactly target
class-1 row `{1,8,22}` is impossible and the other seven rows are feasible.
The row variables in the regular-class encoding are independent after the
outer is frozen, so these local failures explain the extension UNSAT
exactly.  This exposes a potentially stronger branch-3 closure than joint
pricing: prove that the two exceptional exact packs, their reciprocity and
full-pack C4 cap force an ordinary row in one of the two non-diagonal regular
classes to lack an exact five-neighbor pack with the proved triple/pair
support subdegrees.  The distinction is essential: for bad row `{1,8,22}`,
the unrestricted pairwise-disjoint maximum remains five, but enforcing at
most one pair row from each marked support lowers the maximum to four.
Thus this is not a bare `IsLocalGramPacking` obstruction.  An actual residual
relation together with the exact row-type ledger supplies the typed pack at
every row, so that uniform lemma would contradict the branch directly.
Blocking the first complete outer assignment found a distinct class-2
source whose bad target rows are `{4,14,17}` and `{5,11,22}`; the next
blocked searches were `UNKNOWN` at 154--300 seconds.  Thus the bad-row
identity varies, while existence of a typed-deficient opposite-class row
persists across the three one-class sources obtained so far.

The first cross-hole hypothesis split gives a necessary ingredient.  Both
regular classes together with both exact exceptional packs and the full-pack
C4 overlap cap, but without hole reciprocity, are SAT (17 seconds).  Hence
the cap alone cannot force the typed-deficient regular row.  The corresponding
systems with neither cross-hole constraint and with reciprocity alone were
both `UNKNOWN` after 180 seconds; the full reciprocity-plus-cap system remains
`UNKNOWN` as before.  Any uniform cross-class contradiction must therefore
spend hole reciprocity, possibly in essential combination with the cap.

**Retraction of the cross-class incompatibility target.**  A staged solve
starting from the cap-only two-class model freezes its complete outer design
and then restores hole reciprocity.  Both reciprocity alone and
reciprocity-plus-cap extend on that same outer in under 0.6 seconds.  Hence
the full system with both non-diagonal regular classes is SAT; its monolithic
`UNKNOWN` result was search difficulty, and the typed-deficient rows above
are features of the sampled one-class sources rather than a uniform theorem.
The joint-price route remains necessary.  The new probe option
`--stage-all-regular-classes` reproduces the full-strength model and finds
overlap points `p=7,q=19` with integer certificate `107 < 108` at scale two;
the rationally certified continuous optimum is `481/9 < 54`.  Thus all
triple-center exact partitions preserve, rather than replace, the surviving
joint selector.

That full-strength witness is not genuinely synergistic.  Re-running with
`--genuine-only` excludes every pair having an individually strict fiber;
all 21 remaining pairs fail the integer joint scan through denominator six.
The reported pair `p=7,q=19` instead uses the strict single fiber at `q=19`,
whose exact optimum is `53/2 < 27`; `p=7` is non-strict at `543/20`.
Therefore the uniform structural target may naturally split into two horns:
an overlap point with a strict single-fiber cover, or a genuinely joint pair
when every relevant single fails.  The joint two-support terminal still
subsumes both computationally, but the proof mechanisms need not be the same.
The staged all-class source is rare: attempts to obtain independent sources
at solver seeds 1 and 2 remained `UNKNOWN` after 120 and 180 seconds, so the
strict-single horn currently has one full-strength regression rather than a
widened corpus.

The genuine horn really fails on that full-strength model; this is not a
denominator-six artifact.  `--scan-exact-joint-optima` rationally certifies
primal and dual optima for all 21 pairs of non-strict points.  Every optimum
is strictly above 54.  The smallest is `50668/935 = 54 + 178/935` at pair
`(4,7)`; the next is `2389/44 = 54 + 13/44`, and the largest is
`11674/209 = 54 + 388/209`.  Thus the two horns are empirically exclusive
in both directions: this full model needs its strict point `19`, whereas the
stored seed-5 model below has no strict point and needs genuine joint synergy.

The genuine-joint horn is indispensable already at exact-hole scope.  Seed
5 reproducibly has eight overlap points and no strict single fiber.  Their
exact optima (with matching rational dual lower bounds) are `649/24`,
`677/25`, `27`, `28`, `958/35`, `3955/143`, `113/4`, and `28`, all at least
27.  Nevertheless `p=1,q=9` has an integer scale-two joint certificate
`107 < 108`.  The same seed reproduced across separate Python processes,
replacing the earlier nondurable 9-of-10 observation with a named hard
regression.  Thus no proof may collapse the disjunction to strict-single
existence before deriving additional full relation agreement.
The complete outer is stored as
`q9_joint_no_strict_overlap_counterexample.json`; the joint probe's
`--payload` mode rechecks all eight exact single optima and the scale-two
joint certificate without regenerating a Z3 model.

The exact uncrossing-gain matrix further localizes the hard horn.  Only three
of its 28 pairs have joint optimum below 54, and every one contains point 9,
the unique tight single fiber with optimum exactly 27.  For the best pair
`(1,9)`, the two single optima sum to `1352/25 = 54.08`, the joint optimum is
`160/3`, and the uncrossing gain is `56/75`, easily exceeding the single
excess `2/25`.  Pairs `(9,11)` and `(0,9)` have target gaps `17/64` and
`1/11`.  The sum of target gaps over all 28 pairs is negative, so raw pair
averaging cannot prove existence.  A sharper candidate is conditional:
absence of every strict single should force a tight single, then exact-cover
collision around that tight fiber should select the genuinely strict pair.

The probe now emits `single_fiber_costs`, `tight_single_points`, and exact
`nonstrict_single_excesses` in compact mode, so this conditional statement is
falsifiable without retaining bulky LP witnesses.  Across default-generator
seeds 0 through 30, every model had a strict or tight overlap fiber.  Seed 5
was the only model with no strict overlap fiber, and it had the unique tight
point 9 described above.  Several models had strict fibers but no tight one
(seeds 11, 12, 13, 15, and 17), so tightness is plausibly forced only on the
no-strict face and must not be asserted unconditionally.  This sweep is
evidence, not a proof; in particular it contains only one no-strict model, so
the subsequent forced-collision implication still rests on one hard fixture.
In particular, all twelve added seeds 19 through 30 had at least one strict
fiber, so more random sampling did not produce a second point on the
no-strict equality face.  Further progress therefore needs an equality-case
argument or a solver constrained toward that face, not a larger ordinary seed
sweep.

The seed-5 tight optimum itself is unexpectedly integral.  Its primal uses
27 unit point prices, and a matching dual uses 25 unit-weight constraint
edges; exactly two of those edges have both endpoints in the five-row fiber,
so their demands contribute twice and the dual objective is `25 + 2 = 27`.
Thus the observed equality face has a concrete packing interpretation rather
than a delicate fractional denominator.  A viable proof target is now:
classify such saturated unit edge packings under the exceptional-cover
partition, then show that some second overlap fiber necessarily collides with
the packing in a way that saves more than its single-fiber excess.  This is
still fixture-derived, and the integral dual equality is genuinely not a
property of arbitrary tight fibers.  The probe now solves separate integer
primal and dual MILPs for every tight point.  Both tight points in seed 8
have integral cover cost 27 but maximum integral dual-packing value only 26;
their rational dual optima reach 27 fractionally.  Seed 7 has a fractional
primal basis but admits both an integral cost-27 cover and a 25-edge integral
dual of value 27.  Therefore the useful candidate is narrower still:
**absence of strict singles forces a tight fiber with an integral saturated
dual packing**.  The no-strict hypothesis cannot be discarded after the
tight point has been selected.

Seed 41 supplies the needed independent no-strict equality face and is stored
as `q9_joint_no_strict_three_tight_fixture.json`.  Its nine overlap points
have no strict single; three are tight, at points 3, 12, and 22.  Their
maximum integer dual-packing values are respectively 26, 26, and 27, so the
existential saturated-dual candidate survives while the stronger claim that
every tight point is saturated fails inside the no-strict face itself.  The
complete rational joint scan finds seven of 36 pairs below 54, and every one
contains at least one of the three tight points.  Four contain the saturated
point 22.  In particular `(3,12)` has a scale-two integer certificate
`107 < 108` and exact optimum `641/12`, while `(10,12)` has exact optimum 53.
Thus both independent no-strict fixtures exhibit the required joint horn,
and both contain a saturated tight dual, but successful collision need not be
centered only at the saturated tight point.  The uniform theorem must select
existentially across the whole tight set.

The tempting exceptional-anchor selector is false beyond those two fixtures.
The complete seed sweep found empty, singleton, and multi-point intersections
between an anchor block and the common cover-overlap, so singleton incidence
is not forced by hole reciprocity/full-pack geometry.  More decisively, the
durable payload `q9_anchor_pair_nonstrict_counterexample.json` has no strict
single anywhere and singleton anchor intersections `{8}` and `{0}`, but the
direct pair `(8,0)` has exact joint optimum `109/2 > 54`.  Thus neither
"an anchor point is saturated" nor "the two anchor points form the strict
pair" is a valid uniform equality-face lemma.  The same payload still has the
required global horn: `(3,8)` has exact optimum `2129/40 < 54` and a
scale-two integer certificate `107 < 108`; `(8,22)` and `(14,16)` are also
strict.  Point 8 is the tight anchor point, while its successful partner 3 is
a non-anchor tight point.  This restores the genuine global selection
problem: choose across the whole overlap/tight set, not only the anchors.

The next retention rung localizes the remaining relation agreement.  On the
same full two-regular-class outer, exact typed packs for all 21 pair-center
rows extend in about one second, and they coexist with hole reciprocity plus
the full-pack cap.  Thus pair rows are not locally deficient.  Fixing this
outer and adding pair-to-pair reciprocity is instead UNSAT in 1.45 seconds;
adding hole-to-pair reciprocity is UNSAT in 1.06 seconds.  These are again
fixed-outer results, not uniform contradictions: a different rare outer may
satisfy the symmetry constraints.  They identify the next actual-relation
boundary precisely as reciprocal agreement involving pair centers, while
the full triple-row geometry itself already preserves the joint price.
A seed-free source containing all pair rows and pair-to-pair reciprocity,
without the other strengthened row families, remained `UNKNOWN` after 180
seconds, so this boundary is not yet classified in either direction.

Minimum exact eligibility load does not rescue branch 3 at this local scope.
Among ten independent exact-two-sixpack/full-pack-cap models, restricting to
the global argmin of `L(p)=sum_{u in F_p} deg_H(u)` produced a strict scaled
cover in only five.  The argmin was unique in nine models, so tie-breaking is
not the issue.  The positive-special restriction may still make minimum load
useful in branch 4, but bare load descent is not a common branch-3 terminal.

The diagnostic option `--print-hole-packs` prints the selected blocks in a
SAT model.  In one hole-reciprocal branch-3 model, an exact denominator-six
scan found a strict cover at only one of the six hole incidences (scale 2,
`53 < 54`); the other five had no scaled cover through denominator six.
Hence even after imposing both exact local six-packs, no pointwise
"every hole point is strict" lemma is available.  The surviving statement is
genuinely an alternative across the two holes and their six incidences.

The original negation assigns an unrelated partial mass to every candidate,
whereas an actual residual graph is one common symmetric relation.
`--shared-relation` corrects that relaxation: it keeps one global fractional
mass, imposes mutual eligibility and all point capacities, exact degrees on
the union of the selected fibers, and both exact hole partitions.  It does
not zero edges outside the fibers.  Fixed `13f` is `UNSAT` in 0.1 seconds of
solving; the unrestricted branch-3 instance with residual type ledgers is
still `UNKNOWN` after 120 seconds.  Thus common-relation coupling is now
represented soundly, but Z3 still does not extract the six-way alternative.

For branch 4, every multi-special hole row in the six tracked models has a
strict special point even though singleton-special rows can fail.  This is a
conditional corpus horn only: global special mass six does **not** imply that
two special occurrences lie in one hole row, and existence of such a row is
still `UNKNOWN`.  The option `--multispecial-hole-row h` forces the conditional
horn and asserts the partial-mass negation only on the special fibers of row
`h`.  The tracked serious witness at row 23 is `UNSAT` in under one second of
solving; the unrestricted row-22 instance with residual type ledgers remains
`UNKNOWN` after 120 seconds.

The cleaner unconditional branch-4 candidate is global: the two punctured
regular classes miss exactly one point of each color, giving six special
occurrences without requiring hole incidence.  All tracked models have a
strict full fiber at one of these global special points.  This selector should
supersede the conditional multispecial-hole horn.  The option
`--global-special-only` encodes its partial-mass negation: the tracked serious
payload is `UNSAT` in 0.3 seconds of solving, while the unrestricted instance
with residual type ledgers remains `UNKNOWN` after 120 seconds.

## Proof decomposition exposed by the load

Every full point fiber has five rows, and each row degree is five or six, so
`D_p = 25 + H_p`, where `H_p` counts the high-degree rows containing `p`.
The outer incidence ledgers give the following observed rigid split, which
should be proved directly from their cardinality identities:

- branch 3: every exceptional-hole point has `D_p = 27`;
- branch 4: some exceptional-hole point has `D_p >= 28` (fresh samples attain
  28 or 29; the tracked branch-4 payload attains 29).

Branch 3 therefore needs the genuinely strict improvement below 27.  In
branch 4 the correct joint target is `C_p < 27 + special(p)` for some global
special point.  The point choice cannot be separated from its cover: in the
tracked branch-4 payload a maximum-load point `p=19` has target 29 but
fractional optimum about 27.4 (and least integral cover 28), so the tempting
stronger bound `C_p <= 27` at that selected point is false.  The positive
special slack still relaxes branch 4 relative to branch 3, but both require a
genuine coupled selector.

## Refuted shortcuts

- Requiring a triangle vertex, a middle-color hole point, raw averaging over
  all points, and unweighted averaging over exceptional-hole incidences all
  have durable or serious counterexamples elsewhere in the B.3 audit trail.
- The stronger claim that every point has full-fiber cover cost at most 27 is
  false.  On ten fresh outer designs, non-hole point optima reached values from
  28 through approximately 29.19, with 12--20 of the 24 points above 27 in
  each design.  Any proof must use the exceptional-hole/max-load structure.

## Remaining theorem gap

Prove, from the outer design plus the exact exceptional-hole DTB complement
partition, that a maximum-load hole point admits the bounded scaled cover.
Once its natural-number weights and positive scale are produced, the banked
actual-relation consumer closes the symmetric fractional residual relation and
hence the B.3 branch.
