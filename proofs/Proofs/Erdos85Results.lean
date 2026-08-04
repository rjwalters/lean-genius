import Proofs.Erdos85Problem14
import Proofs.Erdos85Problem21
import Proofs.Erdos85Ramsey
import Proofs.Erdos85PairedWitness
import Proofs.Erdos85TightWitness
import Proofs.Erdos85Polarity
import Proofs.Erdos85PolarityDegree
import Proofs.Erdos85PolarityFamily
import Proofs.Erdos85Relabel
import Proofs.Erdos85PrimeFamily
import Proofs.Erdos85PrimeSequence
import Proofs.Erdos85VertexDeletion
import Proofs.Erdos85IteratedDeletion
import Proofs.Erdos85ControlledDeletion
import Proofs.Erdos85ConsecutiveRamsey
import Proofs.Erdos85ProblemConflict
import Proofs.Erdos85PolarityDeletion
import Proofs.Erdos85PolarityAbsolute
import Proofs.Erdos85PolarityBand
import Proofs.Erdos85PolarityAbsoluteSetDeletion
import Proofs.Erdos85PolarityOddSecant
import Proofs.Erdos85PolarityConic
import Proofs.Erdos85PolarityEven
import Proofs.Erdos85SafeSetCounting
import Proofs.Erdos85IntersectingPairs
import Proofs.Erdos85PolarityOddSecantCount
import Proofs.Erdos85DeletePair
import Proofs.Erdos85RepairSet
import Proofs.Erdos85CompensatedRepair
import Proofs.Erdos85GadgetExtension
import Proofs.Erdos85DeleteGadget
import Proofs.Erdos85GadgetCounting
import Proofs.Erdos85CompensatedGadget
import Proofs.Erdos85GadgetMultiplicity
import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos85ReplacementGadgetObstruction
import Proofs.Erdos85DeleteOnePairObstruction
import Proofs.Erdos85BoundedReplacementObstruction
import Proofs.Erdos85ThirtyTwo
import Proofs.Erdos85ThirtyTwoQuotient
import Proofs.Erdos85SignedSRGObstruction
import Proofs.Erdos85SignedSRGSAT
import Proofs.Erdos85SignedSRGBridge
import Proofs.Erdos85LocalCycleSAT
import Proofs.Erdos85SRGLocalCycle
import Proofs.Erdos85FiniteSigningClosure
import Proofs.Erdos85CrossEdgeSwitch
import Proofs.Erdos85CrossEdgeSwitchProgram
import Proofs.Erdos85CrossEdgeSwitchCascade
import Proofs.Erdos85PolarityTwoPointCore
import Proofs.Erdos85FiniteFieldNonsquare
import Proofs.Erdos85PolaritySwitchCoordinates
import Proofs.Erdos85PolarityTangentSwitch
import Proofs.Erdos85PolarityThreePointCore
import Proofs.Erdos85PolarityThreePointPathSwitch
import Proofs.Erdos85PolarityThreePointDynamicSwitch
import Proofs.Erdos85PolarityThreePointSecondSwitch
import Proofs.Erdos85CompensatedRegular
import Proofs.Erdos85DistanceLayers
import Proofs.Erdos85MooreFriendship
import Proofs.Erdos85OddFirstOrderSpectral
import Proofs.Erdos85EvenFirstOrderAntipodal
import Proofs.Erdos85EvenAntipodalQuotient
import Proofs.Erdos85SecondOrderStructure
import Proofs.Erdos85SecondOrderEvenDefect
import Proofs.Erdos85CycleResolvent
import Proofs.Erdos85MinimalWitness
import Proofs.Erdos85TightCore
import Proofs.Erdos85LayeredWitness
import Proofs.Erdos85NonneighborReduction
import Proofs.Erdos85OneDefectCore

/-!
# Headline results for Erdős Problem 85

This module collects the publication-facing statements proved by the detailed
development.  The main problem—eventual monotonicity of `minDegreeForC4`—remains
open.  We provide its exact Ramsey and witness-extension reformulations, a
complete checked table through order 21, one- and two-vertex attachment theory,
and the finite-field polarity construction underlying the classical infinite
family.  In particular, for every finite field of order `q`, the development
proves `minDegreeForC4 (q² + q + 1) = q + 1`.
Chevalley--Warning and deletion of an absolute point strengthen this to the
consecutive pair `f(q²+q) = f(q²+q+1) = q+1`.
The absolute locus is shown to have exactly `q+1` points in every
characteristic.  In odd characteristic, deleting any `k ≤ q+1` absolute
points traps the threshold between `q` and `q+1`; in characteristic two,
deleting the absolute line together with its nucleus gives the additional
exact value `f(q²-1) = q+1`.
This also verifies the monotonicity step immediately preceding every such
characteristic-two value.
The resulting `q`-regular core has no common-neighbor-independent attachment
set of size `q`; its common-neighbor conflict graph has independence number
exactly `q-1`.  Thus this natural
witness cannot settle the following monotonicity step by direct attachment.
In odd characteristic, the degree-`q-1` vertices after deleting the full
absolute conic are classified by unordered absolute pairs, so there are
exactly `choose (q+1) 2` of them.  Double-counting point-conic incidences
shows there are no tangent nonabsolute points: the core is exactly biregular,
and its other `q² - choose (q+1) 2` vertices all have degree `q+1`.
A disjoint-neighborhood counting bound then
proves that no common-neighbor-independent selector can cover all these
defects; direct one-vertex repair of the full deleted-conic core is impossible.
More sharply, the defect-to-absolute-pair map and Erdős--Ko--Rado show that a
safe selector consisting of defects has cardinality at most `q`; the bound is
sharp, realized by all defect pairs through one fixed absolute point.
Consequently, any direct cover of every defect by independently safe
attachment selectors indexed by `I` satisfies `q+1 ≤ 2|I|`; this witness
cannot be repaired by a bounded number of such new vertices as `q` grows.
The rank-two Kneser cover argument sharpens this to `q-1 ≤ |I|`.
This is exact: one triangle selector on three absolute points together with
one star selector for each remaining absolute point gives `q-1` safe
selectors covering every defect.
Finally, a universal compensated surgery is now available: delete every old
edge between the neighborhoods of two vertices `x,w`, then add `xw`.  If the
old graph is `C₄`-free, the switched graph is still `C₄`-free.  This reduces
the new two-absolute-point construction to degree bookkeeping and explicit
finite-geometry incidence counts.  When the endpoints are nonadjacent with
disjoint neighborhoods, every vertex loses at most one cross edge; an abstract
completion theorem repairs a unique one-unit defect provided all other
vertices retain the target degree after cross deletion.
For the polarity graph with two distinct absolute points deleted, the unique
degree-`q-1` vertex is now identified exactly: it is their unique nonabsolute
common neighbor.  Hence the proposed switch has a canonical left endpoint;
only the choice and incidence analysis of its right endpoint remain.
The required field-theoretic existence input is also checked independently:
for every nonzero `a` in a finite field of odd characteristic, `t²-a` is a
nonsquare for some `t`; in particular some nonzero `t` makes `1+t²` a
nonsquare.  Representative rescaling reduces the coordinate switch condition
to precisely this lemma.
The normalized coordinate calculation is checked as well: every parametrized
opposite endpoint of a deleted cross edge has nonzero self-dot-product under
that nonsquare condition.  This candidate nevertheless has a unique
common-neighborhood vertex of cross-edge loss two, so it does not by itself
complete the repair.  The surviving route is instead to choose the right
endpoint to be a third absolute point: tangency removes that double-loss
configuration.  The tangent construction is now complete: for every finite
field of odd characteristic and order `q`, it gives a `C₄`-free graph of
minimum degree `q` on `q²+q-1` vertices and proves the new exact value
`f(q²+q-1)=q+1`.  Together with the preceding polarity values this gives an
exact three-order plateau at `q²+q-1`, `q²+q`, and `q²+q+1`.
The next deletion already exposes a qualitative obstruction: a single
cross-edge switch can raise degrees only at its two endpoints, so no such
switch can repair a graph with three distinct sub-target vertices.  The
three-absolute-point core and each of its pair-pole defects are now defined;
each pair pole still has degree `q-1` after the third deletion.
Arbitrary finite switch programs are also now formalized and remain
`C₄`-free.  A vertex never named as an endpoint can only lose degree over the
whole program, so every initial defect must be named; a program of length `m`
can cover at most `2m` distinct initial defects.  Thus the three-point core
requires at least two switches before incidence losses are even considered.
Moreover, deleting one incident cross edge at an untouched target-tight vertex
makes it a new strict defect.  Any successful continuation must use that
vertex as a later endpoint, giving a formal repair-cascade obstruction.
The cascade criterion is sharp in slack form: whenever cross-edge loss exceeds
a vertex's current degree surplus above the target, every successful
continuation must name that vertex as a later endpoint.
In the three-point core, exactly `q-2` absolute points survive and all of them
are target-tight of degree exactly `q`; this canonical tight set is now
packaged explicitly for subsequent loss-incidence arguments.
The center pair pole's neighborhood is classified further: exactly `q-2`
surviving neighbors avoid the third deleted absolute point, and every member
of this family has full degree `q+1` in the three-point core.
Each clean center neighbor is now proved to have exactly one common neighbor
inside the core with the first outer pair pole, supplying one of the two
cross-edge losses in the static path obstruction.
Both arms and their distinctness are now checked.  The simultaneous pair-pole
path drops every one of the `q-2` clean center neighbors from degree `q+1` to
at most `q-1`, so this natural multi-edge repair provably creates a growing
new defect family.
In particular, the switched graph has minimum degree at most `q-1`; the
static pair-pole path is formally ruled out as a degree-`q` witness.
By contrast, one dynamic switch between two pair poles is completely clean:
it repairs those two defects to degree `q`, creates no new sub-target vertex,
and leaves the third pair pole as the unique degree-`q-1` vertex.
More generally, controlled deletion and finite-gadget attachment are now
composed into an exact delete-`k`/add-`m` surgery.  Taking `m=k+1` gives a
uniform order-raising criterion strictly broader than canonical
delete-one/add-pair repair, with exact compensation for every deleted and
newly attached incidence.
Global mixed-budget counting nevertheless limits this generalization: an
`m`-vertex compatible gadget attached to a degree-`d` old graph forces
`d²-(m-1)² ≤ n` when `m-1 ≤ d`.  At order `d(d-1)+1`, any such gadget
must satisfy `(m-1)² ≥ d-1`; bounded attachment gadgets cannot by themselves
settle eventual witness extension near the Moore-layer scale.
The remaining escape route is now integrated exactly: after deleting old
vertices, one may delete arbitrary additional survivor edges before attaching
the replacement gadget.  The pure bound then gains precisely the
attachment-weighted old-degree loss `L`.  At Moore-layer order it forces
`m(d-1-(m-1)²) ≤ L`, so every unit of gadget-size deficit must be paid by
old-edge losses at attachment vertices and subsequently compensated.
Such compensation cannot be concentrated arbitrarily.  If `t_x` is the
number of selectors containing `x`, compatibility gives
`Σ_x choose(t_x,2) ≤ choose(m,2)`.  At a degree-`d` tight vertex, incident
old-edge loss `ℓ_x` forces `t_x ≥ ℓ_x`; hence the number of tight vertices
with loss at least `q` times `choose(q,2)` is at most `choose(m,2)`.
Compatibility also makes the gadget graph itself `C₄`-free.  Cherry counting
and Cauchy--Schwarz on its degree sequence strengthen the pure gadget-size
obstruction at Moore-layer order to `(d-m)² ≤ 2(m-1)`.  Thus a compatible
replacement gadget must have `m=d-O(√d)` vertices.  With compensated old-edge
deletion the corresponding balance is
`md² ≤ nm+2m(m-1)+L`, quantifying the large loss required to use a smaller
gadget.
For the actual order-raising delete-`k`/add-`k+1` surgery, total survivor loss
includes both neighbors in the deleted set and additional deleted survivor
edges.  At Moore-layer order this directly forces `(k+1)(d-1-k)` to be at
most the attachment-weighted total replacement loss.  The selector-pair
bound applies to this total loss as well, limiting the number of original
tight survivors with loss at least any prescribed `q`.
Specializing to delete one vertex with no additional survivor-edge deletion,
the weighted loss is at most `d+1`, whereas Moore-order replacement requires
at least `2(d-2)`.  Hence for every `d≥6`, no arbitrary compatible
delete-one/add-two replacement exists at a tight degree-`d` vertex of any
minimum-degree-at-least-`d` graph on `d(d-1)+1` vertices, regardless of the
two selector choices.  Consequently every exact-minimum-degree-`d` graph at
this order has a vertex at which all such replacements fail; regularity is
not required.
More generally, deletion-only delete-`k`/add-`k+1` replacement is impossible
whenever `(k+1)² + k*choose(k+1,2) < d`.  Hence every fixed-size replacement
scheme of this form fails for all sufficiently large target degree provided
the deleted vertices are tight; the rest of the graph need not be regular.
Thus `k` must grow with `d`, the deletion set must include higher-degree
vertices, or additional survivor-edge surgery must be essential.
The higher-degree escape is quantitative in complete generality: every
successful deletion-only replacement in a minimum-degree-`d` Moore-layer
graph forces the deleted-set degree surplus
`Σ_{x∈D}(degree(x)-d)` to be at least
`d-((k+1)²+k*choose(k+1,2))`.
Above this polynomial threshold, every successful deleted set must therefore
contain a vertex strictly above degree `d`.  Edge-minimal normalization makes
these high vertices independent and, by direct incidence counting, strictly
less numerous than the tight vertices.  Thus more than half of every
normalized witness is tight, and every deletion set drawn wholly from that
majority is ruled out for fixed sufficiently large `d`.
At Moore-layer order the C4-free cherry-packing inequality sharpens this:
the above-minimum layer has size strictly below `2n/5`, so the tight layer has
size strictly above `3n/5`.  Tight deletion sets therefore exist for every
`k` with `5k≤3n`.
More decisively, the asymmetric Moore bound centered at each vertex proves
full rigidity: every C4-free graph with minimum degree at least `d≥2` and
exact order `d(d-1)+1` is `d`-regular.  Hence the high-degree layer is in fact
empty for a hypothetical witness at this order.  Equality accounting goes
further: every adjacent pair must have one common neighbor and no vertex lies
beyond distance two, so every distinct pair has exactly one common neighbor.
The graph would be a regular friendship graph.  The axiom-free Friendship
Theorem forces its degree to be `2`; consequently no C4-free
minimum-degree-`d` graph of order `d(d-1)+1` exists for any `d≥3`.
Equivalently, every nonempty C4-free graph of minimum degree at least `d≥3`
has at least `d(d-1)+2` vertices, and
`f(d(d-1)+1)≤d`.  Thus the natural-witness versions of the replacement no-go
at exact Moore equality are vacuous; the non-vacuous output is the strict
Moore bound itself and the more general replacement inequalities away from
equality.
The same asymmetric estimate is stable on a full near-Moore band: below
`(d+1)(d-1)+1=d²`, every C4-free minimum-degree-`d` graph is necessarily
`d`-regular.  At the first potentially attainable order `d(d-1)+2`, exact
accounting leaves precisely one unit of slack.  If `d` is even, every
neighborhood is a perfect matching and every center has exactly one vertex
beyond distance two.  If `d` is odd, every neighborhood matching has exactly
one isolated vertex and every vertex of the graph is within distance two of
the center.  These checked templates substantially narrow the next extremal
case rather than treating Moore equality in isolation.
In the odd case, the triangle-free edges are now formally extracted as a
one-regular spanning defect graph with adjacency matrix `M`.  The checked
identities are `A²=(d-1)I+J-M`, `AM=MA`, `M²=I`, and `tr(AM)=|V|`.  Thus the
minus-space matrix `A(I-M)` formally satisfies `B³=4dB` and
`tr(B)=-|V|`.  Reducing this cubic identity modulo a prime divisor `p` of
odd `d` makes `B` nilpotent, so its trace vanishes modulo `p`.  Hence
`p∣|V|`; but `|V|=d(d-1)+2` then forces `p∣2`, contradicting oddness.
Consequently the first possible order is unconditionally excluded for odd
`d≥3`: every such C4-free graph has at least `d(d-1)+3` vertices and
`f(d(d-1)+2)≤d`.
In existence form, deletion-only repair forces
`d ≤ (k+1)²+k*choose(k+1,2) ≤ (k+1)³`.  In the fully compensated form,
the excess of `d` above this polynomial is a lower bound for the
attachment-weighted additional survivor-edge loss.  Thus fixed-size repair
requires edge modification whose cost grows linearly with `d`.
-/

namespace Erdos85

/-- The checked small-value table, packaged as a single function. -/
def minDegreeForC4SmallTable (n : ℕ) : ℕ :=
  if n ≤ 3 then n
  else if n ≤ 4 then 2
  else if n ≤ 9 then 3
  else if n ≤ 14 then 4
  else 5

/-- **Exact table through 21.**  For every nonempty graph order at most 21,
`minDegreeForC4` agrees with `minDegreeForC4SmallTable`. -/
theorem minDegreeForC4_eq_smallTable {n : ℕ} (hpos : 1 ≤ n) (hle : n ≤ 21) :
    minDegreeForC4 n = minDegreeForC4SmallTable n := by
  interval_cases n <;>
    simp [minDegreeForC4SmallTable, minDegreeForC4_eq_self_of_le_three,
      minDegreeForC4_four, minDegreeForC4_five, minDegreeForC4_six,
      minDegreeForC4_seven, minDegreeForC4_eight, minDegreeForC4_nine,
      minDegreeForC4_ten, minDegreeForC4_eleven, minDegreeForC4_twelve,
      minDegreeForC4_thirteen, minDegreeForC4_fourteen,
      minDegreeForC4_fifteen, minDegreeForC4_sixteen,
      minDegreeForC4_seventeen, minDegreeForC4_eighteen,
      minDegreeForC4_nineteen, minDegreeForC4_twenty,
      minDegreeForC4_twentyone] at *

end Erdos85
