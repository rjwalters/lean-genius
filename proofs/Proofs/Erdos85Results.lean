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
import Proofs.Erdos85ThirtyTwo
import Proofs.Erdos85ThirtyTwoQuotient
import Proofs.Erdos85SignedSRGObstruction
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
