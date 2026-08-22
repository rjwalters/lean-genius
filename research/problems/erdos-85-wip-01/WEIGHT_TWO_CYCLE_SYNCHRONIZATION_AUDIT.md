# Weight-two cycle synchronization audit

## Exact reduction

Let `C` be a weight-two second-order-defect component at binary parameter
`q`.  Then `|C| = 2q`, `A[C]` is 2-regular, and every outside vertex has a
two-point trace in `C`.

For `x in C`, inspect the `q-2` outside A-neighbors of `x`.  If an outside
trace through `x` is an internal A-edge, the corresponding cross edge uses
its unique common neighbor inside `C`.  Otherwise its unique common neighbor
lies outside `C`; those outside neighbors pair up in `A[N_A(x) outside C]`.
Consequently the number of edge-traces through `x` is even.  Away from an
internal triangle it is at most two, so it is zero or two.  Therefore every
cycle of length at least five in `A[C]` is uniformly one of:

* T-saturated: none of its edges occurs as an outside trace;
* cross-saturated: every edge occurs as one outside trace.

This recovers the known `deg_T in {0,2}` propagation in its sharpest local
form.  The proposed all-or-nothing trace lemma additionally requires all
cycles of `A[C]` to choose the same orientation.

## Reduced countermodel at a binary parameter

`q16_weight_two_cycle_sync_reduced_sat.py` constructs a satisfiable exact
component-selector model at `q=16`.  Take two orientable internal cycles

```text
A[C] = C5 disjoint-union C27.
```

Represent the `q^2-2q = 224` outside vertices by their distinct two-point
traces.  Thus the traces form a simple `(q-2)=14`-regular graph `F` on the
32 points of `C`.  The model imposes:

* degree 14 at every point of `C` (the exact component quotient degree);
* no repeated trace (simplicity, forced by C4-freeness);
* no trace pair having an internal common neighbor (the exact pair-codegree
  exclusion forced by C4-freeness);
* no C5 edge in `F` (that cycle is T-saturated);
* every C27 edge in `F` (that cycle is cross-saturated).

Z3 finds such an `F`.  It has all 224 required traces but exactly 27
edge-traces.  Since there are no internal triangles, this is strictly between
the corrected synchronization endpoints 0 and `2q = 32`.  (The earlier
uncorrected endpoint `q^2-2q` counts all outside traces, most of which must be
non-edge pairs, and is not the right maximum.)  The script then independently
checks every listed invariant against the model.

The script also realizes the next cross-resolution layer explicitly.  Treat
each edge of `F` as an outside vertex joined across the cut to its two
endpoints.  At every `x in C`, pair the incident non-edge traces and put an
outside A-edge across each pair.  Edge-traces already resolve their two
cross edges through the other endpoint in `C`; the new matching edges resolve
every remaining cross edge through exactly one outside common neighbor.
The local matchings never reuse an outside edge, because two distinct trace
pairs cannot share two endpoints.  Direct checks give outside resolution
degree zero on the 27 edge-traces and degree two on all 197 non-edge traces,
with exactly one resolver for every cross incidence.

## Verdict

Cycle synchronization does not follow from the complete component-side
selector degree, uniqueness, and internal-codegree laws, even at a relevant
parameter `q=2^4`.  This is a reduced countermodel, not a full regular
C4-free graph on `q^2` vertices, so it does not disprove the all-or-nothing
lemma itself.  It identifies the missing currency precisely: a proof must
couple traces belonging to different outside defect components, or enforce
the remaining outside-outside regularity and D-component placement.  Even
the simultaneous outside common-neighbor matchings and their induced even
degree split do not synchronize the cycles.  Further parity or packing
inside the single weight-two component cannot establish the lemma.
