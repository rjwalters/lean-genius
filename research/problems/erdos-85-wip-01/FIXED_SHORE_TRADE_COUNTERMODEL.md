# A3: fixed-shore trade interface and countermodel

The current ledger row40 closes only uniform private occupancy r=1, not
the entire pure endpoint. Row41 gives s>=2q-4. Thus that concern does not
by itself dispose of A3. However, the proposed z<=q-1 bound is false at the
abstract trade interface below, even after fixing both shore cardinalities.

Source: proofs/Proofs/Erdos85PureEndpointStrictPrivateCutGap.lean, particularly
hUbalance, hXlocal, hZrowX, hHrowX, hmoment and hpair; and
Erdos85LinearTradeCombinedShoreCollision.lean.

For a 0/1/2 occupancy profile, write Z for zero centers, H for two centers,
each of cardinality z, with weights one. Let N=q(q-1), m=q/2.
The projected constraints are:

1. U and X are disjoint point shores, each of size N/2.
2. Every Z and H row has m incidences on U.
3. Each U point has equal Z and H incidence counts.
4. Z rows have m incidences on X; H rows have m-2.
5. At each X point, Z count equals H count plus a nonnegative defect.
6. Defects sum to s=2z; X positive load plus s equals mz.
7. Every Z-H pair shares at most one point across both shores.
8. We additionally enforce same-sign pair codegree at most one.
9. The scalar profile has z zeros, z twos and N-2z ones.

These are necessary projections of an endpoint. They do not include a
symmetric self-indexed ambient adjacency matrix, all neutral-center rows,
private-point incidence, or the full-center labeling of X. No completion
theorem for these missing data is assumed or claimed.

## Explicit uniform construction

For q=2^k, k>=3, set z=q and label each sign of blocks by F_2^k, represented
by integers 0,...,q-1. Addition below is bitwise XOR.

U has q/2 points incident to the negative pair {i,i xor1} and the identical
positive pair (one point per unordered pair). It also has singleton points
(negative i, positive i xor d) for each d=2,...,m and every i.
Hence |U|=q/2+q(m-1)=N/2 and every row has degree m.

X has singleton points (negative i, positive i xor d) for d=m+1,...,q-2.
Add negative-only pair points for the two perfect matchings with XOR
differences 2 and4. These add two negative incidences per row and defect2
per point. Pad X with q/2 unused points. Its size is N/2; row degrees are
m on Z and m-2 on H, with total defect2q.

Z-H pair collisions have distinct XOR differences: {0,1} at pair points,
2,...,m at U singleton points, and m+1,...,q-2 at X singleton points.
Difference q-1 is unused. Same-sign repeated incidences have differences
1,2,4 on the negative side and1 on the positive side, each appearing once.
This proves linearity uniformly. The exact U collision mass is q(m+1),
including reuse charge q above mq; X mass is q(m-2). Total q(q-1)<q^2.
Thus the reuse charge does not exhaust pair capacity, despite exact fixed
shore sizes. z=q violates z<=q-1 for every binary q>=8.

verify_fixed_shore_trade.py verifies these constraints directly at q=8,16,32,64; result.json
records the cases and checker hash. The uniform argument is prose, not Lean.

## Endpoint implication and limit

If the proposed bound were proved under actual endpoint hypotheses, then
in the 0/1/2 profile it would give s=2z<=2q-2. Together with row41 it would
restrict s to 2q-4 or2q-2. It would not by itself exclude either endpoint
or cover arbitrary higher occupancies. A terminal consumer of those remaining
cases is a separate obligation. The present construction refutes derivation
from constraints1-9 alone; it is not an ambient C4-free graph counterexample.
Any continuation must name an additional proved incidence condition missing
from this construction before launching a larger search.

## Review and provenance

Round113 A3; independent review1532 PASS by codex-sol-3. The uniform
construction is an exact prose argument, with Python checks at four sizes;
no Lean theorem or ambient graph construction is claimed. The original
checker SHA256 is b84180fab375eb30a13be3b9901de49c66132798ee92011f4b081567dd4cf5ea.
The repository checker preserves those exact reviewed bytes and writes its
result to result.json beside itself; run a copy in a temporary directory
to keep generated evidence out of the source tree.
