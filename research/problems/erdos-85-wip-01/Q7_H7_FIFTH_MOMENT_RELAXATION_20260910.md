# H7 fifth-moment relaxation: exact non-obstruction — 2026-09-10

Owner: codex-sol-3. Passed independent review1604 by codex-sol-2 (exact rational arithmetic and continuous-measure scope). This is a positive rational
measure for a continuous moment relaxation, **not an integral spectrum,
characteristic polynomial, or graph witness**.

## Tested consumer

The old H7 fifth-moment audits left the defect overlap R=tr(CD²) uncontrolled.
The [local isolation bound](Q7_LOCAL_DEFECT_OVERLAP_BOUND_20260910.md) supplies
a C4-sensitive upper bound. This test asks whether that bound makes the
first five residual moments and an integer positive-root count contradictory
in the continuous moment relaxation used by scalar polynomial bounds.

Take T=10 and R=96. These satisfy the triangle range, nonnegative even R,
R=3T+1 modulo5, and the new local upper bound R<=138. The residual targets
for orders0 through5 are

    (34,-7,203,-136,1379,-1417).

There is an exact positive measure with these moments supported on

    -11/10, -13/5, -59/20, 39/20, 9/4, 13/5, 13/4.

All seven nodes satisfy strictly
(7-sqrt21)/2 < x² < (17+sqrt21)/2. The positive and negative masses are
both17, so the aggregate sign count is an integer. Exact positive rational
weights are retained in `q7_h7_fifth_moment_measure.json`; they are not
integer multiplicities.

## Evidence

A bounded SciPy linear program selected the support from a rational grid.
The weights were then reconstructed by exact rational linear algebra.
`verify_q7_h7_fifth_moment_measure.py` independently checks them using only
Python's Fraction arithmetic: positivity, all six moments, both sign masses,
strict intervals by squaring rational inequalities, and the R bounds and
congruence. Verification uses no optimizer or floating-point tolerance.
No infeasibility result from the discovery grid is used as proof.

## Consequence and limit

This row cannot be rejected by the stated continuous first-five-moment
relaxation plus integer aggregate sign count and the local R bound. In
particular these data do not yield a uniform H7 exclusion through that
relaxation alone. The witness does not satisfy, or claim to satisfy, individual
integer eigenvalue multiplicities, a monic integral polynomial, the modular
polynomial filters, higher moments, an integral C/D pair, or graph constraints.

The local R bound remains useful and gives a separate small H5 triangle
cut. This result closes only this bounded H7 moment consumer; it is not an
H7 existence result and does not justify declaring a full spectrum survivor.
Revisit this measure only when a stronger independent condition can test it.
