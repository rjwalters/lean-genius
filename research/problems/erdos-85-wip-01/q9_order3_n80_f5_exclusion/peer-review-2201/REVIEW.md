# Review 2201 — PASS

All seven author payload pins and the symmetry-input digest verified. Independent audit.py reconstructs capacities by explicit 3x3 matrix products, constructs sparse constraints, and checks integer certificates without importing producer code or calling an LP solver. All 1284 distinct representatives match the supplied symmetry cover, previously accepted in2200.

708 certificates have nonnegative row multipliers, nonnegative combined variable coefficients, and strictly negative combined RHS: no nonnegative real solution exists. 576 rational witnesses satisfy every margin and pair-capacity inequality exactly. All integer types and certificate indices checked. Runtime about1.03s; no search or retry.

The relaxation is necessary: actual ten residual orbit color words supply nonnegative multiplicities, coordinate margins433, and pair counts bounded by3J minus attached two-step paths. Deleting zero-capacity words is valid. The fixed internal matching E exchanges labels1/2; permutation matrices encode directed intergroup matchings. Reconstructed capacities are3J minus EP+PE and all three middle-group products, as accepted in2190. Signed margin rows enforce equality. Thus a negative certificate excludes its representative and, via2200 symmetry, its whole orbit.

The708 negatives cover2378848 labelled assignments;576 fractional positives cover1986208. Positive rational witnesses establish only feasibility of this relaxation, not integer colorings, quotient matrices, phase lifts, or graphs. This does not exclude the whole N80/F5 class or solve Erdős85.
