# Simultaneous low-edge relaxation: partial exact results

Use every94 surviving assignment from2478. Each candidate remaining low-low edge has a variable in[0,1]; previously forced edges have value1. Involution equalities are omitted as a relaxation, permitting every actual inactive labeling. No particular earlier L matrix is selected.

Require each active low to have total low-degree6 and exactly one neighbor at each of its six target supports. Require each inactive low to have total low-degree7 and at most one neighbor in each non-residual-middle support. Subtract all forced contributions from these bounds and equations.

An inactive low at support r has defect to e precisely when e is not rho(r) and it has no low neighbor at support e. Therefore L[r,e] is an affine expression: u_r*1[e!=rho(r)] minus all inactive-low incidences from r to support e, including forced edges. Use these expressions to impose the exact remaining defect columns and all45 remaining RR commutator equations. Active lows contribute no residual defects.

For every pair of remaining edge variables that together create a C4 with the forced partial graph, impose x+y<=1. If they share a low endpoint, their other endpoints must not already share a forced common neighbor. If they are disjoint, check the two possible forced-edge completions of the square. These inequalities are necessary; cycles involving three or four variable edges are not yet imposed. There are195461 such pair inequalities across94 models, with at most549 variables in one model.

## Exact status, including unresolved case

Model construction completes94 models in6.052442 seconds under its original30-second cap. The allocation stage terminates in16.677487 seconds, also below its original30-second cap, with3 exact rational Farkas contradictions,90 exact rational feasible assignments, and1 UNKNOWN. Its overall status is INCOMPLETE because that numerical solution did not pass exact reconstruction; this is not a time-cap receipt. All90 verified witnesses are fractional, so none establishes an integer edge set or low-graph realization.

The UNKNOWN is model root46, source_root545, source assignment0, class6, solver status0. No numerical-only conclusion is drawn from it. The original result is preserved. Each of the other93 records is verified by Fraction arithmetic against the model inequalities: nonnegative Farkas weights cancel all coefficients and give a negative right side, or the supplied rational vector satisfies every inequality.

The generic certificate writer uses result.assignment for the rational vector on positive records, while negative/UNKNOWN records retain the source assignment integer there. To avoid ambiguity, case-index.json binds every model root to source_root and source_assignment; models.json always retains the source assignment index. All result-to-case mapping must use the root identifier and this index, not interpret a witness vector as a source index.

These3 exclusions are conditional on independent acceptance of model necessity and exact certificates. The90 fractional witnesses and1 UNKNOWN remain open. No fullcase, global Erdős85, Lean theorem, or capped-domain retry is claimed.
