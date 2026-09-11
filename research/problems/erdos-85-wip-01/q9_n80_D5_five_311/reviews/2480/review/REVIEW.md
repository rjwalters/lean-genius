# Review 2480 — PASS model and partial exact results, UNKNOWN retained

Fourteen hashes and fresh accepted 2467,2469,2473,2476,2478 checked. The original results remain INCOMPLETE, with model46 UNKNOWN; this audit does not rerun its solver or replace that outcome.

Independently reconstructed all94 source/assignment keys from the accepted propagation positives. Each model's low vertices and forced graph come from that exact source; its variable list equals the complete remaining-edge list. Exact degrees and per-support constraints correctly subtract forced incidences. For inactive low vertices, absence of a low neighbor at a support other than the unique residual-middle endpoint is precisely a residual defect. Summing these affine indicators reconstructs every defect-column and commutator equation, using independently audited remaining commutators from review2473. Active lows contribute no defect. Omitting involution constraints admits actual solutions and therefore is a valid relaxation.

Independently reconstructed all195461 two-variable C4 conflicts. With adjacent variable edges, the two other endpoints must already have a common fixed neighbor; with disjoint variable edges, a square requires one of the two complementary fixed-edge pairs. Both patterns are necessary exclusions. This does not assert that cycles using three or four variables have been encoded.

Every bound and labeled constraint matches the independent model, including the UNKNOWN model. Exact Fraction checks verify the three Farkas certificates (nonnegative weights, zero combined coefficients and strictly negative right-hand side) and all90 fractional witnesses. Model46/source545/source_assignment0 is retained UNKNOWN. case-index.json and model roots establish correspondence; the result.assignment witness vector is never interpreted as a source-assignment index.

COMPLETE independent audit in10.245243209 seconds under its original30-second aggregate cap. This verifies the stated three exclusions only. The ninety fractional models and one UNKNOWN remain open, with no graph construction, fullcase exclusion, capped retry or Lean theorem claimed.
