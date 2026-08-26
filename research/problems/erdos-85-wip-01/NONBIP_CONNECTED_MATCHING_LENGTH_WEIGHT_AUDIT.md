# NONBIP-CONNECTED matching length-weight audit

Status: bounded negative refinement of the signed matching-exchange lane,
26 August 2026.

The positive q=4 calibration gives a perfect matching in the bipartite graph
whose shores are positive and negative Levi perfect matchings and whose
edges are sign-changing single-cycle switches.  A fractional perfect
matching would already imply an integral one by bipartite matching
integrality.

Every even alternating cycle defines a partial sign-reversing involution.
The cheapest uniform fractional ansatz assigns a nonnegative weight `c_l`
to every switch of half-length `l`.  The load at a Levi matching `M` is

```text
sum_{l in {4,6,...,16}} c_l * numberOfAlternatingCycles(M,l).
```

If this load were one for every `M`, the cycle weights would give a
fractional perfect matching and hence prove Hall automatically.

`nonbip_connected_matching_length_weight_control.py` enumerates the first
twelve deterministic perfect matchings of the exact q=4 control and counts
all simple sign-changing alternating cycles at each half-length.  The
resulting `12 x 7` integer matrix has exact rational rank 7, while appending
the all-ones target column raises the rank to 8.  Therefore no weights exist,
even allowing arbitrary signed rational `c_l`; nonnegativity is irrelevant.

This cuts every fractional normalization depending only on cycle length.
The successful q=4 perfect pairing is consequently placement-sensitive.
A q-generic Hall proof must use which vertices/triangle owners a cycle
visits, or a genuinely global switch potential; aggregate cycle length is
not enough.
