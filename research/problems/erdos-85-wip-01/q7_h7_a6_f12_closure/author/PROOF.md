# Coupled singleton–pair incidence projection

Use the refined necessary singleton families from review 2712. Every graph completion selects one family F(p) for each pair vertex p. Each singleton s must appear in exactly c(s)=7-deg(s) selected families.

There is an additional C4 restriction across different pair vertices. Their selected families cannot add too many common singleton neighbours: for distinct p,q,

    |F(p) intersect F(q)| + |N_saved(p) intersect N_saved(q)| <= 1.

The two terms count disjoint sets. Saved pair-vertex neighbours are high or empty vertices, whereas members of F(p) are singletons. Any two common neighbours would form a four-cycle. Missing pair–pair edges can only create additional obstructions, so omitting those edges is a necessary relaxation.

The bounded choice search assigns one complete necessary family at each pair vertex. It rejects a choice only if it exceeds a singleton capacity or violates the displayed common-neighbour bound with a previously assigned pair. A negative tree lists every family choice at every visited node and either its explicit capacity/C4 rejection or the next child. A separately reconstructed-family checker verifies every branch. A positive leaf supplies a singleton–pair incidence projection, which is checked directly but is not a completed graph because missing pair–pair edges are omitted.

The probe is limited to 10000 tree nodes per case, 60 seconds total and 50 MB of compact record data, on the 23 cases remaining after review 2712. UNKNOWN and unvisited cases remain explicit. It does not rerun the historical residual-row or ARC implementation. This finite necessary model does not constitute a Lean/kernel or global Erdős 85 proof.
