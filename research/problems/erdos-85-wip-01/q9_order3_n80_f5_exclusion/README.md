# Order-three automorphisms at80 vertices: five fixed vertices excluded

For a C4-free graph on80 vertices with minimum degree at least9, no automorphism of order3 fixes five vertices. Together with the independently accepted fixed-count theorem2176, every such automorphism fixes exactly two vertices.

This archive preserves a finite paper/computational proof, including exact integer certificates and independently checked complete enumerations. It is not a fully formalized Lean theorem and does not exclude graphs with two fixed vertices or without order-three symmetry. Erdős85 remains unresolved.

The closure proof and review snapshots are in `q9-order3-n80-f5-closure`. The necessary attached matching system has1284 symmetry representatives. Completed exclusions form a disjoint exact partition:708 shared-color linear certificates,516 completed color/row searches,58 symmetric fractional-residual certificates,one double-entry-budget certificate, andone empty local-row-support fixed point. Review2214 independently verified both the last step and the full partition.

Each source directory preserves its original pins and outcomes. Capped searches and failed numerical rationalizations remain recorded; none is counted as an exclusion. Later distinct models supply the completed evidence. Numerical LP engines discovered candidates, while exact integer arithmetic verified every negative certificate used here.

The eleven `peer-review-*` directories preserve independent audits of the necessary formulations, enumeration coverage, symmetry action, certificates, and final case closure. Earlier2176/2179 fixed-count and normal-form proofs are already archived elsewhere in this repository and their accepted review records are included in the closure snapshot.

Run `python3 verify_archive.py` for a read-only check of all copied payload hashes, original source pins, accepted review snapshots, and the exact1284-case partition. It does not rerun searches or replace the independent mathematical audits. Frozen scripts retain original provenance paths; the archive checker resolves the copied evidence locally.
