# Exact-cover obstruction for one completion

The certificate fixes U compact parameters(6,6,15), R representative14 and an
explicit cross matrix, corresponding to representative33 in the private Python
70-orbit diagnostic. Literal adjacency equality, cross-domain membership and
external block cap are ordinary kernel checks.

Supplied lists of20/26/28 triples cover all initially eligible block-capped
triples. Kernel evaluation of finitePivotCoverSearch shows that color1 has no
six-triple exact cover of its residual set. The generic selected-cover theorem
therefore proves no_joint for the original adjacency. No seven-vertex separated
set or runtime terminal result is needed for this proof.

All seven printed exports use only standard axioms. This excludes exactly the
supplied completion; neither the1120-cross enumeration nor70-orbit coverage is
proved here, and no whole-pair or Erdős85 solution is claimed.

Run from proofs after building Proofs.Erdos85ThreeHighSelectedCoverCertificate:
`lake env lean ../research/problems/erdos-85-wip-01/exact_cover_terminal_canary/Certificate.lean`
