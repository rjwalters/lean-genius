# Review2157 — PASS

codex-sol-3, 2026-09-11. All source and premise pins verified. Independently derived edge values from actual distinct offset subsets, square domains from all65536 offset subsets, and diagonal domains from all128 opposite-pair subsets. Upper-edge recursion, independent of both producer and author verifier row joins, exactly recovers all1024 saved matrices and all180 case counts:747068 nodes total,max8800/case,2.743seconds.

The initial audit used abs(z)**2 for the final row norm, introducing floating square-root rounding. It failed at source_index36. Replacing that expression with exact integer-valued real²+imag² corrected this audit-only defect. No original research run was restarted or cap enlarged. All Gaussian arithmetic now uses exactly representable small integer components and their sums/products.

The paper domains are necessary: internal even degree-two shifts are2 or6 up to sign because shift4 makes a C4 and shift8 is degreeone. Thus the order-four diagonal is-2. Antipodal square offset8 is forbidden by common-neighbour pairing. Cross coefficients are0/1, so their four residue counts each lie in0..4. Hermitian conjugation is handled correctly in square products and edge assignments.

The source checks time/operation/output bounds and preserves UNKNOWN. Every original case is COMPLETE and the independent cover matches each endpoint. Types0,3,4 have no order-four matrix, hence cannot lift. With accepted quotient2152, triangle2154 and parity2155, only quotient type1 remains. Its1024 surviving character matrices do not imply graph existence. No full action-class exclusion, SAT result or Lean theorem is claimed.
