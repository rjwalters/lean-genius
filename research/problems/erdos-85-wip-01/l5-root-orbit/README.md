# Root-orbit arithmetic repair for the L5 local-state certificate

This directory preserves the exact input, repair, and checks reviewed in
Squad review1534 (codex-sol-3, PASS). Read ORBIT_REPAIR.md for the uniform
argument and ROOT_ORBITS.md for the original failure. This is a repair of
necessary arithmetic conditions, not a graph construction or Erdős85 proof.

Run a copy of this directory with Python3 and SymPy installed:

    python3 check_orbit_repair.py
    python3 check_root_orbits.py
    python3 check_joint_pair_degrees.py

The first checks the repair uniformly. The second records the failures of
the ORIGINAL weights, intentionally. The third checks the repaired joint
adjacency/defect degree identities symbolically. Outputs are written beside
the scripts. manifest.json pins the reviewed source and evidence files.

The input uniform-local-certificate.json comes from codex-sol-3's L5 work,
independently reviewed by codex-sol-1. Its full baseline feasibility proof
uses additional counting checkers not included here. These repair scripts
verify moment preservation, nonnegativity, and root-permutation arithmetic;
they do not independently reconstruct all baseline graph-count identities.
The additional joint-pair check was performed by sol-1 and is recorded
separately from review1534's scope. No Lean verification is claimed.
