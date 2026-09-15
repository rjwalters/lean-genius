# Selected H7 coverage: a6 F16 and F17

This exact two-row overlay extends the 24-root map banked at 76f775789408dd46f02e0cc11b919e0f761fdc64. Reviews 2704 and 2709 add cube_F6_t15 (source F16) and cube_F6_t5 (source F17). The other 26 rows are unchanged, including root masks and CNF identities.

The selected reviewed coverage is 26 of 28 roots. Remaining are cube_F6_t17 (source F12) and cube_F6_t18 (source F14). F12 partial exclusions do not promote its root; F14 host completeness alone does not exclude its root.

Run `python3 check.py` to check input hashes, exact review snapshots, root permutations and the two-row delta. Source/quotient completeness remains inherited. No arbitrary CNF UNSAT, Lean/kernel, whole H7 or global Erdős 85 theorem is claimed.
