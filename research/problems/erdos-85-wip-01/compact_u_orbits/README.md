# Remaining normalized U symmetry: bounded Python audit

The full compact U domain has 27,000 raw parameter tuples. This audit finds 670 whose induced U graph is C4-free and 55 representatives under the specified 16 relabelings. The deficient domain has 135,000 raw tuples, 5,310 C4-free tuples and 370 representatives under the same action. These are parameter orbits under this subgroup, not a count of all graph isomorphism classes.

The first row has matching mask129, namely edges01 and23 with isolated vertex4. Its stabilizer consists of eight permutations of Fin5. Apply one permutation diagonally to all three rows; optionally exchange rows1 and2. Diagonal relabeling conjugates the cross permutation. Exchanging rows1 and2 swaps their matching masks and inverts the cross permutation. In the deficient case it also moves the missing source d to pi(d), before diagonal relabeling.

For every C4-free tuple, the scripts check all16 relabelings: each transformed tuple remains in the enumerated valid domain, the induced15-label map is bijective, and all225 directed adjacency entries agree. The selected representative is the lexicographically least transformed tuple; each representative is checked to be fixed by this normalization.

Run `python3 generate.py` and `python3 generate_deficient.py` from any directory. They use only the Python standard library and write summaries, representatives and explicit per-input relabeling witnesses to this directory. The checked runs took about0.44s and3.41s respectively. Retained summaries pin generator SHA-256 hashes; representative lists are retained separately. The larger regenerated witness maps are not included in this artifact.

This is Python evidence for a prospective Lean orbit-coverage certificate. It is not a Lean theorem, a whole-graph search, or a rejection certificate. No claim is made that every representative extends to a graph satisfying the complete problem hypotheses. Actual E24 relabeling and all required graph/family constraints still need formal transport before these reductions can replace quantified U parameters in the certificate interface.
