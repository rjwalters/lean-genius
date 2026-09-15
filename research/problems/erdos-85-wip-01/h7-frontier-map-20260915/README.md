# H7 frozen-root structural scope map

The 28 frozen H7 roots split into **12 roots covered by selected accepted structural exclusion scopes** and **16 not covered by those scopes**. This is a conditional provenance join, not a new exclusion proof, Lean theorem, or change to the solver queue. It does not assert no additional reductions exist.

The map uses accepted reviews 2080 (a9), 2091 (a8), 2117 (C7), 2127 (F9), and 2131 (F15). It verifies every inventory source hash, root ID/index/CNF hash, edge count, and parent-to-classification permutation. Shape matches carry an explicit vertex permutation, checked on the complete edge set. Input byte pins are in results.json; check.py reproduces the join without invoking historical research scripts.

## Avoid confusing naming systems

- Reviewed F15 (two triangles and an isolated vertex) maps to **cube_F6_t14**, not cube_F6_t15.
- Reviewed F9 (a triangle with a pendant edge, plus a disjoint triangle) and C7 map to the two covered a7 roots; exact labels and permutations are in results.json.
- Every a8/a9 root is covered by its full edge-count exclusion.

## Remaining selected-scope complement

Six a6 roots: t5, t8, t15, t16, t17, t18.
Ten a7 roots: t0, t2, t3, t4, t5, t6, t8, t10, t11, t13.

These IDs describe structural work still outside the selected whole-shape exclusions. In particular, a complete host cover alone is not a residual completion exclusion, and UNKNOWN/unvisited suffixes remain unresolved. All historical caps and dispatch gates remain unchanged.

Peer review requested before using this mapping operationally. The proof premises of the five accepted structural exclusions are inherited, not rerun by this script. Full Erdős 85 and finite-drop kernel closure remain open.
