# A6 F15 residual endpoints

CLOSURE.md gives the complete covering chain and scope. export.py preserves exactly the142812host masks from accepted2128; source-indices.json and source-bases.jsonl.gz preserve the original ordering and graph labels. run.py guards live2120/2126/2128, exact accepted source/API/prepared hashes and a single launch marker. It retains explicit UNKNOWN/ARC_FEASIBLE and unvisited states if encountered; this pass completed all leaves negatively.

verify.py reconstructs each source graph and independently regenerates complete residual rows, then checks every ARC deletion against the current domains before applying its atomic batch. Its compiled helper uses increasing active-vertex order, whereas production uses least-uncovered-colour recursion. The helper was already checked on45a6/a7fixtures and1575exact domains. The20-payload host package and accepted API remain referenced through exact manifests. Nothing here is a Lean proof.
