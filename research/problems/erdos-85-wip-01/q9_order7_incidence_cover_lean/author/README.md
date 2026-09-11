# Incidence capacity and neighbour-cover Lean review

Two new integration modules support the final order-seven incidence proof.

Erdos85NeighborCover.lean proves degree(a)<=|B| in a C4-free graph if a is outside B and every neighbour of a has a neighbour in B. Choosing such endpoints is injective because any collision would give two common neighbours of distinct a and b. Its contrapositive forces C4 when |B|<degree(a).

Erdos85IncidenceCapacity.lean proves sum(degrees on A)<=|D| when vertices outside D have zero neighbours in A and every vertex has at most one neighbour in A. The equality theorem proves every vertex of D has exactly one neighbour in A. These two theorems use no C4-freeness; their incidence assumptions remain explicit.

Targeted Docker builds passed, terminal exit0: NeighborCover12s and IncidenceCapacity20s, with8192MB/10m limits and LEAN_SKIP_CACHE=true. Combined Audit.lean contains both full source bodies and four axiom prints, importing only existing GadgetCounting. Separate direct-source Docker compilation exited0; all four declarations use only propext, Classical.choice and Quot.sound. Raw output is compile.json.

Audit setup: image lean4-arm64:v4.31.0,4096MB memory/swap,two CPUs; read-only integration at /workspace, lean-mathlib-cache at /workspace/proofs/.lake/build, lean-mathlib-packages at /workspace/proofs/.lake/packages, this directory at /audit. Working directory /workspace/proofs; command: timeout 120s lake env lean /audit/Audit.lean. Please independently verify live/frozen equality and compile both complete bodies.

The attached-set application must still supply zero/one incidence bounds, degree sums and cardinalities. No full order-seven exclusion, graph search or unrestricted nonexistence result is claimed by this package.
