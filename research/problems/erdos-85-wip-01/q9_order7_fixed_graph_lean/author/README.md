# Order-seven fixed-graph Lean reduction

Two new integration modules:
- Erdos85TwoNineDegreeReduction.lean: a nonempty C4-free fixed graph of order at most23, degree2/9, fixed-card congruence modulo7, and ambient78/80 boundary inequality has order8 at78, or3/10 at80; every degree is2.
- Erdos85OrderSevenFixedGraph.lean: derives every preceding fixed-graph hypothesis from a finite C4-free minimum-degree9 graph of order78/80 and a nonidentity adjacency-preserving map whose seventh iterate is identity.

The counting proof uses 10r=2choose(r,2)+18 at degrees2/9, cherry counting and the boundary inequality. It obtains83F<=F²+10N and the stated cardinal possibilities. In the ten-vertex case, any degree9 vertex would force the total degree to27, contradicting handshake parity. The assembly uses prime fixed-degree congruence, the moved-card57 bound, regularity, fixed/moved cardinal split and fixed-boundary counting. Global fixed-point congruence supplies nonempty fixed set because neither78 nor80 is divisible by7.

Accepted component reviews:2171 FixedNeighbors,2172 MovedDegree,2173 MovedCard,2178 FixedBoundary,2180 PrimeFixedDegree. All five component source files are frozen here together with the two new modules. This package contains a fresh combined Audit.lean, topologically concatenating all seven full source bodies and importing only the existing DistanceLayers, GadgetDegreeSquares, GadgetCounting and Mathlib Cycle.Type dependencies. It does not import a precompiled new module.

Targeted builds passed with terminal exit0: TwoNineDegreeReduction4.3s, OrderSevenFixedGraph3.5s;8192MB,10m,LEAN_SKIP_CACHE=true. Separate combined-source audit passed exit0 with standard propext/Classical.choice/Quot.sound axioms for both new final declarations; raw result compile.json.

Direct audit setup: image lean4-arm64:v4.31.0,4096MB memory/swap,two CPUs; read-only integration /workspace, shared lean-mathlib-cache and lean-mathlib-packages at /workspace/proofs/.lake/build and packages, this directory /audit; working directory /workspace/proofs; timeout 120s lake env lean /audit/Audit.lean. Peer review should verify all frozen/live equalities and independently assemble/compile all source bodies.

Scope is the first half of accepted paper2169. It does not exclude the remaining fixed configurations or prove the full absence of order-seven automorphisms in Lean. The attached-orbit counting contradiction is still a formalization obligation. No graph search or solver was run.
