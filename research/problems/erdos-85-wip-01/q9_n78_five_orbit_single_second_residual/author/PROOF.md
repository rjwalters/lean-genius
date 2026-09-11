# No saved first residual orbit admits the second residual orbit

The inputs are all896 first-B12 neighborhoods saved in the single-residual packet submitted as2347, on the partial graphs from2345. Their complete coverage uses accepted2343 and separate independent acceptance of2345 and2347. This packet keeps those dependencies conditional.

For every input, reconstruct the full orbit of twelve distinct B-neighborhoods under left translation and append all twelve incidence vertices to the54-vertex partial graph. This66-vertex graph is invariant under the group action: left translation permutes the complete family of B-neighborhoods.

The second residual orbit C has four U-neighbors and two V-neighbors at each vertex, by the accepted single-attachment quotient. Normalize a chosen V-neighbor to V1. This normalization is still valid after selecting the B orbit: translating the entire group-invariant B-neighborhood family leaves that family unchanged, although it may change which member is labelled as its origin. Thus no compatible C choice is lost by the second normalization.

For every involution l with no fixed center, let L={1,l}. The two V-neighbors must be{V1,Vl}; the four U-neighbors must be two left-L pairs. As in2343/2347, a fixed center would force l to fix the unique selected attached vertex over that center, impossible in a regular attached orbit. Every candidate must cover all six centers once.

Reject any pair of selected vertices having a common neighbor in the reconstructed66-vertex graph. This enforces compatibility with the original partial graph AND every vertex of B. In particular it rules out a C neighborhood intersecting any B neighborhood in two vertices. Finally enforce |X intersect gX|<=1 for every g outside L, ensuring that distinct translated C neighborhoods do not have two common vertices. These conditions are necessary before any residual internal edges are supplied.

The original aggregate30-second run completed in0.090 seconds. All896 input roots are COMPLETE and negative; no second-orbit neighborhood survives. No UNKNOWN or unvisited receipt occurs. The exact input correspondence and per-root receipts are saved in results.json.

After independent acceptance of2345/2347 establishes complete input coverage, this obstruction excludes the remaining order24 single-attachment five-orbit case. The separate accepted2338 and2342 cover the split-center and double-attachment cases, and2339 covers order48, but their final assembly is not performed in this packet.

No residual internal edges were enumerated, no full graph solver was run, and no graph with six or more automorphism orbits or the global Erdős85 problem is excluded here. This is a finite necessary-incidence obstruction and is not Lean formalization.
