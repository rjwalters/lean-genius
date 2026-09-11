# Review2174 — PASS independent direct-source compilation

All four frozen pins and live/source equality verified. Independently compiled complete theorem source plus axiom prints, importing only existing DistanceLayers rather than the precompiled new module. Read-only Docker dependencies, network disabled,2CPUs/8GiB; terminal exit0 in2.828seconds. Both declarations depend exactly on propext, Classical.choice and Quot.sound, no sorryAx. Raw output and exact command receipt preserved.

The first declaration transports the existing tight-point theorem on Fin(k*(k-1)+1) through overFinIso, preserving minimum degree and pulling the injective C4 embedding back through the inverse graph isomorphism. The second explicitly assumes a nonempty vertex type, chooses a centre, derives the weak cardinality bound from degree>=k and the distance-layer inequality, then excludes equality using the first declaration. The arithmetic requires k>=3 as stated. No hidden vertex-order or automorphism assumption occurs.

Specializing k8 gives cardinality>57, hence at least58 for any nonempty C4-free minimum-degree8 graph. Combined with independently reviewed moved-degree results this sharpens the moved-set bound. It does not itself establish any fixed-point enumeration or global N78/N80 exclusion.
