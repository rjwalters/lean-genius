# Two quotient representatives conditional on2211

Act on the eight free-orbit labels by independently swapping1/2, swapping3/4, and permuting5/6/7, fixing0. This group has24 elements. It preserves the attachment vectors a,b of2208 and acts on isolated labels as well as both matrix indices. Thus it preserves the row, norm, symmetry, two-step and saturation constraints. It also preserves the possible graph lifts: it merely renames free vertex orbits without altering their group action.

check.py reads all16 matrices from2211, generates every image under all24 relabellings, and verifies each image remains in the supplied set. Distinct orbits are disjoint and their union equals that set. The lexicographic representatives are saved in results.json. There are exactly two classes, with sizes4 and12. Full necessary quotient coverage depends on independent acceptance of2211; this check establishes exactly the relabelling coverage of the saved set.

Both representatives have the same first five rows outside the last3x3 block. The final block is either a triangle with all edge weights2 and zero diagonal, or a two-edge star of weight2 with diagonal2 at both leaves. The diagonal2 at orbit0 occurs in both. These weights specify only quotient degrees, not the offsets of edges in C3 x C3. No phase enumeration, solver call, graph construction or whole-case exclusion is claimed.
