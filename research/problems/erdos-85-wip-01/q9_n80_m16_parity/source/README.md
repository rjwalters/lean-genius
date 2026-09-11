# Parity-character necessary matrices for the six N80/m16 quotients

codex-sol-2, 2026-09-11. This is an integer character-matrix filter, not a graph search. It adds no CNF clauses and launches no solver.

For a quotient Q from accepted2152, evaluate each circulant block of the adjacency matrix at z=-1, obtaining a real symmetric matrix H. A cross block of degree q has entry in{-q,-q+2,...,q}. Internal degree0 gives0; internal degree1 uses shift8 and gives+1; internal degree2 gives±2. These are necessary values; not every signed matrix lifts to offset sets.

Let T=(Q²)ij for i!=j. The corresponding adjacency-square block is a0/1 circulant with T ones. Among its16 offsets, eight are even and eight odd. Hence `(H²)ij=2e-T` for some0<=e<=8 and0<=T-e<=8, equivalently absolute value at most min(T,16-T) and parity T.

Within one orbit, the adjacency square has diagonal9 and `(Q²)ii-9` other1 entries. The latter offsets are negation-invariant and cannot contain8: the common neighbours of antipodal vertices would be paired by the free involution, contradicting codegree at most1. Thus they comprise k=((Q²)ii-9)/2 opposite pairs from representatives1,...,7. Three representatives are even and four are odd. The possible diagonal value is `9+2(e-o)` with e+o=k,0<=e<=3,0<=o<=4.

The native program exhausts all allowed H entries. Each fixed type, diagonal-sign choice and first-two-edge choice is one case, with at most11664 combinations; the original aggregate cap was60seconds. All cases completed in0.010seconds, leaving respectively **36,48,32,32,64,80** signed matrices for quotient types0 through5. Every type retains candidates; this stage alone excludes none.

The independent verifier uses complete signed-row templates with allowed squared norms, joins them by matrix symmetry and checks cross dot products as rows arrive. It derives allowed diagonal norms by enumerating opposite-pair subsets and cross values by even/odd cardinalities, rather than importing native formulas or code. It reproduces every retained matrix exactly, in2578states with maximum345states per first row. Verification receipts include its elapsed time.

The separate mixed-triangle argument2154 excludes quotient types2 and5; that exclusion is not used by either parity enumeration. If combined after independent acceptance,180 parity matrices remain across types0,1,3,4. This is not a graph existence result, a complete N80/m16 exclusion or a Lean theorem. Original result files are preserved; no retry or cap increase occurred.
