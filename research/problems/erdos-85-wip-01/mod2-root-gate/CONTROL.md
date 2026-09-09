# Uniform graph-derived controls for the full mod-2 alternating-root test

Status: explicit uniform prose construction, pending independent review.
No A-REG counterexample, rational/integer square root, or Lean claim.

Let q=2^k with k>=3, set s=q squared/4 and t=q/4-1. Let T be the
circulant on Z/sZ with steps plus/minus 1,...,t. The steps are distinct,
nonzero and include 1, so T is simple, connected and 2t-regular.
Let H be the Cartesian product K2 square T, on m=2s vertices. It is
connected, (2t+1)=(q/2-1)-regular, and admits the fixed-point-free
involutive automorphism P which swaps the K2 coordinate; each vertex is
adjacent to its P partner. Let D=H[K2], the lexicographic product with K2.
Then D is simple, connected, nonbipartite (each edge of H gives a K4),
on n=2m=q squared vertices, and has degree 2(q/2-1)+1=q-1.
Its single component has size q times q, satisfying the existing component
size law, with no unit component and no bipartite component.

All subsequent matrices are over F2. Order H by its K2 coordinate and set
F=I_m+J_m+H. Its block form is

    F = [[F0,F1],[F1,F0]],
    F0=I_s+J_s+T,       F1=J_s+I_s.

Both F0 and F1 are symmetric with zero diagonal. Choose the strictly
upper-triangular matrix U with U+U transpose=F0, and set

    B = [[0,U],[U transpose,F1]],
    P = [[0,I_s],[I_s,0]],       X=I_m+P.

B is symmetric with zero diagonal, X is symmetric, and X squared=0.
Direct block multiplication gives

    BP+PB = [[U+U transpose,F1],[F1,U+U transpose]]=F,
    BX+XB = BP+PB=F.

Now order D by the internal K2 coordinate of each doubled vertex and set

    A = [[B,B+X],[B+X,B]].

This A is symmetric with zero diagonal. Its row sums vanish since
A1=(X1,X1)=0. Its square has diagonal blocks
B squared+(B+X) squared=BX+XB+X squared=F,
and off-diagonal blocks B(B+X)+(B+X)B=BX+XB=F. Therefore

    A squared = [[F,F],[F,F]] = I_n+J_n+D.

The last equality follows from the graph definition: D has diagonal
blocks H and off-diagonal blocks H+I_m in this ordering. Thus the complete
necessary mod-2 alternating-root test is satisfied for every binary q>=8.

## Scope

The matrix A is a binary representative of a root modulo 2. It is not
asserted to have integer row sum q or exact integer common-neighbor counts.
This controls the full mod-2 root predicate on actual simple regular
connected nonbipartite D, rather than on a formal characteristic polynomial.
It does not certify determinant-square, rational Hasse invariants, higher
2-adic lifting, or an integer adjacency root. Existing filters may exclude
these D for other reasons.

Consequently a criterion solely for existence of an alternating symmetric
root of I+J+D over F2 cannot exclude all D satisfying the degree and defect
component laws. Such a criterion can still reject individual candidates.
A conjunction with additional graph-derived arithmetic information is not
ruled out. No claim of novelty is made.
