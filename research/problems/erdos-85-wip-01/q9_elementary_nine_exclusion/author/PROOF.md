# Character determinant obstruction for both elementary order9 quotients

Conditional on accepted2207/2208/2211 and the two-representative/deficiency reductions2212/2213. This proposed obstruction excludes the remaining C3 x C3 action at N78, not all graphs at N78.

Write M for graph adjacency and E=8I+J-M^2 for deficiency adjacency. Then ME=EM. By2213 E has components C1,C2,C3 of sizes24,18,36. In particular, restricting commutation to C2 gives M22 E22=E22 M22 (there are no E edges to other components).

C2=X2 union X4. M22 consists of a perfect matching between its two regular P-orbits, so in group convolution blocks it is [[0,U],[U*,0]], with U a translation. E22 has blocks [[R,V],[V*,S]], with V a translation and R,S inverse-closed Cayley connection sets of size4. Since all translations commute in P, the offdiagonal commutation equation US=RU forces S=R. The diagonal equation UV*=VU* forces the translation U V^{-1} to be its own inverse. P has exponent3, so U=V. Thus, after choosing compatible origins, E22=[[R,I],[I,R]]. R consists of two distinct lines' nonzero elements; there are six choices of that pair among the four lines of F3^2.

For each nontrivial character chi:P-> {1,omega,omega^2}, let K be its kernel line. On the chi-isotypic vertex space, J=0 and therefore M_chi^2=8I-E_chi. In a basis of character-valued functions on vertex orbits, all entries of M_chi are Eisenstein integers. (A short orbit contributes one basis vector precisely when its stabilizer is K.) M_chi is similar to a Hermitian matrix, as it is the restriction of real symmetric M, so its determinant is real. A real Eisenstein integer is an ordinary integer. Consequently det(8I-E_chi)=det(M_chi)^2 must be a nonnegative integer square. The conjugate character has the same determinant; only the four kernel lines need consideration.

Because E is block diagonal by components, this determinant is the product of its three component determinants. Each component's orbit support is a tree (allowing internal diagonal Cayley graphs), so phases in matching entries cancel, and a double-edge block enters only through its squared character magnitude. The following formulas are exact; their product provides a necessary test without reconstructing graph edge phases.

Label the short stabilizers L_A=0,L_B=1; the other two lines are2,3.

C1: its orbit chain is A--X1--X3--B. The internal connection line at X1 is u, at X3 is v, and the difference line of the two X1--X3 offsets is w. Each has four possibilities. Set x=8-(2 if K=u else -1), y=8-(2 if K=v else -1), and t=4 if K=w else1. If K=0, the determinant is (9x-3)y-9t; if K=1, it is (9y-3)x-9t; otherwise it is xy-t. The9 is8 minus the eigenvalue -1 of a triangle on its nontrivial character; the3 is the product of the two short-to-long incidence coefficients. Only one short orbit occurs for a given nontrivial character, since L_A differs from L_B.

C2: choose a pair S of distinct lines. Its internal Cayley eigenvalue is1 when K belongs to S, and -2 otherwise. The determinant is (8-d)^2-1.

C3: the orbit support is the star X0--{X5,X6,X7}, all three edges perfect matchings. Choose one internal connection line u0 at X0, and a pair of distinct internal connection lines S_i at each leaf. Set z=8-(2 if K=u0 else -1), and v_i=8-(1 if K belongs to S_i else -2). The determinant is z*v1*v2*v3-(v1*v2+v1*v3+v2*v3).

These choices deliberately ignore other constraints, giving a superset of possible deficiency graphs: 4^3 * 6 * (4*6^3)=331776 assignments. run.py visits every assignment under the original60second aggregate cap, evaluates these integer determinants and checks exact integer squares. It completes in about0.192s with no survivors; all fail already at K=0. No numerical eigenvalues, numerical solver, timeout inference or retry is used.

Subject to independent verification of this proof and finite arithmetic, neither quotient can lift. Combining the complete quotient coverage and2207 would improve the N78 Sylow3 bound from9 to3. This still leaves other automorphism groups and asymmetric graphs, and is not a solution of Erdős85.
