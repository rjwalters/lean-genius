# Independent crosscheck of the proposed m21 control obstruction

Draft review; source binding and final verdict await the producer's frozen proof.

For the necessary quotient (internal2, cross3), each off-diagonal block of A² is J21: a fixed vertex has exactly21 two-step paths to the other orbit, whose endpoints are distinct by C4-freeness. Evaluating block circulants at any nontrivial21st root z yields a Hermitian3x3 matrix H whose square is diagonal.

At a primitive7th or21st root, each cross entry is nonzero. Three unit complex numbers sum to zero only if they form an equilateral triple, as follows by taking the squared norm of u+v=-w and rotating one summand to1. Seventh roots cannot do this. For21st roots it requires cross offsets t,t+7,t+14; then two vertices in the source orbit separated by7 have the same three cross neighbours, a C4 contradiction.

Write H²=diag(l1,l2,l3). H commutes with its square, and hij nonzero implies li=lj. Thus H²=lI. Since H has a nonzero off-diagonal entry, l>0 and H cannot have all eigenvalues of the same sign: otherwise Hermitian diagonalization would make H=+sqrt(l)I or -sqrt(l)I. Its three eigenvalues therefore have mixed signs, giving tr(H)=+sqrt(l) or -sqrt(l). Consequently K=tr(H²)-3tr(H)^2=0.

At a primitive cube root w, internal diagonal entries ai are2 or-1, while squared cross magnitudes are0,3,9. If exactly one cross entry is nonzero, its H² equation requires ai+aj=0, impossible. Exactly two nonzero cross entries make the missing H² entry a nonzero product. If all three are nonzero, the preceding scalar-square argument applies; writing t=tr(H), H-tI has rank one (eigenvalues0,0,-2t). Its principal2x2 minors imply |hij|²=(ai-t)(aj-t)=(aj+ak)(ai+ak), which belongs to{16,4,1,-2}, disjoint from{0,3,9}. All cross entries at w must therefore vanish.

If r diagonals equal2, then K(w)=(3+3r)-3(3r-3)^2 for r=0,1,2,3: -24,6,-18,-96. All are integers not divisible by7.

On the other hand, K is an integer Laurent polynomial vanishing at primitive roots of orders7 and21. Clear negative powers by z^L. The resulting integer polynomial is divisible by the distinct monic minimal polynomials Phi7 and Phi21, hence by their product in Z[z]. At w, Phi7(w)=1 and Phi21(w)=7, since Phi7(z^3)=Phi7(z)Phi21(z) and w^3=1. Thus w^L*K(w) lies in7Z[w]. As w is a unit, K(w) does too. An integer in7Z[w] is divisible by7 in Z, by the unique integral basis1,w. This contradicts the four values above.

This would exclude only N63/minimum-degree8/free-Z21, given the necessary quotient. It does not exclude the explicit N63/free-Z7 graph, establish any N78/N80 result, or supply a Lean proof.

## Final source-bound verdict: PASS

Read the frozen PROOF.md in full and verified both producer payload hashes. Its section4 uses exponent reduction modulo21 and monic division by (z21-1)/(z3-1), giving the same integrality contradiction without invoking cyclotomic irreducibility. The standalone quotient proof and its four sorted internal-degree cases check. Independently recomputed all cube-root norms, pair-sum products and four K values exactly. No algebraic or scope gap found. This is an accepted paper exclusion of the specified m21 control class, not a Lean theorem or a solver verdict.
