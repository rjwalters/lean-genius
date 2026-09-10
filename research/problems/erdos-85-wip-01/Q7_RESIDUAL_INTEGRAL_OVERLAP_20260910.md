# Residual congruences from integral subspace overlap

2026-09-10, codex-sol-1. Independent paper/lattice review1591 PASS (codex-sol-3); prior-work comparison remains pending. Necessary conditions only; no profile is excluded or residual polynomial exhibited.

Use the exact low block C and integer incidence matrix B in `Q7_H1_H3_SQUEEZE_20260910.md`. Set R=[1^T;B] and let L=ker(R:Z^l -> Z^(h+1)). Every incidence profile has an empty-support vertex and a singleton-support vertex for each high label. Taking those columns gives a unimodular minor of R. Thus R is split surjective, L is a free direct summand, and reduction modulo any prime p identifies L/pL with ker(R modp). This avoids assuming that rational orthogonal projection preserves an integral lattice.

The identities BC=J and C1=7*1-t imply that C preserves L. In an integer basis of L its characteristic polynomial is precisely the monic residual factor psi_h from the rational block decomposition. Therefore a nonzero eigenvector of C on ker(R modp) with eigenvalue lambda forces psi_h(lambda)=0 modp.

For h1 take p=5 and v=1-6t. For h3 take p=67 and v=12*1-23t. The exact checks are:

| h | v | 1^T v | Bv | Cv-lambda v | lambda |
|---|---|---:|---|---|---:|
| 1 | 1-6t | 0 | -40*1_h | 5t | 1 |
| 3 | 12*1-23t | 0 | -134*1_h | -201*1+402t | 18 |

Each v is nonzero modulo the stated prime (look at an empty-support coordinate). Both Rv and the displayed eigenvector error vanish modulo that prime. Consequently

```
psi_1(1) = 0 mod5,
psi_3(18) = 0 mod67.
```

This uses simultaneous C invariance and the integral lattice. It is stronger than merely asking whether the incidence Gram matrix can be represented: that matrix already has an explicit integer representation. It does not require D connectivity, though it applies to the remaining connected cases.

`verify_q7_residual_overlap.py` constructs B for h1 and both h3 incidence profiles, an explicit integer basis of ker R using the unimodular minor, and the nonzero modular vectors above. It checks reduction into that kernel basis and the formal eigenvector identities from C1,Ct. No C completion is constructed. The characteristic-polynomial conclusion is the paper argument above, not a formal Lean theorem.


## H3 residual kernel modulo7 and determinant valuation

The reviewed H5/H7 lattice argument (review1593) applies to h3 as well. Let X have columns e1-e3,e2-e3 and put W=B^T X. Then BW=7X, 1^T W=0 and CW=JX=0. Modulo7 the two columns of W therefore lie in the reduction of the integral residual lattice and in the residual C kernel. They are independent: the singleton coordinates for highs1 and2 give an identity minor. Thus the residual integer matrix has nullity at least2 modulo7.

It follows that x² divides psi3 modulo7 and **49 divides psi3(0)**. The valuation statement follows from the actual two-dimensional kernel: lift a kernel basis to an invertible matrix over Z7, making its first two image columns divisible by7, and take determinants. Characteristic-polynomial multiplicity alone would not justify this valuation. Since psi3(0) is nonzero, det A is a nonzero multiple of46*7^4=110446.

The verifier now checks both high-difference columns, their independence, and their reduction into the explicit kernel basis for both H3 incidence profiles. It also computes the exact kernel-lattice Gram determinant,320 for h1 and13132 for h3; the equality with det(RR^T) follows from the unimodular pivot and Sylvester's determinant identity. These are additional necessary constraints, not exclusions. No new unknown C matrix is constructed.
