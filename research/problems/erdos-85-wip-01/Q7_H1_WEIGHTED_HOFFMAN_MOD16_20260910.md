# H1 weighted-Hoffman consequence modulo16

2026-09-10, codex-sol-1. Independent paper review1595 PASS (codex-sol-2). This specializes the weighted-Hoffman argument proposed by codex-sol-3; no candidate spectrum is supplied and no H1 profile is excluded.

## Weighted identity and its parity

Use the actual low adjacency C of order48 and t indicating the eight high neighbors. Put a=(7+3sqrt5)/2, b=7-a=1/a, z=a1-t. The simple eigenvalue a has eigenvector z and char_C=(x-a)(x-b)psi_1. All other residual roots have absolute value below a by the defect bounds. For the integer-over-Z[a] polynomial f_a=char_C/(x-a), spectral projection gives

```
f_a(C)=tau*z*z^T,
tau=psi_1(a)/(48a-8)=psi_1(a)/(8(6a-1)).
```

The scalar tau lies in Z[a]: an empty-support and singleton-support coordinate of z differ by1, so the quadratic form of f_a(C) on their coordinate-vector difference equals tau. This avoids treating an arbitrary rational spectral projector as integral.

Work modulo2 in Z[a]/2=F4. Here a+b=ab=1, and write psi_1=(x²+x+1)T² modulo2 with binary T. Put L=(x-b)T; then f_a=(x-a)L² modulo2. Since C is symmetric with zero diagonal, diag(C L(C)²)=0. Also diag(L(C)²)=L^[2](C)1, where [2] squares the coefficients: positive even powers satisfy diag(C^(2j))=C^j1 modulo2. Here L^[2]=(x-a)T.

Let zbar=b1+t. Then1=z+zbar, Cz=az, Czbar=bzbar, and z squared coordinatewise equals zbar. Hence diag f_a(C)=a*T(b)*zbar, whereas the weighted identity gives tau*zbar. Therefore

```
tau = a*T(b) modulo2.
```

Combining this with the exact denominator yields

```
psi_1(a) = 8a*T(b) modulo16
```

in Z[a]/16, since6a-1 is1 modulo2.

## Cyclotomic form of the condition

The already-reviewed H1 Ihara condition, written for the original residual polynomial rather than its reciprocal, is

```
psi_1=q*T²+4R,     q=x²+x+1,
```

for integer R and binary T (obtained by reversing and padding the reciprocal binary factor). Set f=x²-7x+1. Since q(a)=8a and T(a)²=T(b) modulo2, the weighted congruence is equivalent to R(a)=0 modulo4. Division by the monic f identifies this with f dividing R modulo4. But f=q modulo4, so it is equivalent to

```
x²+x+1 divides psi_1(x) modulo16.
```

For the converse, q dividing psi_1 modulo16 and psi_1=qT²+4R imply q divides R modulo4 by taking the degree-at-most-one remainder. Thus the displayed divisibility is exactly the weighted parity refinement under the Ihara premise, not an asserted integer factorization of psi_1.

## Checks and limits

`verify_q7_h1_weighted_mod16.py` checks the field identities and equivalence on256 deterministic polynomial controls satisfying the Ihara premise. Sixteen pass and240 fail; none is asserted to be a residual spectrum or a graph. The controls include a multiple of f in R to check independence from its chosen representative. The matrix-to-weighted-polynomial and parity arguments are paper proofs, not Lean formalization.


The verifier additionally constructs an actual48-by48 symmetric integer C: an8-vertex matching, eight attachment groups of five, and the40-vertex circulant with steps±1,±2,±3. It checks C1=7*1-t and Ct=1, computes the exact degree46 residual polynomial, and verifies the mod16 condition and psi(1)=0 modulo5. This is only a matrix calibration: vertices8,9,10,11 form an explicit C4. It is not a surviving q7 graph or a spectrum satisfying all graph constraints. The paper proof and original256 controls passed review1595; this additional calibration was checked locally afterward.
