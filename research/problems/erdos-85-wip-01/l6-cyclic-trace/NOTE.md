# A rational trace obstruction for interval circulant defects

This excludes the interval circulant defect at q=16 and q=64 using small
polynomial calculations. It does not prove that arbitrary defects are
circulant, or exclude a cofinal family. The q=16 example was already excluded
by the squad's independent Hasse-invariant calculation. The q=64 result
uses no dense 4096 by 4096 matrix, graph search, or primality assumptions.

Let q=4^a, a>=2, n=q^2 and m=q/2. On Z/n take the defect connection set
{n/2} union +/-{1,...,m-1}. Put M=(q-1)I+J-D. Suppose there is a rational
symmetric matrix A with A^2=M, A1=q1, and trace(A)=0. Every hypothetical
q-regular loopless graph giving this defect would satisfy these conditions.

## A conditional criterion valid for every a

For a primitive d-th root zeta, d=2^b>=4, let K_d=Q(zeta+zeta^-1), and set

    lambda_d = q-2 - sum_{j=1}^{m-1}(zeta^j+zeta^-j)  (d<n),
    lambda_n = q   - sum_{j=1}^{m-1}(zeta^j+zeta^-j).

If lambda_d is nonsquare in K_d for every d>q dividing n, such A cannot exist.

Indeed, Fourier diagonalization of M gives these eigenvalues:

* The constant vector has eigenvalue n, with multiplicity one.
* All nontrivial m-th roots give eigenvalue q, total multiplicity m-1.
  This follows by summing each full m-th-root geometric progression.
* Primitive q-th roots give eigenvalue q-2, total multiplicity m, since
  zeta^m=-1 and the symmetric partial sum is zero.
* The remaining strata are those d>q above, each with real-field degree
  d/4 and total dimension d/2.

The value q-2 is a nonsquare rational integer: it is 2 modulo 4. For a
higher-stratum value lambda, nonsquareness in K_d implies nonsquareness in
the subfield Q(lambda). If h is its irreducible polynomial over Q, then
h(t^2) is irreducible: adjoining sqrt(lambda) has twice the degree of
adjoining lambda. In particular it is even. Rationality of A forces equal
multiplicity for all its conjugate roots, so the contribution of this entire
irreducible factor to trace(A) is zero. The same argument applies to q-2.
This remains valid if strata share eigenvalues; it does not require A to
preserve Fourier spaces or commute with cyclic shift.

None of these nonsquare values can equal the rational squares q or n.
Thus the only contributions left are q from A1=q1 and +/-sqrt(q) from the
q-eigenspace of odd dimension m-1. Hence

    trace(A)/sqrt(q) = sqrt(q) + an odd integer,

which is odd and cannot vanish. This proves the criterion. Symmetry makes
the spectral discussion immediate; no assumption that A is circulant is used.

## Exact norm certificates at q=16 and q=64

It suffices to show Norm_{K_d/Q}(lambda_d) is a nonsquare integer. Define
f_2(x)=x and f_{b+1}(x)=f_b(x)^2-2. Then f_b is the monic minimal polynomial
of zeta_{2^b}+zeta_{2^b}^-1: its roots are precisely the primitive real
cyclotomic conjugates, and its degree is phi(2^b)/2. Define C_0=2,C_1=x,
C_j=x C_{j-1}-C_{j-2}; these evaluate to zeta^j+zeta^-j. The relevant norm is
the integer resultant of f_b and q-2-sum C_j, with q replacing q-2 at d=n.

The checker computes this resultant modulo a certified small odd prime p
and verifies that its nonzero residue is a quadratic nonresidue. A square
integer cannot have that residue, so this is a complete nonsquareness
certificate, without factoring a large norm. All strata d>q are checked.
It also checks the constant values on all lower real-cyclotomic strata and
the dimension census. Run `python3 check.py`; see verification.json.

The maximum polynomial degree is 1024 at q=64, with the second polynomial
of degree31. No matrix of order4096 is constructed. The finite certificates
do not establish nonsquareness uniformly in a. That number-theoretic
statement is the precise missing input for extending this particular
defect-family exclusion to unbounded q; even that would not close A-REG.
