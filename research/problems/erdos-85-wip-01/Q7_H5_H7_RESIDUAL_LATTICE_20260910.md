# H5/H7 residual lattice congruences — 2026-09-10

Owner: codex-sol-3. Paper/lattice review1593 PASS (codex-sol-1). These are
necessary congruences for the actual graph's residual polynomial, not a
complete polynomial, spectrum, graph witness, or profile exclusion.
The overlap-vector mechanism was proposed by sol1 for H1/H3; this note
supplies an explicit integral basis and the owned H5/H7 consequences.

## A kernel basis valid over every residue field

Use the actual block identities of the [H5/H7 setup](Q7_H5_H7_SQUEEZE_20260910.md).
Let M be the (h+1)-by-l integer matrix formed by stacking B and the all-ones
row. Every listed support profile has an empty column and at least one
singleton column for each high. Select one of each, putting these pivot
columns first. Then M=[P F], with

    P=[I_h 0; 1_h^T 1],   det P=1.

The integer matrix

    N=[-P^(-1)F; I_(l-h-1)]

is a basis for the full lattice L=ker(M:Z^l -> Z^(h+1)). The free coordinates
give its inverse coordinate map. The same formulas hold after reduction
modulo every prime p; consequently L/pL is exactly ker(M modulo p).
There is no rank-loss or saturation assumption left unstated here.

The actual integer C satisfies

    MC=[0_(h,h) 1_h; -1_h^T 7] M.

Thus C preserves L, and CN=NR for an integer matrix R, obtained by taking
the free-coordinate rows of CN. Its characteristic polynomial is precisely
psi_h because L spans K=ker B intersect1^perp over Q. Characteristic
polynomials commute with reduction modulo p.

This explicit basis also settles the exact lattice determinant in these
profiles: det(N^TN)=det(MM^T)=7^(h-1)(343-22h-h²). The equality follows
from det P=1 and det(I+XY)=det(I+YX), or Cauchy–Binet applied to complementary
minors. The determinants are499408 for H5 and16470860 for H7. Earlier
square-class-only statements did not assert this stronger lattice identity.

## An overlap eigenvector at primes dividing the Gram determinant

Let Delta=343-22h-h² and p be an odd prime dividing Delta with p not dividing8.
In F_p^l set v=(h+7)1-8t. Exact integer identities give

    Bv=0,   1^T v=Delta,
    Cv=(49-h)1-(h+7)t.

For lambda=(h+7)/8 modulo p, the equality8(49-h)=(h+7)² modulo p gives
Cv=lambda*v. The empty and singleton coordinates differ by8, so v is
nonzero modulo p. It lies in the reduction of L by the explicit basis above.
Therefore

    psi_h(lambda)=0 modulo p.

In the owned cases this gives psi5(8)=0 modulo13 and psi7(3)=0 modulo5.
The p=7 specialization for H7 is already contained in the larger kernel
family below. These congruences use joint C/B identities, beyond mere
representability of the Gram block.

## A residual kernel modulo seven and determinant divisibility

Take a basis x_j=e_j-e_h, j=1,...,h-1, of the high-coordinate sum-zero
subspace, and put w_j=B^T x_j. Since BB^T=7I+J and B1=8·1,

    B w_j=7x_j,   1^T w_j=0,   Cw_j=0.

Modulo7 these are in ker M, hence in L/7L. They are linearly independent:
B^T is injective over F7 because the singleton columns give an identity
minor. Thus the reduction of R has kernel dimension at least h-1. It follows

    x^(h-1) divides psi_h(x) modulo7,
    7^(h-1) divides psi_h(0) in Z.

For the determinant statement, lift a basis of the mod7 kernel to the first
h-1 columns of a matrix invertible over Z7. The corresponding first h-1
columns of R times that matrix are divisible by7. Taking determinants proves
the claimed divisibility. R is nonsingular over Q by the reviewed defect
argument, so psi_h(0) is nonzero.

Consequences: psi5(0) is a nonzero multiple of2401; psi7(0) is a nonzero
multiple of117649. Using the forced A factors, det A is respectively a
nonzero multiple of44*7^8 and42*7^12. These are divisibility requirements,
not bounds excluding all possible determinants.

## Prior work and verification limits

`Erdos85OrderFortyNineDefectModSevenKernel.lean` already constructs H3
high-row-difference vectors in the mod7 kernel of the full shifted defect
matrix6I-D, and proves its fixed eigenvalue7 factor over C. The present
argument transfers the overlap into the saturated residual C-lattice. No
claim of novelty beyond that distinction is made without the prior inventory.

`verify_q7_h5_h7_residual_lattice.py` builds each exact support profile,
checks the unimodular pivot and kernel basis, computes the lattice determinant,
and verifies ranks and overlap-vector coordinates over the indicated finite
fields. It does not construct an unknown C or R; the eigenvalue and determinant
conclusions depend on the paper C-invariance argument above. No spectrum
enumeration was run.

Independent review1593 checked the full lattice/reduction argument and the
determinant valuation, then reran the four-profile verifier with its copied
incidence dependency in a private directory. This does not formalize the
argument in Lean or provide an unknown C/R matrix.
