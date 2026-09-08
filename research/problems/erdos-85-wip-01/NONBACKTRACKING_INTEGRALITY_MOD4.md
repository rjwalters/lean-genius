# All-length primitive-cycle integrality is a finite mod-four test

2026-09-08, codex-sol-1, A-REG-NONBIP; follow-up to divergence #109.
Prose proof with executable checks, not Lean. No novelty claim.

## Statement

Let n and q be positive **even** integers, q>=2, and let
P(t) in Z[t] have constant coefficient 1 and degree at most n. For spectral
applications P(t)=det(I-tA), the reciprocal characteristic polynomial.
Put s=q-1, m=nq/2, and define the formal Ihara polynomial

    F(u)=(1-u²)^(m-n) (1+s*u²)^n P(u/(1+s*u²)).

Define T_l by -log F(u)=sum_(l>=1) T_l*u^l/l and define

    C_l = (1/(2l)) sum_(d|l) mu(l/d) T_d.

For an actual simple undirected q-regular graph these are primitive
cyclically nonbacktracking walk counts up to rotation and reversal, as
in `NONBACKTRACKING_POSITIVITY_AUDIT.md`. The determinant identity is
the regular case of [Rangarajan, Theorem 2, PDF page 3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol093-fsttcs2017/LIPIcs.FSTTCS.2017.46/LIPIcs.FSTTCS.2017.46.pdf).
Here neither graph realization nor real eigenvalues are assumed.

The following are equivalent:

1. C_l is an integer for **every** l>=1.
2. P(t) is a square in Z[[t]], with square root of constant coefficient 1.
3. Writing P(t)=sum p_j*t^j and
   R(t)=sum_(j=0..floor(n/2)) (p_(2j) mod 2)*t^j, one has
   **P(t) = R(t)² modulo 4**, coefficientwise.

Thus the all-length integrality test requires only the finite list of
characteristic coefficients modulo four. For binary square order q>=8,
the companion positivity result already supplies nonnegative formal C_l.
Passing the present test still does not supply a graph realization.

## Proof

Every integer unit series F in 1+uZ[[u]] has a unique Euler expansion

    F(u)=product_(l>=1) (1-u^l)^b_l,   b_l in Z.

This follows recursively: after fixing all lower factors, choose the
integer b_l to cancel the coefficient at degree l. Negative exponents
also give integer series; each fixed coefficient uses finitely many
factors. Taking a formal logarithm gives T_l=sum_(d|l) d*b_d;
Möbius inversion gives b_l=2C_l. By uniqueness of Euler expansions,
all b_l are even exactly when F is the square of an integer unit series.

Now m-n=n(q/2-1) is even, as is n. Both displayed prefactors in F are
squares of integer unit series, so they can be removed without changing
whether F is a square. The substitution phi(u)=u/(1+s*u²) is an
automorphism of integer formal series: its inverse psi(t) is determined
recursively by psi=t(1+s*psi²), with linear coefficient 1 and integer
coefficients at every degree. Consequently P(phi(u)) is a square if and
only if P(t) is a square. This proves (1) iff (2).

If P=H² with H in 1+tZ[[t]], Frobenius modulo two says that all odd
coefficients of P vanish modulo two and H=R modulo two. (Coefficients
of P beyond its degree are zero.) Thus H=R+2K for an integer series K,
and P=R² modulo four.

Conversely suppose P=R²+4J for J in Z[t]. Both P and R have constant
coefficient 1, hence J(0)=0 and R is invertible in Z[[t]]. Then

    sqrt(P)=R * sqrt(1+4J/R²)

is an integer unit series: the coefficients of sqrt(1+4z) beyond its
constant term are 2*(-1)^(j-1)*Catalan_(j-1), all integers. Substitution
is legitimate because J/R² has zero constant term. This proves (3)
implies (2). Since deg R²<=n, condition (3) is finite.

## Relation to the already-recorded walk congruences

Sol3 independently supplied the following comparison. Impose the additional
graph moments a_1=0 and a_2=nq, where -log P(t)=sum a_j*t^j/j.
Let b_k=(1/k)sum_(d|k) mu(k/d)a_d. These are integers by the same Euler
expansion argument. The divisor identity sum_(e|r) phi(e)=r gives

    (1/N) sum_(d|N) phi(N/d) a_d = sum_(k|N) b_k.

The all-length Harary--Schwenk rotation/reversal congruences, already cited
in `NONBIP_CONNECTED_ODD_POWER_MOD4_AUDIT.md`, consequently require the
right side to be even. For even N their extra reflection term, divided
by 2N, is nq^(N/2)/4, an integer because n and q are even. For odd N
there is no reflection term. The source is
[Harary--Schwenk, Corollary 5a, page 448](https://msp.org/pjm/1979/80-2/pjm-v80-n2-p15-s.pdf).

Their stated N>=3 range loses nothing here: b_1=0 and b_2=nq/2 are
already even. Divisor induction shows that every sum_(k|N)b_k is even
if and only if every b_k is even, equivalently P is an integer-series
square. Thus, **under these low-moment assumptions, all-length primitive
nonbacktracking integrality is exactly the all-length classical walk
congruence family**, not a new independent restriction. The finite
mod-four criterion evaluates that entire family at once; the previously
used length-six test alone is not asserted to imply it.

## Calibration and limits

`verify_nonbacktracking_integrality_mod4.py` constructs characteristic
coefficients from exact adjacency moments for the actual 16-vertex q4
control. It passes the finite mod-four criterion. The already-excluded
q16 unpaired ledger fails it. Independently calculated primitive counts
recover its first failure at length 6; this is not a new exclusion of
that ledger.

Small integer polynomials, including ones with no real spectral
interpretation, cross-check the algebra against exact rational square-root
coefficients and Ihara trace counts. These finite checks calibrate the
implementation; the all-length equivalence is the proof above.

This does not show that all primitive-cycle integrality conditions follow
from one low-order trace congruence, nor that mod-two characteristic data
suffice. For example P=1+2t⁴ is a square modulo two but fails condition
(3). Its rational square root has an integer coefficient at degree 4 and
a half-integer at degree 8, illustrating why a short prefix can miss an
obstruction. This example is an algebraic control, not an A-REG spectrum.

The next useful spectral check is the finite mod-four criterion on any
otherwise surviving integer characteristic polynomial. Repeatedly extending
the list of cycle lengths adds no stronger condition once it passes.
No A-REG theorem or graph-existence claim is promoted.

Independent proof review: Codex subagent `review_integrality`; Squad review
#1477 PASS from Sol3, who independently derived the classical-walk
comparison above and checked 4095 additional residue polynomials.
These are prose reviews, not machine verification.
