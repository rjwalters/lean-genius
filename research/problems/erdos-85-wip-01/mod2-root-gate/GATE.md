# Characteristic-two square-root source gate

Status: prose derivation for review, not a new A-REG obstruction or Lean result.

Let M be a symmetric zero-diagonal matrix over F2 with M1=0. In the
Erdos85 binary setting, M=I+J+D has these properties because n=q squared
is even and D is (q-1)-regular. The necessary test is whether M=A squared
for a symmetric zero-diagonal A over F2.

## Two constraints that do not add independent tests

For symmetric A, (A squared)_ii=sum_j A_ij squared=sum_j A_ij over F2.
Thus if A squared=M and diag M=0, A1=0 automatically. A separate marked
row-sum constraint adds nothing at this stage.

The standard unit form b(x,y)=x transpose y satisfies b(x,x)=b(x,1).
Consequently any isometry P of that form fixes 1: for all x,
b(Px,P1)=b(x,1)=b(x,x)=b(Px,Px)=b(Px,1), and nondegeneracy gives P1=1.
Thus marking 1 also adds nothing to the orthogonal conjugacy problem.
Zero diagonal of A remains essential: A=J in even dimension has A squared=0
and A1=0, but all its diagonal entries are 1.

## Semisimple matrices automatically pass this test

**Lemma.** If the minimal polynomial of M is squarefree, then there is a
symmetric zero-diagonal A over F2 with A squared=M (and A1=0).

The algebra F2[M] is a product of finite fields, since its defining minimal
polynomial is squarefree. Frobenius squaring is an automorphism of this
algebra, so there is a polynomial p with p(M) squared=M. Since M1=0 and
1 is a nonzero vector, zero is an eigenvalue. Evaluation at zero in the
algebra gives p(0) squared=0, hence p(0)=0. Take A=p(M).

Every positive power of M is symmetric and zero-diagonal. For an odd
power 2r+1, b(x,M^(2r+1)x)=b(M^r x,M M^r x)=0 because M is alternating.
For an even positive power 2r,
b(x,M^(2r)x)=b(M^r x,M^r x)=b(M^r x,1)=b(x,M^r1)=0.
A polynomial with zero constant term is therefore symmetric and alternating,
so A has the required properties. Its row sums vanish as well.

This is a sufficiency statement about the modular relaxation, not an
example of a graph-derived M passing all the existing real/integer tests.
It shows that a universal modular exclusion would in particular need to
rule out semisimple M among the candidate defect graphs. No such graph
structural theorem is supplied here. The unresolved form classification
can only add an obstruction on nonsemisimple M.

## Primary source inspected and stopping decision

Gregory Berhuy, Minimal and characteristic polynomials of symmetric matrices
in characteristic two, arXiv:2106.10239v2 (16 November 2021):
https://arxiv.org/pdf/2106.10239

Theorem 1.1 and Corollary 1.2 (printed page 3) allow every monic polynomial
over a perfect characteristic-two field. Lemma 2.1 (printed page 4) builds
symmetric multiplication matrices using a transfer form isometric to the
unit form. Thus it would be inaccurate to describe this as just ordinary
similarity with no bilinear form. However the stated results do not solve
the zero-diagonal square-root problem for a prescribed M. The theorem is
not a source of an additional characteristic-polynomial obstruction over F2.

The semisimple lemma above is an independent elementary derivation; no
claim of novelty is made. Stop the proposed direct import of Berhuy's
polynomial theorem. A later form-preserving primary-space classification
would still require a graph-side argument applicable to every remaining D.
No finite candidate search was run, and no universal exclusion is claimed.
