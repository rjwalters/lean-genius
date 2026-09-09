# Integral-module reformulation: the missing weaker condition

The round-114 arithmetic proposal has not supplied a new obstruction. The
exact integral-module formulation with its metric and distinguished vector
retains the entire graph-existence problem. This is a formulation/source
gate, not a theorem ruling out all arithmetic approaches.

Let D be a simple (q-1)-regular graph on n=q^2 vertices and put
M=(q-1)I+J-D. Thus M_ii=q and every off-diagonal entry is 0 or 1.

Suppose an integral symmetric matrix T satisfies T^2=M and T1=q1. For
every row i,

    sum_j T_ij(T_ij-1) = (T^2)_ii - (T1)_i = q-q = 0.

Each summand is nonnegative for integer T_ij. Hence every entry is 0 or 1.
If additionally trace(T)=0, all diagonal entries vanish. Off-diagonal
entries of T^2 are at most 1, so the resulting simple graph is C4-free,
and its degree is q. Conversely, any such graph with defect D supplies T.

Consequently requiring the standard lattice Z^n to carry a self-adjoint
action of

    R[t]/(t^2-M),  R=Z[M],

extending its given R-action, with t1=q1 and trace(t)=0, is equivalent to
the original fixed-D graph problem. The coefficient ring must be R, not
Z with an unexplained matrix coefficient. The vector 1 and the standard
bilinear form are part of the data; omitting either changes the problem.

## What the checked literature supplies

Knight--Stasinski, *Representatives of similarity classes of matrices over
PIDs corresponding to ideal classes*, describes the Latimer--MacDuffee
correspondence for irreducible characteristic polynomial and provides
representatives close to companion form under a maximal-order hypothesis
(Introduction and Theorem 5.2):
https://arxiv.org/html/2205.02094v2

Zhu, *Similarity of Matrices over Dedekind Rings*, extends the correspondence
and studies descent of similarity (v4 abstract/introduction):
https://arxiv.org/html/2405.08501v4

These are similarity/module classification results. Applying them does not
by itself classify roots self-adjoint for the fixed standard form and with
the fixed vector 1. Even symmetry is not preserved by a general integral
similarity: S=[[1,1],[1,0]] and P=[[1,2],[0,1]] give

    P^-1 S P = [[-1,-1],[1,2]],

which is not symmetric, although the irreducible characteristic polynomial
t^2-t-1 is preserved. Transporting the metric repairs self-adjointness but
retains extra lattice data that the graph problem requires. No conclusion
about arbitrary D follows just from this correspondence or from frequencies
of success on random D.

To reopen this proposal, specify a necessary condition on those lattice
data that is genuinely weaker than existence of T, prove it for every
graph-derived D, and show how it contradicts an unbounded defect class.
The current proposal has not supplied that condition. Existing rational
isometry and trace-factor tests remain available with their recorded scopes.
