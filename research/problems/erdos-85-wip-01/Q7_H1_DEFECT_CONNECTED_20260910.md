# H1 defect connectivity from an integer component quotient

2026-09-10, codex-sol-1. **Independent paper review #1589 PASS (codex-sol-2).** The argument proves that D is connected for h1; it does not exclude the connected H1 case or solve Erdős85. It uses the actual joint C/D identities, not Gram representability alone.

## Component basis

Use the h1 setup in `Q7_H1_H3_SQUEEZE_20260910.md`. There are eight low vertices N with t=1, forty with t=0, and Ct=1. Every D component S_i contains k_i vertices of N and5k_i empty-support vertices, with k_i positive even and sum k_i=8. Thus each component has vertices of both types.

Let a>6 solve a²-7a+1=0, put b=7-a=1/a and rho=a-1. The vectors z_i=a1_(S_i)-t restricted to S_i form a basis over Q(a) of the rho eigenspace of D. Their norms are

```
||z_i||² = k_i(6a²-2a+1) = k_i(40a-5).
```

Their sum z satisfies Cz=az. Since CD=DC, write the matrix of C on this component basis as Q, with convention C z_j=sum_i Q_ij z_i.

## Integer coefficients force two involutions

For an empty-support vertex x in S_i, write X=|N_C(x) intersect S_j| and Y=|N_C(x) intersect N intersect S_j|. Evaluating C z_j at x gives

```
Q_ij = (aX-Y)/a = X-7Y+aY.
```

Because a is irrational, the integer coefficients X,Y are the same for every such x in S_i. For a support-one vertex x' in S_i, define X',Y' analogously. Evaluating at x' gives

```
aX'-Y' = Q_ij(a-1) = a(X-Y)-X+6Y,
```

so X'=X-Y and Y'=X-6Y. Hence X=6Y+Y' and

```
Q_ij = rho Y + Y'.
```

The identity Ct=1 means each vertex has exactly one C neighbor in N. Consequently F_ij=Y and H_ij=Y' define0/1 matrices F,H with exactly one1 in each row, and Q=rho F+H.

Selfadjointness for the component Gram matrix diag(k_i(40a-5)) gives k_i Q_ij=k_j Q_ji. Irrationality of rho separates this into k_i F_ij=k_j F_ji and the analogous identity for H. Each chosen arrow must therefore have its reverse, and its endpoint weights are equal. Thus F and H are permutation matrices of involutions, preserving k: F²=H²=I. Fixed points are allowed.

## Squaring the quotient

The orthogonal complement to z in the rho eigenspace lies in K=ker(B) intersect1-perp, by the already-reviewed block argument. Therefore C²=bI on that complement and C²z=a²z. The orthogonal projector onto z has component matrix 1*k^T/8, since the component norms are proportional to k_i. Thus

```
Q² = bI + (a²-b)1*k^T/8 = bI + rho 1*k^T.
```

On the other hand Q=rho F+H and rho²-5rho-5=0 give

```
Q² = (rho²+1)I + rho(FH+HF),
6I+FH+HF = 1*k^T.
```

Taking diagonal entries forces k_i>=6 for every component. Since sum k_i=8, there cannot be two components. Thus D is connected. The reviewed even-bipartite-component-count lemma then also makes D nonbipartite.

## Verification scope

`verify_q7_h1_component_quotient.py` checks the quadratic-field identities and exhausts the finite involution/positive-even-weight systems for1..4 components and total weight8. Only the one-component system remains. This is a check of the quotient constraints, not a graph construction or a formal graph-to-quotient proof. The elementary diagonal argument above avoids relying on enumeration for the general contradiction. No novelty claim is made pending prior-work comparison.
