# Proposed exclusion of the last N80/m20 quotient (internal2, cross124)

This proposed paper proof uses accepted2147's necessary quotient. No solver or CNF change is involved. Label the four20-vertex cyclic orbits so their degree matrix is

```
2 1 2 4
1 2 4 2
2 4 2 1
4 2 1 2
```

## 1. Saturated blocks and a parity observation

The off-diagonal entries of Q² at pairs12,14,23,34 are20. Thus all corresponding adjacency-square blocks are J20, since C4-freeness permits at most one two-step path to each of the20 target vertices.

For any fixed orbit, the number of nonreturning two-step paths ending in the same orbit is (Q²)ii-9=25-9=16. Their16 offsets are distinct nonzero residues modulo20 and closed under negation. The three missing nonzero residues must therefore be10 and a pair ±t. Among the ten odd residues either zero or two are missing; the number of odd two-step offsets is8 or10.

The two internal-shift paths have offsets ±2s and are even. The size-one cross-offset set contributes none. If the size-two cross-offset set has both offsets of the same parity, it contributes no odd difference. The size-four cross-offset set, with r odd offsets, contributes2r(4-r) odd differences, in{0,6,8}. In the same-parity size-two case this must be8, so r=2. We will use: **if a degree-two cross-offset pair has the same parity, the corresponding degree-four set has two even and two odd offsets.**

## 2. Two Fourier evaluations

For any nontrivial20th root z, write the Hermitian Fourier adjacency in orbit order(1,3 | 2,4) as

```
H = [ L  X  ],   L = [ a1 c  ],  R = [ a2 d  ],  X = [ p q ].
    [ X* R ]        [ c* a3 ]      [ d* a4 ]        [ r s ]
```

Here ai=z^si+z^-si are internal entries; c,d are sums of two powers; p,s are single powers; q,r are sums of four powers. Cross-block saturation gives

    L X + X R = 0.

At z=-1, p,s are ±1, q,r are even integers, so det X=ps-qr is odd and nonzero. At z=i, p,s are Gaussian units. Each sum of four Gaussian units is divisible by pi=1+i, hence qr is divisible by pi while ps is not; det X is again nonzero. Therefore at both evaluations L is similar to -R, giving

    tr L = -tr R,    det L = det R.

At -1 every ai is ±2. The trace identity forces exactly two plus signs and two minus signs. Accordingly a1*a3=a2*a4 (both4 if each half has constant sign, both-4 otherwise). The determinant identity then forces c²=d²: c,d are either both zero or both in{±2}.

## 3. Mixed signs within each half

Write the diagonals at -1 as L:(a,-a), R:(b,-b), where a,b∈{±2}.

If c,d are nonzero, their degree-two offset sets have same-parity offsets. Section1 gives q=r=0 at -1. The11 entry of LX+XR then gives (a+b)p=0, hence b=-a.

If c=d=0, the same11 equation gives b=-a, and the12 and21 equations force q=r=0 because a-b=2a is nonzero.

Thus in either subcase the internal shifts of orbits1 and2 have opposite parity, and each degree-four cross set is balanced (two even, two odd offsets). At z=i, a1+a2 is consequently ±2; p is a Gaussian unit; c,d are divisible by pi; and q,r are divisible by2, since balanced offset parity makes their real and imaginary parts even.

The11 equation is

    (a1+a2)p + c*r + q*conjugate(d) = 0.

The last two terms are divisible by2*pi, but the first is ±2 times a Gaussian unit and is not. Contradiction.

## 4. Constant sign within each half

One half has two even internal shifts and the other has two odd shifts. Interchange halves if necessary so L is the even half. At i its two diagonal entries are in{±2}, while both diagonal entries of R vanish.

If c=d=0 at -1, each size-two offset set has one even and one odd offset. At i both |c|² and |d|² equal2. The determinant identity gives

    a1*a3 - 2 = -2,

which would require a1*a3=0, impossible.

If c,d are both nonzero at -1, each size-two offset set has same-parity offsets. At i, c,d are divisible by2. Section1 makes q,r balanced and hence also divisible by2. In the11 equation the last two terms are divisible by4, whereas (a1+a2)p is ±2 times a Gaussian unit and is not. Contradiction.

All sign cases are exhausted. Therefore this last quotient cannot lift to a C4-free graph. Subject to independent review, combining this with2148 and the first-pattern exclusion2149 would exclude the full N80/minimum-degree9/free-Z20 class. It would not exclude other cyclic actions, all N80 graphs, or Erdős85 globally; this is not a Lean theorem or SAT verdict.
