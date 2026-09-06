# A monotone scalar control for the Ramsey functional shortcut

Date: 2026-09-06. Node: root-level alternative to A-REG, attempting to
force infinitely many drops directly from Ramsey functional inequalities.
Status: this particular shortcut is insufficient. No graph realization,
eventual-monotonicity theorem, or resolution of Erdős 85 is claimed.

## Inputs being tested

Write R(s)=R(C4,K1,s), to distinguish the Ramsey function from the
minimum-degree forcing function h(N) in Erdős 85. Boza's
[arXiv:2409.12770v2](https://arxiv.org/pdf/2409.12770v2) gives:

- Lemma 1: R(s)-R(s-1)<=2.
- Corollary 3: R(s)<=s+ceil(sqrt(s-1))+1 for s>=2.
- Theorem 4: R(m²+3)<=m²+m+4 for m>=8, m=2 modulo 6.
- Theorem 6: R(a)>=a+b or R(a+b)<=a+2b for positive a,b.
- Corollaries 7 and 8: R(2s-R(s)+1)>=s and
  R(R(s)+1)<=2R(s)-s+2, when the arguments are positive.

The known binary q-regular C4-free graph on q²-1 vertices additionally
gives R(q²-q-1)>=q², equivalently h(q²-1)>=q+1.
The test below concerns these numerical inequalities and witness bounds.
It does not encode every finite Ramsey value or every graph-theoretic
constraint. In particular, its Corollary 3 comparison is eventual, not
an assertion at the exceptional small inputs 2 and 5.

## Explicit model and inverse relation

For N>=3 and s>=1 define

```text
mu*(N) = floor(sqrt(N+1)),
h*(N)  = mu*(N)+1,
d(s)   = min {d>=1 : d(d-1)>=s+2},
R*(s)  = s+d(s).
```

The function h* is monotone. Also N-mu*(N) is nondecreasing, since
mu* increases by at most one between consecutive integers. The threshold
relation is exactly

```text
R*(s) = min {N>=3 : mu*(N)<N-s}.
```

Indeed the inequality requires N>s; writing N=s+d gives
`floor(sqrt(s+d+1))<d`. This is equivalent to
`s+d+1<d²`, and, by integrality, to `s+2<=d(d-1)`.
For positive s its first solution has d>=3 and N>=4, so the domain
restriction causes no exception. Thus R* and h* have the same inverse
threshold relationship as the two graph parameters, while h* has no drops.

As s increases by one, d(s) stays fixed or increases by one. Consequently
`R*(s+1)-R*(s)` is 1 or 2. This supplies strict monotonicity of R* and
the increment upper bound.

## The functional inequalities hold uniformly

Suppose the first horn of the dichotomy fails, so d(a)<b. Then

```text
a+2 <= d(a)(d(a)-1) <= (b-1)(b-2).
```

Here b>=4. Adding b yields

```text
a+b+2 <= (b-1)(b-2)+b <= b(b-1).
```

Hence d(a+b)<=b and R*(a+b)<=a+2b. Theorem 6 therefore holds
for every positive a,b in this scalar model.

For completeness the two corollaries also have direct checks. Put d=d(s).
Minimality gives `s>=(d-1)(d-2)-1`. If a=s-d+1>=1, then

```text
a+2 >= (d-2)² > (d-2)(d-3),
```

so d(a)>=d-1 and R*(a)>=s. This proves Corollary 7. For Corollary 8,
`s+2<=d(d-1)` gives

```text
(R*(s)+1)+2 = s+d+3 <= d²+1 <= d(d+1).
```

Thus d(R*(s)+1)<=d+1 and the required upper bound follows.

## General upper bounds and the square anchors

For s>=6 put r=ceil(sqrt(s-1)), so r>=3. Then

```text
s+2 <= r²+3 <= r(r+1).
```

Therefore d(s)<=r+1 and the Corollary 3 bound holds at every s>=6.
Likewise d(m²+1)<=m+1 for m>=3, giving the usual square-input
upper bound. Finally, if m>=5, then
`(m²+3)+2<=m(m+1)`, so R*(m²+3)<=m²+m+4. This is stronger
in its range than the particular congruence-restricted Theorem 4 input.

For every integer q>=3, direct comparison with d=q and d=q+1 gives

```text
d(q²-q-1)=d(q²-q)=q+1,
R*(q²-q-1)=q²,
R*(q²-q)=q²+1,
h*(q²-1)=h*(q²)=q+1.
```

Thus all the binary square-minus-one witness bounds hold, with equality
in their Ramsey formulation. Nevertheless the model has no drop at any
square, or anywhere else. The numerical data being tested do not prohibit
the next square-order witness; excluding it requires an additional input.

## Verification and stopping point

An independent integer-arithmetic calibration checked the inverse relation
through N=500; both corollaries and increment/upper bounds through s=2000;
the dichotomy for all 250,000 pairs 1<=a,b<=500; and square anchors through
q=1000. The proof above supplies the uniform result, not those checks.

This is a scalar countermodel to an implication from the listed numerical
inputs. It is not a C4-free graph family and does not assert that the true
Ramsey function equals R*. It also does not claim to match the known finite
table. The functional shortcut stops here: a new structural restriction,
or a genuinely stronger numerical theorem that this model violates, is
needed before it can force infinitely many drops. No Lean wrapper or
larger finite search is warranted by this control alone.
