# Circulant coherent-factorization augmentation audit

Node: `A-REG-NONBIP / all size-two / circulant ansatz`; divergence round 103.

Status: exact characteristic-two filtration isolated; its first tropical
layer has a uniform escape, so a successful 2-adic consumer must retain unit
coefficients beyond the valuations.

## Group-ring form

Put `n=2q=2^(k+1)` and `r=q/2`.  In the circulant ansatz a two-regular block
is represented by a two-set `A_ce={a_ce,b_ce}` in `Z_n` and the polynomial

```text
f_ce(x)=x^a_ce+x^b_ce.
```

Reciprocity is `f_ec=f_ce^*`, where the involution sends `x` to `x^(-1)`.
For distinct colors `c,d`, coherent factorization of the complete tile
partition is exactly

```text
sum_e f_ce f_de^* = 1+x+...+x^(n-1).                  (1)
```

The diagonal self-indexing condition is

```text
f_cc=x^s_c+x^(-s_c).
```

This audit concerns only this circulant restriction; no normalization theorem
puts an arbitrary all-size-two family into this form.

## Exact augmentation valuation

Reduce (1) modulo two and write `x=1+t`.  Since `n` is a power of two,

```text
F_2[Z_n] = F_2[t]/(t^n),
1+x+...+x^(n-1) = t^(n-1).                            (2)
```

For a genuine two-set with cyclic separation `delta=a-b != 0`, let
`alpha(delta)=2^v2(delta)`, where the valuation is taken for the representative
modulo `n` and hence `alpha(delta)<=n/2`.  Then

```text
v_t(x^a+x^b)=alpha(delta).                            (3)
```

Indeed, write `delta=2^j m` with `m` odd.  In characteristic two,

```text
1+x^delta = (1+x^m)^(2^j),
```

and `1+(1+t)^m` has a simple zero at `t=0`.  Multiplication by the unit
`x^b` and the reciprocal involution do not alter the valuation.

Consequently the `e`-summand in (1) has valuation

```text
w_e(c,d)=alpha(a_ce-b_ce)+alpha(a_de-b_de),           (4)
```

unless the sum reaches `n`, in which case that product vanishes in the
truncated binary group ring.

## Tropical cancellation law

Every nonzero summand in (1) has leading `t`-coefficient one after its
valuation is removed.  Comparing with (2) gives the following necessary
condition for every pair `c!=d`:

- if `m=min_e w_e(c,d)<n-1`, the number of indices attaining `m` is even;
- if the first uncancelled degree is `n-1`, its coefficient is odd;
- after the minimum cancels, the unit coefficients of the tied summands
  determine the next degree.  Valuations alone do not determine this cascade.

The weight matrix is symmetric by reciprocity.  On the diagonal its entries
come from separation `2s_c`, so they are at least two (and are powers of
two).  This is an exact ultrametric shadow of the strong difference system.

## Uniform escape from the valuation layer

The tropical condition is not an obstruction.  Assign

```text
alpha_ce=1  for c!=e,
alpha_cc=2.
```

This corresponds to every off-diagonal two-set having odd separation and
every diagonal inverse pair having separation congruent to two modulo four.
For a row pair `c!=d`, the weights (4) are

```text
2, repeated r-2 times,       and
3, repeated twice.
```

For binary `q>=8`, `r=q/2` is even, so both multiplicities are even.  The
leading valuation layers can cancel exactly as required.  The same parity
pattern also clears the order-two character equations: the off-diagonal
Fourier entries vanish while the diagonal entries are `+/-2`.

Therefore neither the dyadic separation weights, their minimum-pairing law,
nor the order-two character quotient alone can exclude the circulant system.
The first higher unit coefficient, however, already eliminates this uniform
escape as soon as there are three colors.

### The first lifted coefficient kills the uniform pattern

Assume the displayed pattern: every off-diagonal separation is odd and every
diagonal separation has valuation exactly two.  For `c!=e`, write

```text
f_ce = t (1 + lambda_ce t + O(t^2)),
```

with `lambda_ce in F_2`.  If `f_ce=x^a+x^b`, reciprocity gives

```text
f_ec=f_ce^*=x^(-a-b)f_ce.
```

Since `a-b` is odd, `a+b` is odd, and
`x^(-a-b)=1+t+O(t^2)`.  Hence

```text
lambda_ec=lambda_ce+1.                                (5)
```

Put `L_c=sum_(e!=c) lambda_ce`.  In the row-pair equation for `c!=d`,
the `r-2` ordinary columns have valuation two.  Their leading coefficients
cancel because `r` is even.  The two endpoint columns have valuation three
and leading coefficient one each, so they also cancel.  The remaining
coefficient of `t^3` is

```text
sum_(e!=c,d) (lambda_ce+lambda_ed)
  = L_c+L_d+lambda_cd+lambda_dc
  = L_c+L_d+1,                                        (6)
```

where the even value of `r-2` and (5) were used to convert the column sum to
a row sum.  The right side `t^(n-1)` has zero `t^3` coefficient for `n>=8`,
so (6) forces

```text
L_c+L_d=1                 for every c!=d.              (7)
```

Three binary values cannot be pairwise distinct: from the equations for
`(c,d)` and `(c,e)` one gets `L_d=L_e`, contradicting the equation for
`(d,e)`.  Thus:

> A symmetric circulant strong-difference system with at least three colors
> cannot have every off-diagonal two-set of odd separation and every
> diagonal inverse pair of separation `2 mod 4`.

This is the first genuine obstruction from the lifted augmentation
filtration.  It explains the `q=4` calibration sharply: two colors can
satisfy (7), whereas every binary `q>=8` has `r=q/2>=4`.

It does **not** eliminate mixed valuation patterns.  A general surviving
augmentation proof must compute higher unit coefficients of

```text
t^(-alpha(delta)) (1+(1+t)^delta),
```

and propagate them through the strata of entries attaining each minimum.
Calling the valuation pattern alone an ultrametric obstruction would still
overstate the result.

## `q=4` calibration

The exact cyclic system is already feasible at the mandatory exception.
Over `Z_8`, with two colors, one solution is

```text
A_00={1,7},       A_01={0,1},       A_11={3,5},
A_10=-A_01.
```

The two via difference multisets are the disjoint four-sets

```text
{0,1,2,7},        {3,4,5,6},
```

which partition `Z_8`.  A direct exhaustive calibration finds 32 labeled
triples `(A_00,A_01,A_11)` satisfying the equation.  Thus the circulant ansatz
contains, rather than accidentally excludes, the small binary exception.

## Honest next statement

The remaining restricted target is a lifted group-ring theorem:

> For `k>=3`, no symmetric array of two-monomial polynomials over
> `Z[Z_(2^(k+1))]` with inverse-pair diagonal can have every distinct-row
> inner product equal to the all-ones group-ring element.

The present audit proves the exact valuation input, shows that its first
tropical consequence is insufficient, and then uses the first lifted unit
coefficient to kill the uniform minimal-valuation escape.  A next probe should
stratify mixed dyadic separations and ask whether the same row-sum obstruction
propagates inside a minimum-weight class, or construct a q-generic symmetric
strong-difference array.  It should not repeat the valuation-only layer.
