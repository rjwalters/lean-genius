# Extremal sign-factorization audit

Node: cap-free first positive-variance endpoint, in the permutation normal
form of `SIZE_TWO_CYCLIC_EXTREMAL_PERMUTATION_NORMAL_FORM.md`.

## Factoring the reciprocal involution

On the dart set `Cells x R`, put

```text
P(p,r) = (p, psi_p(r)).
```

Thus

```text
sign(P) = product_p sign(psi_p).
```

Write the reciprocal involution as `T=Q P`.  For fixed output label `s`, if
`r=psi_(x,t)^(-1)(s)` and `h=t+r`, then

```text
Q_s(x,t) = (x+h, -s-h).                              (1)
```

The map `Q` preserves `s`, so every `Q_s` is a permutation of the cells.

Let

```text
H_s = {h : -s-h is an allowed fibre}.
```

For every fixed base `x`, (1) implies that

```text
rho_(x,s) : t |-> t + psi_(x,t)^(-1)(s)              (2)
```

is a bijection from the allowed-fibre set `D` to `H_s`.  Indeed, two equal
values of `h` at the same `x` would give the same output cell in (1), and
both sets have size `q-2`.

Consequently `Q_s` factors as

```text
(x,t) --rho--> (x,h) --A_s--> (x+h,-s-h).
```

Relative to increasing orders on the two-hole sets,

```text
sign(Q_s) = sign(A_s) product_x sign(rho_(x,s)).      (3)
```

## The affine factor has fixed negative sign

The fibre permutation `h |-> -s-h` occurs in `q` base blocks, so its sign
contributes an even power and disappears.  Within the block indexed by `h`,
`A_s` translates `Z/q` by `h`.  For binary `q`, this translation is odd
exactly when `h` is odd.  The two deleted values defining `H_s` have opposite
parity, hence `H_s` contains `q/2-1` odd residues.  For `8 | q`, this number
is odd, and therefore

```text
sign(A_s) = -1.                                      (4)
```

There are `q-2` labels `s`, an even number.  Also the fixed-point-free
involution `T` has `q(q-2)^2/2` transpositions, an even number at binary
`q>=8`, so `sign(T)=+1`.  Combining `T=QP`, (3), and (4) yields the exact
global identity

```text
product_(p) sign(psi_p)
  * product_(x,s) sign(rho_(x,s)) = +1.              (5)
```

Equation (5) is the correct defect-compatible row/column sign interface.  It
is not an ordinary Latin-square parity formula: both index sets have two
moving holes, and the `rho` permutations arise from reciprocal base shifts.

## Two bounded cuts

First, sharpness does not determine the first product in (5).  Exhaustive
enumeration of all `6!` local permutations at q8 shows that for most fixed
triples `(t, missing fibre, doubled fibre)`, both values of `sign(psi_p)`
occur.  The two canonical repairs of the near-permutation have opposite
signs, but the triples

```text
(sign psi, sign first repair, sign second repair)
```

realize all four possible orientations in many defect profiles.  Thus no
argument multiplying a sign fixed independently at each cell can work.

Second, the one-base consequence (2) is not itself contradictory.  A direct
q8 Z3 relaxation chooses the six permutations `psi_(x,t)` at one fixed base,
imposes their sharp load profiles, and requires every map (2) to be a
bijection.  It is SAT (as are q4 and q6).  Therefore row/column parity inside
one base slice cannot prove the endpoint.

## Surviving sign target

The q8 full reciprocal normal form is UNSAT while every isolated base slice
above is SAT.  The missing information is precisely how (1) transports the
chosen permutation at base `x` to the permutation at the shifted base
`x+h`.  A viable sign theorem must compare the orientations of the
`rho_(x,s)` across those translations, or build a reciprocity-compatible
choice between the two opposite local repairs.  Equation (5) alone is an
identity, not a contradiction; replacing the translated coupling by
independent base slices is a sound falsifier and is already SAT.

## Global route sign at the q8 minimum-rank endpoint

The full Boolean probe now exposes `--global-route-sign even|odd`.  It
constructs each local permutation directly from the exact-hit edge
variables: for row and column labels `r,s in Z/q \\ {0,1}`, the target cell
is

```text
(x+t+r, -t-r-s),
```

and an XOR of all pairs `r_i<r_j`, `s_i>s_j` is its inversion parity.  The
XOR over all sources is the sign of the first product in (5).

At the cap-free minimum-rank endpoint the exact q8 verdict is

```text
a=1, sum r<=64: global route sign even SAT, odd UNSAT;
a=2, sum r<=64: global route sign even SAT, odd UNSAT.
```

Both odd-sign exclusions were independently exported through the validated
pure-Boolean DIMACS path and proved by Kissat.  Dropping reciprocity makes
the q8 a1 odd-sign query SAT immediately, so the restriction is not generic
permutation bookkeeping.  By contrast, the reciprocal odd-sign query with
no rank bound remained UNKNOWN at 120 seconds; the present evidence fixes
the sign only on minimum-rank endpoints and must not be stated for every
reciprocal routing.

The same test at the true cap-free minima of the two boundary hole phases
gives

```text
a=0, sum r<=78: global route sign even SAT, odd UNSAT;
a=3, sum r<=88: global route sign even SAT, odd UNSAT.
```

The odd exclusions again have independent validated DIMACS/Kissat proofs.
Consequently **every q8 hole placement has even global route sign throughout
its minimum-defect-rank stratum**, despite the minima `78,64,64,88` and their
load geometries being quite different.  This is substantially more stable
than an equality-at-`q^2` observation and suggests a q-generic minimum-
stratum orientation theorem.  It remains bounded evidence: neither the
minimum rank nor this sign law is yet known at general binary order.

This refines rather than closes the sign route.  The endpoint models of all
hole types already realize the required even sign, so scalar parity alone
does not contradict them.  A cap terminal must show that selecting a
cap-respecting endpoint in each reflection orbit forces the opposite sign,
or that any cap-preserving descent changes the conserved trade component.
The new diagnostic makes those two prospective claims directly falsifiable.

The grouped directed-variable cross-check also proves the a1 odd-sign
endpoint UNSAT when all 21 block-transpose assumptions are enabled.  A
bounded deletion pass retained **every** reciprocal block.  Since each
deletion was allowed only five seconds, this is a sufficient, highly
nonminimal core: a retained block may mean SAT or merely UNKNOWN after its
removal.  It nevertheless supplies no evidence for a small reflection-pair
localization of the even sign.  The observed parity is globally distributed
across the transpose system at the present resolution, so the full family
of shifted-base orientations remains the honest proof target.
