# Translation-averaged trace-moment lift

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## The scope problem

The reduced translation-invariant probe identifies all simultaneous base
translates of one edge with a single Boolean `E(t,u,r)`.  An arbitrary Lean
code instead has base-resolved indicators

```text
K(x,t; x+r,u) in {0,1}.
```

There is no known symmetrization that turns an arbitrary code into a
deterministic TI code while preserving the quadratic caps.  Averaging edge
indicators and then multiplying them introduces cross-translate terms that
were not common-target events in the original code.

The colored trace separator suggests a more precise lift: average the
*monomials*, not the edge variables.

## Cyclic averaging of local monomials

For any polynomial monomial `m(K)` in finitely many base-resolved edge
indicators, define its orbit average

```text
Avg(m) = (1/q) sum_(h in Z/q) m(translate_h K),
```

or use the division-free orbit sum in Lean.  Translation permutes the base
coordinates and preserves difference-fibre colors.

The exact hypotheses have translation-stable moment forms:

1. **Row and column hits.**  These are pointwise linear equations, hence
   remain exact after summing over `h`.
2. **Empty diagonal block.**  Every translated internal-edge indicator is
   zero, so every moment containing one is zero.
3. **Full caps.**  For fixed source base pair and fibre, the sum of the
   degree-two common-target monomials is at most one.  Summing this inequality
   over all translates preserves it exactly.
4. **Trace reversal.**  A colored triangle or four-cycle orbit sum is a sum
   of degree-three or degree-four closed-walk monomials.  Route reversal is a
   bijection from every such walk to the reversed color word, so reciprocity
   proves equality of the orbit sums without translation invariance.
5. **Booleanity.**  `K_e^2=K_e` remains available before averaging and can be
   used inside each local monomial reduction.

Thus a certificate that is a linear combination of translation-orbit sums
of local monomials and pointwise nonnegative cap slacks can lift verbatim to
the arbitrary base-dependent code.

## The invalid factorization to avoid

In a TI deterministic model one writes a single Boolean `E(t,u,r)`.  If

```text
p(t,u,r) = Avg(K(x,t;x+r,u)),
```

then in a general code

```text
Avg(K_e K_f) != p_e p_f
```

in general.  The left side is a joint orbit moment; the right side is a
product of marginal densities.  Any proposed identity that factors a
colored trace or cap term into products of averaged first moments is confined
to the TI ansatz and cannot prove the Lean theorem.

This includes ordinary group-ring multiplication of the averaged adjacency
coefficients unless each coefficient product is explicitly interpreted as a
joint translated-edge moment.  The same warning applies to PSD arguments on
the averaged adjacency matrix: convex averaging preserves PSD of Gram
matrices, but `Avg(K) Avg(K)^T` is not `Avg(K K^T)`.

## Why the T3/T4 interface is liftable

For example, the arbitrary-base colored triangle count is

```text
sum_(x,r,s)
  K(x,t; x+r,u)
  K(x+r,u; x+r+s,v)
  K(x+r+s,v; x,t).
```

Simultaneously translating `x` merely permutes its summands.  Transposing
the three actual edges reverses the walk and proves the `T3(t,u,v)` reversal
identity.  The four-cycle expression behaves identically.  No product of
averaged marginals is used.

The TI convolution formulas are the specialization in which each translated
edge indicator is equal.  They are a convenient discovery representation,
not the definition needed for the proof.

## Certificate criterion

A computational or algebraic trace certificate is eligible for promotion to
the general theorem only if it can be written in the form

```text
constant contradiction
  = sum orbit-averaged hit equalities
  + sum coefficients * orbit-averaged T3/T4 reversal defects
  + sum nonnegative multiples of orbit-averaged cap slacks
  + sum Boolean reductions local to one translate.
```

It is ineligible if it uses:

- multiplication of two orbit-averaged first moments;
- a deterministic choice of representative edge for an orbit;
- circulant commutativity not expressible by reindexing actual closed walks;
  or
- a factorization/rank property of the averaged edge-density matrix.

This gives a concrete audit for an SOS/Positivstellensatz search.  Export the
certificate in local edge monomials with translation-orbit coefficients;
then every term has a direct base-resolved interpretation and a plausible
Lean statement.

## Consequence

Translation averaging does not prove the packing bound by itself, but it
removes the apparent gap between the TI trace experiment and arbitrary
blocks for the right class of certificates.  The live next object is not a
TI code; it is a degree-at-most-four cyclic moment functional satisfying the
hit, empty, cap, Boolean, and reversal relations above.

The q8 leave-one-color controls say any certificate in this class must use
the full allowed-fibre sum.  The empty-fibre SAT control says its constant
term must also depend essentially on the zero diagonal moment.  These are
testable structural requirements for the certificate rather than post-hoc
scope caveats.
