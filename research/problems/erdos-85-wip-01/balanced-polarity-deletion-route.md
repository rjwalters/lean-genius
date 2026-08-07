# Balanced polarity deletion as a quadratic localization route

Status: exploratory.  No claim below is yet part of the verified Lean result.

## Motivation

The direct polarity-band construction uses the deterministic deletion band

\[
  q^2+d,\ldots,q^2+q
\]

of a polarity graph.  This band has lower endpoint of order `q²` but length
only of order `q`.  The interval-composition lemma therefore gives a
conductor of order `q³`.  Separately, `Erdos85QuadraticConductor` already
supplies a verified all-order conductor at `36d²` using parabola Sidon graphs
and a polarity component.  Thus balanced deletion is valuable not merely for
reaching quadratic order, but for moving the conductor close to the Moore
scale `d²` with a subquadratic error term.

Arbitrary deletion is unnecessarily pessimistic: it charges every retained
vertex one degree for every deleted vertex.  A balanced deletion set only
charges a vertex for its deleted *neighbors*.  Since a polarity graph has
degree about `q` but order about `q²`, one should be able to delete a positive
fraction of all vertices while controlling every local loss.

## Candidate probabilistic lemma

The cleanest formulation uses independent Bernoulli retention; fixed-size
sampling is unnecessary.  Choose a random retained set `R` by keeping each
vertex independently with probability `p`.  For a vertex of degree `k`, its
number of retained neighbors is binomial with mean `pk`.  A union bound over
the bad events

\[
  v\in R \quad\hbox{and}\quad |N(v)\cap R|<d
\]

together with an upper-tail bound for `|R|` gives, for suitable `A`, a set
`R` such that `G[R]` has minimum degree at least `d` and `|R| <= A`.

This single set already yields the whole interval `[A,N]`: enlarge `R` by
arbitrary omitted vertices until it has each desired cardinality.  Passing
to a larger induced subgraph cannot lower the degrees of the old vertices,
and each newly added vertex needs separate control.  To avoid that last
issue, add vertices only after first choosing a *deletion* set `D` for which
every vertex of the ambient graph has at most `k-d` neighbors in `D`.
Then every complement of a subset of `D` has minimum degree at least `d`.
Equivalently, use Bernoulli deletion and bound all neighborhood losses from
above.  This is the correct monotone formulation.

Concretely, choose every vertex for deletion with probability `rho`.  If

\[
  |N(v)\cap D|\le k-d\quad\text{for every }v
\]

and `|D| >= L`, then choosing arbitrary subsets of `D` of all sizes at most
`L` supplies the contiguous retained-order band `[N-L,N]`.

An alternative fixed-cardinality statement, useful if it gives better
constants, is as follows.

Let `G` be a `k`-regular graph on `N` vertices, and choose uniformly a set
`R` of exactly `n` retained vertices.  Conditional on `v in R`, the random
variable

\[
  \deg_{G[R]}(v)
\]

is hypergeometric with mean

\[
  \mu = k\frac{n-1}{N-1}.
\]

A hypergeometric lower-tail bound and a union bound over the vertices suggest
that an induced subgraph on exactly `n` vertices with minimum degree at least
`d` exists whenever

\[
  \mu-d \mathrel{\gtrsim} \sqrt{\mu\log N}.
\]

For a projective-plane polarity graph, `N=q²+q+1` and `k` is `q` or `q+1`
(depending on the treatment of absolute points).  Thus the expected lower
endpoint of the balanced band is

\[
  n_0 = dq + O\!\left(q\sqrt{d\log q}\right).
\]

The Bernoulli-deletion formulation gives the contiguous band from one good
deletion set, rather than requiring a separate random experiment at every
integer `n`.

## Consequence for plateau cores

Choose a prime power `q` in a constant-factor interval above `2d`.  Then

\[
  n_0 = O(d²), \qquad N-n_0 = \Theta(d²).
\]

In fact, for `q` sufficiently close to `2d`, the band length is at least a
positive constant times its lower endpoint.  Feeding `[n₀,N]` into the
existing interval-composition theorem gives another quadratic conductor,
potentially with a much smaller constant than the verified `36d²` bound.
Consequently every degree-`d` plateau core would satisfy

\[
  d(d-1)+3 \le m < C d²,
\]

This constant-factor form alone would sharpen the existing quadratic
localization; the near-diagonal choice below is the materially stronger goal.

This does not alone settle Erdős 85: the remaining window still has quadratic
width.  It does, however, put all possible cores on the same scale as the
Moore/defect identities and may make a uniform slack or packing contradiction
possible.

## Stronger near-diagonal parameter choice

The constant-factor choice `q ≈ 2d` is robust but far from optimal.  The
probabilistic estimate predicts a retained-order threshold

\[
  n_0 = dq + O\!\left(q\sqrt{d\log q}\right).
\]

Consequently one should take `q` as close to `d` as the concentration slack
and the availability of prime powers allow.  Write `q = d + g`.  Provided
`g` dominates `sqrt(d log d)`, the deletion budget `q-d=g` still leaves room
for a union-bound construction, while

\[
  n_0 = d^2 + dg + O\!\left(d^{3/2}\sqrt{\log d}
                    + g\sqrt{d\log d}\right).
\]

A quantitative prime-gap theorem of the form

\[
  q-d = O(d^\theta), \qquad \tfrac12 < \theta < 1,
\]

would therefore give

\[
  n_0 = d^2 + O(d^{1+\theta}).
\]

For example, the classical exponent `θ = 0.525` would reduce the possible
plateau-core window to

\[
  d(d-1)+3 \le m < d^2 + O(d^{1.525}),
\]

up to logarithmic and absolute-point bookkeeping terms.  This is much
stronger than a bare `O(d²)` localization: the unresolved width becomes
subquadratic.  It is also exactly the regime in which the Moore identity has
small total degree defect relative to the ambient order, so a stability or
PSD-slack argument becomes substantially more plausible.

This observation depends on two inputs that must not be conflated:

1. a sufficiently close prime or prime power `q ≥ d`, and
2. enough surplus `q-d` to absorb the simultaneous neighborhood-loss tail.

The optimal choice is therefore the first available `q` above
`d + C sqrt(d log d)`, not simply the first `q ≥ d`.

## Required checks

1. Choose the exact polarity witness (regular looped model, simple graph after
   absolute-point handling, or the already formalized free deletion graph) so
   every vertex has a clean degree lower bound.
2. First try the simpler binomial upper-tail estimate for all neighborhood
   losses and a lower-tail estimate for the total deletion-set size.
3. Verify constants ensuring the resulting deletion band has length a fixed
   positive fraction of its lower endpoint.
4. Optimize only enough to ensure `N-n₀` is comparable with `n₀`; sharp
   constants are not initially important.
5. Feed the resulting interval directly into `eventually_witness_of_interval`
   and derive a new quadratic plateau-core localization theorem.

## Possible deterministic variants

- Use an equitable or discrepancy-controlled vertex coloring and take unions
  of color classes.  This could replace probability with a reusable balanced
  induced-subgraph lemma.
- Use the polarity graph's spectral gap to derandomize conditional
  expectations.  Expander mixing controls averages, so an additional local
  discrepancy step is still needed for minimum degree.
- Apply the Lovász local lemma instead of a union bound.  This may improve the
  error term but is unnecessary for the first constant-factor quadratic
  localization.
