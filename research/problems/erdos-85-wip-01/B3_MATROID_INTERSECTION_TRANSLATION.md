# B.3 canonical separation is matroid intersection

Date: 2026-08-24

Owner: codex-sol-2

Scope: goal #36, B.3 generic transfer; outside-first literature verdict

## Verdict

The directed fractional system (12g) in
`B3_HOLE_PARTITION_OBSTRUCTION_AUDIT.md` is an ordinary common-base problem
for two matroids.  Its canonical antisymmetric separator (12h) is therefore
equivalent to an Edmonds matroid-intersection rank deficit.  The useful proof
object is not an arbitrary skew matrix: it is one subset of the directed-arc
ground set violating a rank inequality.

This translation is parameter-free and does not use `q = 9`.  It is a real
generic interface for transfer to A-REG.  It does **not** by itself prove the
outer-design theorem (13f): the remaining task is to derive the rank deficit
from the `Q,K` incidence data, or prove that every directed-arc subset obeys
the rank inequality.

## Exact construction

Let `E` be the symmetric set of allowed ordered pairs `(t,u)`.  For a fixed
tail `t`, let `E_t = {(t,u) in E}`.  The augmented bipartite candidate graph
of (12f) has:

- one left vertex for each arc `(t,u) in E_t`;
- the selected real labels met by candidate `u` on the right;
- one private dummy on the right for every singleton candidate.

A subset of `E_t` is independent when its left vertices can be matched into
the label/dummy shore.  These independent sets form the transversal matroid
`N_t`.  Truncate `N_t` to rank `d_t`, calling the result `M_t`.  Under the
already-audited local-feasibility hypothesis `rank(N_t) >= d_t`, the local
polytope `P_t` from (12g) is exactly the base polytope `B(M_t)`.  The equality
`sum_u X_tu = d_t` selects the base face; the label capacities are precisely
the transversal-matroid inequalities because the bipartite matching
polytope is integral.

Now put

```text
M_out = directSum_t M_t                         on arcs grouped by tail,
M_in  = directSum_u reversePullback(M_u)        on arcs grouped by head.
```

Then

```text
P    = product_t P_t = B(M_out),
T(P) = product_u T(P_u) = B(M_in).
```

Consequently a directed matrix satisfying all outgoing and incoming
matching constraints exists iff `M_out` and `M_in` have a common base.  This
is exactly the feasibility of (12g).  Since matroid intersection is integral,
fractional feasibility is equivalent here to an integral common directed
base.  (As in the audit, symmetrizing its incidence matrix gives the required
fractional symmetric matrix; the common base itself need not be invariant
under reversal.)

## Rank-deficit certificate

Write

```text
R = sum_t d_t = rank(M_out) = rank(M_in).
```

Edmonds' matroid-intersection min--max theorem gives

```text
P intersect T(P) is nonempty
iff
for every S subset E,
  rank_out(S) + rank_in(E ∖ S) >= R.                    (MI)
```

Thus fractional infeasibility is witnessed by a single `S subset E` with
strict deficit.  In local matching language the two ranks are explicit:

```text
rank_out(S)
  = sum_t min(d_t, nu(candidateGraph_t restricted to S intersect E_t)),

rank_in(E ∖ S)
  = sum_u min(d_u,
      nu(candidateGraph_u restricted to
         reverse((E ∖ S) intersect arcsEntering(u)))).
```

Each matching number has the label-only Kőnig/Hall cover formula already
derived in (12fa).  Therefore `(MI)` turns the global obstruction into one
two-sided collection of ordinary label covers.  It is the discrete min--max
normal form behind the continuous skew-potential form (12h)--(12n).

## Oriented-cut uncrossing

The deficient set in `(MI)` may be assumed to contain at most one
orientation of every allowed unordered pair.  This is an exact normal form,
not a heuristic choice of a sparse certificate.

Let `rho` reverse every directed arc and abbreviate

```text
r(S) = rank_out(S),
S*   = rho(E ∖ S),
g(S) = r(S) + r(S*).
```

Because `M_in` is the reversal pullback of `M_out`, `g(S)` is the left side
of `(MI)`.  Reversal-complement is an involution and

```text
g(S*) = g(S).
```

The function `g` is submodular: its first summand is a matroid rank
function, while its second is a matroid rank function composed with
complement and reversal (the submodular inequality merely exchanges union
and intersection in that summand).  Put

```text
A = S intersect S*,
B = S union S*.
```

Then `A* = B`, so `g(A)=g(B)`.  Submodularity and the displayed symmetry give

```text
2 g(A) = g(A) + g(B)
       <= g(S) + g(S*)
        = 2 g(S).
```

Thus `g(A) <= g(S)`: if `S` is deficient, then so is `A`.  Finally
`A intersect rho(A)=empty`, since `A subset S` while `rho(A) subset E ∖ S`.
Therefore every failure of (12g) has a certificate `A` which is literally an
orientation of a subgraph of the symmetric allowed support.  By applying
`*`, one may equivalently use the co-oriented certificate `E ∖ rho(A)`.

This removes all bidirected and absent/present ambiguity from the next
classification problem.  The remaining rank inequality for an oriented
arc set is

```text
r(A) + r(E ∖ rho(A)) < R,       A intersect rho(A) = empty.
```

It does not yet force a local deficit or collision, but it aligns the
Edmonds witness with the existing direction-sensitive reciprocity language:
the only free decision on an unordered allowed pair is its direction or its
omission.

## Why this is sharper than the previous literature dictionary

The earlier separation theorem says only that some antisymmetric functional
has strict sign on a product polytope.  Weighted support-function evaluation
then requires 47 independent matching optimizations and leaves an arbitrary
price table to construct.

Matroid intersection removes that freedom.  A failed instance has one cut
`S`; after choosing minimum vertex covers for the restricted local candidate
graphs, every term is an integer matching deficiency.  This suggests a
bounded next probe with an unambiguous success condition:

> classify a minimal deficient `S` under arc reversal and the `Q,K` support
> laws, then prove it induces the deficit/collision alternative consumed by
> `false_of_localGramPacking_deficit_or_forced_collision`.

If minimal deficient sets have no forced structure beyond arbitrary local
Hall covers, the route stops: Edmonds supplies a better certificate language
but not the missing outer-design inequality.

## Literature anchors

- Jack Edmonds, *Submodular functions, matroids, and certain polyhedra*,
  in **Combinatorial Structures and Their Applications** (1970), pp. 69--87.
  This is the classical source for matroid base-polytope integrality and the
  matroid-intersection min--max framework.
- Eugene L. Lawler and C. U. Martel, *Computing maximal polymatroidal network
  flows*, **Mathematics of Operations Research** 7 (1982), 334--347,
  DOI `10.1287/moor.7.3.334`.  This is a broader flow language for local
  submodular capacity constraints; in the present problem the sharper
  specialization is ordinary intersection of two direct sums of truncated
  transversal matroids.

## Formalization boundary

No Lean wrapper is opened in this pass.  A source-tree audit of the pinned
Mathlib finds matroid basics, finite rank, maps, duals, minors, and sums, but
no matroid-intersection or common-base min--max theorem.  Formalizing the
forward certificate check is cheap: a displayed deficient `S` immediately
bounds every common selection.  Formalizing the converse existence theorem
would be a substantial new combinatorial development.  The best near-term
interface is therefore certificate-facing: define the two local matching
ranks and prove that a `Q,K`-forced deficient subset rules out the directed
selection.  The graph-facing consumer should remain separate from this
combinatorial theorem.
