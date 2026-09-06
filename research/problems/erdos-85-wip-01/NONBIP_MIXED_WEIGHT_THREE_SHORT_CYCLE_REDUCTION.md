# Weight-three short-cycle reduction

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED`.

Status: prose proof, externally corroborated; not a Lean theorem or an
exclusion of an ambient graph. Both resulting completion cases remain open.

## Complete cycle split on the small component

**Proposition.** Let `q >= 8`. Every nonbipartite simple graph on `3q`
vertices with minimum degree at least `q-1` contains a triangle or an
induced five-cycle.

Here is the standard bound underlying the proposition. If a nonbipartite
graph has order `N`, minimum degree `delta`, and shortest odd cycle of
length `ell >= 5`, then

```text
ell * delta <= 2N.                                      (1)
```

The shortest odd cycle is induced: a chord splits it into two shorter
cycles, one odd. An outside vertex cannot have three neighbors on it.
Indeed, the three cyclic gaps are at least two (there are no triangles),
have odd sum, and hence include an odd gap of length at most `ell-4`.
That arc together with the outside vertex gives a shorter odd cycle.
Thus every vertex has at most two neighbors on the cycle. Counting
incidences with the cycle gives (1), counting an internal edge twice.

If the proposition failed, `ell >= 7`, so

```text
7(q-1) <= ell(q-1) <= 6q,
```

which forces `q <= 7`. This proves the proposition. The threshold is
sharp for abstract regular graphs: replace each vertex of `C7` by three
independent vertices and each edge by a complete bipartite graph. The
result has order 21, degree 6, and odd girth 7. This is not an ambient
C4-free graph or a realized defect component.

The literature states the general implication
`delta > 2N/(2g+1)` implies an odd cycle shorter than `2g+1`:
Freddie Illingworth, *The chromatic profile of locally colourable graphs*,
[Lemma 2.1, pp. 7–8](https://discovery.ucl.ac.uk/id/eprint/10197002/1/min_deg_stab_accepted.pdf),
attributed there to Andrásfai, Erdős and Sós. Its application here is `g=3`.

More generally, for a component of order `mq`, `m >= 2`, degree `q-1`,
and `q > 2m+1`, its shortest odd cycle has length at most `2m-1`.
Keep a triangle as a separate immediate case; otherwise (1) applies.
An odd length at least `2m+1` would imply
`(2m+1)(q-1) <= 2mq`, or `q <= 2m+1`. At equality the strict
conclusion need not hold: the balanced blow-up of `C_(2m+1)` with part
size `m` has order `mq` and degree `q-1` for `q=2m+1`.

## Application to the two-component partition [q-3,3]

Orient the component `C` to have order `3q`, and the other component `F`
to have order `qn`, where `n=q-3`. Assume `D_C` is nonbipartite.
For the ambient cross adjacency `B=A_G[C,F]`, row sums are `n` and
column sums are 3. These are the opposite orientation from the
40-to-24 shore in
`NONBIP_MIXED_EXTERIOR_SELF_INDEX_TRANSPORT_AUDIT.md`.

The proposition makes the following split exhaustive on `C`:

* A defect triangle: its three ambient exterior neighborhoods are
  disjoint sets of size `n`. The integer carrier `B^T 1_Q` has profile
  `1^(3n), 0^(qn-3n)`.
* An induced defect `C5`: write its exterior neighborhoods as `S_i`,
  each of size `n`. Consecutive sets are disjoint. An exterior label
  meets at most two sets, since an independent set in `C5` has size
  at most two. Each of the five noncycle pairs shares at most one
  label by ambient C4-freeness. The integer carrier therefore has profile
  `2^d, 1^(5n-2d), 0^(qn-5n+d)`, where `0 <= d <= 5`.

For even `q`, `n` is odd, so both carriers have odd support modulo two.
At `q=8`, the C5 profile in THIS orientation is
`2^d, 1^(25-2d), 0^(15+d)` on the 40-shore, not the older
`2^d, 1^(15-2d), 0^(9+d)` profile on the 24-shore.

Both cases must retain the same ambient blocks and simultaneous equations

```text
D_C B = B D_F,
H_C B + B H_F = J,
A_G^2 = (q-1)I + J - D,
```

with zero-one symmetric ambient adjacency, full C4 cap, and connected
defect components. A local carrier alone is not a completion.

This removes longer *shortest* odd cycles from the small-shore case split;
it does not forbid longer odd cycles in the graph. It does not establish
that the small component is nonbipartite from its size alone, force a
triangle on the large component, or make an older large-shore triangle
probe exhaustive. In a branch where every defect component is already
known nonbipartite, the hypothesis on `C` is available. Other partitions,
including the connected `[q]` branch, remain outside this reduction.

## Formalization boundary

No new Lean declaration is claimed. The apparent reusable theorem
`Erdos57Aristotle.bipartite_iff_no_odd_cycles` contains `sorry` and must
not be imported as evidence. The completed odd-closed-walk construction
and odd-weight cycle extraction are possible ingredients, but a formal
shortest-cycle incidence proof still needs to be supplied. No graph
enumeration or order-64 search is required for this reduction.
