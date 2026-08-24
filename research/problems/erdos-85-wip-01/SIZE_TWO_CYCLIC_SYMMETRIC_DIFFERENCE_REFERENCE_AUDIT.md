# SIZE-TWO-CYCLIC: symmetric-difference reference audit

## Canonical reference

Node: full-cap reciprocal empty-fibre target beneath outline A.5.3
`GAP A-REG-NONBIP`.

For source difference `t`, admissible relative rows omit `t,t+1`, while
admissible relative columns omit `0,-1`.  The canonical parallel bijection is

```text
P0_t(r) = r - t - 1.
```

It maps the two omitted rows to the two omitted columns and sends every
actual row to target difference

```text
P0_t(r)-r = -t-1 =: t*.
```

The fibre map `t -> t*` is an involution and the resulting reference route
family is globally reciprocal.  Superposing an actual reciprocal code with
this reference and taking symmetric difference therefore does produce an
undirected even-degree graph: both constituents are `(q-2)`-regular, so each
XOR degree is even.  Equivalently, its signed darts decompose into alternating
Eulerian components.

## Why the empty fibre creates no boundary

The proposed round-13 mechanism required the selected empty diagonal block
to force a nonzero component or boundary in this symmetric difference.  But
the reference has no diagonal block in *any* fibre.  A reference route stays
in its source fibre exactly when

```text
t = -t-1,
```

or `2t=-1` in `Z/q`.  For even `q` this is impossible: the left side lies in
the image of doubling, whereas `-1` does not.  Hence

```text
(P0)_(t,t) = 0  for every t.
```

If the actual selected block `A_tt` is empty, its XOR with the reference
block is still zero.  Nothing in the Eulerian decomposition distinguishes
the selected fibre from the other reference diagonal blocks.  Thus the
claimed "empty fibre forces a nonzero boundary component" does not follow.

## Scope of the cut

The Eulerian symmetric-difference construction itself is valid, but it has
no named chain to the empty-fibre contradiction.  A revival needs either:

- a different globally reciprocal exact-hit reference with a nonempty
  selected diagonal block; or
- an additional color/weight that marks absence of actual `t`-routes even
  though the unweighted reference diagonal is also empty.

The first option cannot be obtained by merely switching the two artificial
hole completions: those completion edges are not the `(q-2)` genuine route
matching and the canonical global completion-bit holonomy is already cut.
No alternating-component interface should be formalized until such a
distinguishing boundary is supplied.
