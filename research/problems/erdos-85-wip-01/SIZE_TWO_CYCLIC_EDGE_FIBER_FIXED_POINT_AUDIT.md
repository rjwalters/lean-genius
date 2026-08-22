# Size-two cyclic edge-fiber fixed-point audit

## Scope

This note audits a possible coupling between the row-zero resolver matchings
and the internal-edge difference fibers `0,-1` in
`BinarySizeTwoCyclicPackingBound`.  Everything below is q-generic.  It uses
only routing reciprocity and the same-difference agreement law; it is not an
order-64 endpoint argument.

## Fixed points are reversed edge-fiber incidences

Write

```text
P_(x,t)(r) = r + targetDifference(x,t,r)
```

for the punctured routing permutation at source cell `(x,t)`, and put

```text
F_t(x) = #{r : targetDifference(x,t,r)=0}.
```

Thus `F_t(x)` is exactly the number of fixed points of `P_(x,t)`.  If such a
route uses row `r`, reciprocity reverses it to a route

```text
(x+r,0)  -->  (x,t)
```

using row `-r`.  Conversely every route from a source in difference fiber
`0` to `(x,t)` reverses uniquely to one of these fixed points.  Hence

```text
F_t(x)
 = multiplicity of the absolute cell (x,x+t)
   among all q source matchings in fiber 0.
```

The analogous statement for target difference `-1` identifies the solutions
of `P_(x,t)(r)=r-1` with multiplicities of the source orbit `-1`.

This is already implicit in the banked matching API:

- `sizeTwoCyclicMatchingSourceCell` identifies `(x,t)` with `(x,x+t)`;
- `sizeTwoCyclicSourceMatching_sourceCell_mem_comm` reverses incidence;
- `sizeTwoCyclicSelectedOrbitMultiplicity_sourceCell` performs the
  pointwise incidence transpose.

## Exact agreement budget

Apply the raw one-orbit second-moment theorem to source fiber `0`.  The
same-difference agreement cap gives

```text
2 * sum_(x,t) C(F_t(x),2) <= q(q-1).
```

Here `t` ranges over all `q-2` allowed target fibers.  The total mass is
also exact:

```text
sum_(x,t) F_t(x) = q(q-2),
```

because the q source cells in fiber `0` each have `q-2` routed targets.
Therefore the fixed-point table has average entry exactly one.  Replacing
`0` by `-1` gives the identical pair of statements for the shifted fixed
points `P_(x,t)(r)=r-1`.

The upper bound is precisely
`two_mul_sizeTwoCyclicRawMatchingOrbitMultiplicity_choose_two_sum_le`; this
audit supplies its fixed-point interpretation, not a new independent
inequality.

## Why this does not consume resolver overlap

The row-zero resolver map is

```text
rho_x(t) = targetDifference(x,t,0)
```

on non-edge fibers `t notin {0,-1}`.  Reverse admissibility forces
`rho_x(t)` to remain a non-edge fiber.  Consequently a resolver edge never
contributes to `F_t(x)`: at row zero its target difference is explicitly
neither `0` nor `-1`.

Moreover, the two exact fixed-point identities permit the completely uniform
profile

```text
F_t(x)=1 for every (x,t),
```

whose collision mass is zero.  Thus they provide no lower bound that can be
compared with the resolver-overlap lower bound `5(q-4)/2`.  Route-line parity
does not repair this: an off-diagonal `t -> 0` block is paired with the
`0 -> t` block, so its contribution to the preserved line `t+0` is already
even.  Only diagonal blocks yield an independent parity statement.

## Precise missing statement

The edge-fiber route is useful only if another invariant forces many
fixed/shifted-fixed points, or ties them to repeated resolver pairs.  A
sufficient new input would have the form

> repeated resolver pair `{t,s}` at bases `x,y` forces a specified
> `targetDifference=0` or `-1` event in one of the four cross rows.

Neither reciprocity, the punctured-permutation first/second displacement
moments, nor route-line parity implies such an event.  Without this bridge,
the edge-fiber fixed-point census is exactly the already-banked one-orbit
agreement budget and cannot close the packing bound.
