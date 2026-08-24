# NONBIP-CONNECTED endgame audit

Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`, candidate (vi).

Status: strategic audit, 24 August 2026.  This does not close the node.

## The verified chain

For a hypothetical binary square-order candidate, connectedness of the
second-order defect graph `D` currently feeds two independent chains.

1. `binarySquare_regular_pred_le_defectCut_of_pos` gives the sharp lower
   bound `q-1` for every nonzero defect cut.  This proves that `D` is
   maximally edge-connected and, through
   `binarySquare_connected_secondOrderDefect_erase_connected` and the
   two-separator Mantel modules, that deleting one or two vertices cannot
   disconnect `D`.
2. The incidence bottleneck

   ```text
   E = AD - (J-A) = qA - A^3 + (q-1)J
   ```

   has nonzero integral zero-sum rows.  The closed-star residue strengthens
   its Frobenius lower bound to

   ```text
   ||E||_F^2 >= q^3+2  (k even),
   ||E||_F^2 >= q^3+4  (k odd),
   ```

   as formalized by
   `connected_binarySquare_dyadic_incidenceBottleneck_energy_ge_cube_add_two`
   and its odd-exponent sibling.  The same fact is an exact lower bound on
   the sixth adjacency moment.

The large three-separator tree is an attempt to extend item 1 from deletion
of two vertices to deletion of three.  Its recent bottom-slice chain is

```text
B48 paired wing profiles
  -> dyadic q mod 3 selection
  -> B51 zero/one P-core budget
  -> B50' exceptional-wing localization.
```

This is genuine classification progress, but it is not currently an
endgame.

## The missing arrow

No checked theorem or stated conjecture in the outline consumes
`vertexConnectivity(D) >= 4`.  More generally, no fixed connectivity lower
bound is known to imply singularity of `A`, an upper bound on the designated
spectral dimension, or an upper bound on `||E||_F^2`.  Therefore closing the
three-separator tree would prove a stronger property of `D` but would not
shorten a verified implication chain to `False`.

This matters structurally: a `(q-1)`-regular graph can have vertex
connectivity as large as `q-1`.  Thus repeatedly excluding separators has
no automatic terminal before the maximum possible connectivity, and even
maximal connectivity is not itself incompatible with the spectral and
determinant conditions recorded in `NONBIP_CONNECTED.md`.  An endgame must
use the special integral square-root identity `A^2=L_D+J`, not connectivity
alone.

## Candidate (vi): exact upper-bound terminal

The shortest consumer of the banked strict-energy theorem is the following
entrywise upper bound:

```text
INCIDENCE-BOTTLENECK-CUBE-UPPER
  Under the binary square-order, regular, C4-free hypotheses,
  if D is connected then ||AD-(J-A)||_F^2 <= q^3.
```

Together with the already proved dyadic strict lower bound, this gives
`q^3+2 <= q^3` immediately.  Equivalently, via
`binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthTrace_sub_baseline`,
one may target the matching sixth-moment upper bound.  No wrapper should be
built before the upper bound itself exists.

At present this is a **candidate statement, not an axiom believed proved or
even independently validated**.  Its conditional Lean composition is being
handled separately; this audit does not duplicate that wrapper.  The exact
obstacle is visible in the row model: an entry of `E` is occupancy-minus-one
among `q-1` defect-neighbour blocks.  C4-freeness controls pairwise block
intersections, but the current ledger gives only a lower bound on row energy;
it gives no global upper bound on repeated occupancy.  A viable proof must
add a global packing constraint on those repeated occupancies.  Higher
vertex-connectivity does not provide that constraint by itself.

## The `mu=-1` blind spot, split by exponent parity

On a simultaneous adjacency/defect eigenvector, `E` acts by

```text
theta (mu+1),       theta^2 = q-1-mu.
```

The banked `incidenceBottleneck_mulVec_eq_zero_iff_mu_eq_neg_one` proves
that the only nonprincipal kernel is `mu=-1`.  There the adjacency square is
`q I`.

- If `k` is odd, `q=2^k` is not a rational square.  The `+sqrt(q)` and
  `-sqrt(q)` multiplicities on every rational `mu=-1` primary sector must
  pair, so that sector has trace zero.  The blind spot therefore cannot
  carry any of the required nonprincipal trace `-q`.
- If `k` is even, `sqrt(q)` is integral.  The same argument supplies no sign
  pairing.  A pure blind-spot escape cancelling the principal trace would
  require signed multiplicity imbalance exactly `sqrt(q)` between the two
  adjacency roots.  This is the precise open `mult_D(-1)` / sign-imbalance
  problem recorded in the outline.

The useful missing blind-spot statement is therefore

```text
BLIND-TRACE-ZERO:
  trace(A restricted to ker(D+I)) = 0.
```

It is automatic in the odd-exponent branch and genuinely additional in the
even-exponent branch.  It removes the exact kernel of `E`, but it is **not by
itself a terminal**: designated square-in-eigenfield factors with
`mu != -1` can still contribute trace.  Any account claiming that
BLIND-TRACE-ZERO alone closes `NONBIP-CONNECTED` skips this remaining family.

## Designated-factor alternative

The honest algebraic child is the designated-factor route already isolated
in the outline.  `connectedNonbipartite_designatedFactor_finrank_sq_growth`
forces the intrinsic designated dimension to grow, while all certified
residual sectors have trace zero.  The missing statement is an **upper bound
on the total dimension of square-in-eigenfield factors** strong enough to
prevent their signed traces from summing to `-q`.  This route uses
`A^2=L_D+J` directly and has a terminal; the separator route presently does
not.

## Work-allocation conclusion

Do not extend the separator classification to a new B53 solely to obtain
four-connectivity.  Resume it only if either

- a graph-facing consumer of four-connectivity is stated, or
- a separator lemma also proves the repeated-occupancy packing needed for
  `INCIDENCE-BOTTLENECK-CUBE-UPPER`.

Otherwise the load-bearing targets beneath `NONBIP-CONNECTED` are the
incidence-energy upper bound above or the designated-dimension upper bound.
Within the latter, odd `k` has no `mu=-1` trace escape; even `k` additionally
requires BLIND-TRACE-ZERO or a sharp bound on its signed root imbalance.
