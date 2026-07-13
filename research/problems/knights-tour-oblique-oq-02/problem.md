# knights-tour-oblique-oq-02

## Problem Description

What is the distribution of oblique counts across all 13+ trillion closed
knight's tours on the 8×8 chessboard?

Knuth (2025 Christmas Lecture, TAOCP Vol 4 Fascicle 8a) established that the
*minimum* oblique count is 4 and is achieved by a unique tour up to D4
symmetry. The parent gallery proof `knights-tour-oblique` formalizes that
minimum and uniqueness. This open question asks for the *full histogram* —
or, more realistically (since Lean cannot enumerate 1.3 × 10^13 tours), for
the structural constraints that the histogram must satisfy.

## Formal target

Define a function

```
obliqueDistribution : ℕ → ℕ
obliqueDistribution k = #{ t : ClosedTour // obliqueCount t = k }
```

and establish the structural properties of this distribution that fall out
of the existing winding/D4 infrastructure in `KnightsTourOblique.lean`,
without enumerating the ~13.3T tours.

## Metadata

- **Category**: extension (distribution refinement of the parent minimum
  theorem)
- **Source proof**: `knights-tour-oblique` (`Proofs/KnightsTourOblique.lean`,
  2469 lines, 1 axiom, status: axiomatized)
- **Tier**: B
- **Selected by**: seeker, 2026-05-12 09:56 UTC
- **Significance**: 5 (gallery-internal structural refinement; Knuth's main
  contribution is the minimum + uniqueness, the histogram is a distinct but
  closely related object)
- **Tractability**: 7 (structural lemmas are reachable; the actual histogram
  values are not)

## Related gallery work

- **Parent**: `knights-tour-oblique` — proves `obliqueCount ≥ 4` and
  `Classical.choice`-style uniqueness via 1 axiom
  (`knuth_unique_four_oblique`).
- **Sibling OQ-01**: `knights-tour-oblique-oq-01` — generalizes the minimum
  to n×n boards (n ≥ 5). `KnightsTourObliqueOQ01.lean`:381
  `four_oblique_corners` proves `obliqueCount t ≥ 4` for all closed tours on
  n×n with n ≥ 5.

## Tractability triage (what's feasible in Lean)

**NOT feasible**:
- Compute concrete histogram values `obliqueDistribution 4 = 1`,
  `obliqueDistribution 5 = ?`, etc. The full enumeration of ~1.3 × 10^13
  tours is far beyond `decide` / `native_decide`.

**Feasible (structural lemmas)**:
- **Support lower bound**: `obliqueDistribution k = 0` for `k < 4` — direct
  reformulation of the parent's `four_oblique_corners`.
- **Parity / winding-mod-8 constraint**: from `tour_winding_zero` (sum of
  turn angles ≡ 0 mod 8) and the elimination of `turnAngle = 4`
  (`no_turn_angle_4_all`), oblique angles can only be 3 or 5, both *odd*.
  This forces a parity constraint on the joint count of `#turnAngle = 3` and
  `#turnAngle = 5`.
- **D4 invariance**: the dihedral group D4 (order 8) acts on `ClosedTour` by
  board symmetries, and `obliqueCount` is D4-invariant. This forces
  `obliqueDistribution k ≡ 0 mod 8` *generically* (with exceptions only for
  tours fixed by some non-identity D4 element — exceptional symmetric
  tours).
- **Reversal symmetry**: `reverse t` is a closed tour with the same
  `obliqueCount`. Generically forces `obliqueDistribution k ≡ 0 mod 2`
  (exceptions: palindromic tours).
- **Support upper bound**: every turn angle is in `{0, 1, 2, 3, 5, 6, 7}`
  (since 4 is eliminated). The 64-turn winding constraint (sum ≡ 0 mod 8)
  combined with oblique turns contributing 3 or 5 (≡ 3, −3 mod 8) gives a
  better bound than the trivial `k ≤ 64`.
- **Sum-to-total**: `∑_k obliqueDistribution k = totalClosedTours`. The
  total `13267364410532` is *Knuth-asserted* (Loebbing-Wegener 1996, Mc-Kay
  1997, replicated by Knuth 2025) and would need to be either axiomatized
  or proven via `native_decide` on a *highly optimized* enumeration — out
  of scope here.

## Suggested first steps (S2+ ACT phase)

1. Define `obliqueDistribution : ℕ → ℕ` in a new
   `Proofs/KnightsTourObliqueOQ02.lean`.
2. Re-export the parent's `four_oblique_corners` (or the 8×8 minimum) as
   `obliqueDistribution_zero_below_four : ∀ k < 4, obliqueDistribution k = 0`.
3. Build the D4 group action on `ClosedTour` (an 8-element finite group via
   horizontal/vertical reflection + 90° rotation generators) and prove
   `obliqueCount`-invariance.
4. Conclude a generic-mod-8 divisibility for `obliqueDistribution k` (with
   the symmetric-tour exception set explicitly carved out).
5. Add a winding-parity lemma: if `obliqueDistribution k ≠ 0` then some
   parity / mod-8 constraint linking the `turnAngle = 3` and `turnAngle = 5`
   sub-distributions holds.

A finished OQ-02 deliverable need not produce histogram values; producing the
**structural skeleton** — support, D4-mod-8, reversal-mod-2, winding-parity
— is itself the natural contribution.

## References

- Knuth, D. E. (2025). *29th Annual Christmas Lecture: Knight's Tours and
  Oblique Turns*. Stanford University, December 2025.
- Knuth, D. E. *The Art of Computer Programming, Volume 4, Fascicle 8a:
  Knight's Tours* (forthcoming, 2026).
- Löbbing, M.; Wegener, I. (1996). *The Number of Knight's Tours Equals
  33,439,123,484,294 — Counting with Binary Decision Diagrams*. Electronic
  J. Combinatorics 3, R5. (Note: this earlier total was later corrected;
  Mc-Kay 1997 obtained 13,267,364,410,532 *directed closed tours starting
  from a fixed square*, which is the count relevant here.)
- McKay, B. D. (1997). *Knight's Tours on an 8 × 8 Chessboard*. Tech. Rep.
  TR-CS-97-03, Australian National University.

## Provenance

- Selected by seeker, 2026-05-12T09:56:28Z
- Parent gallery: `src/data/proofs/knights-tour-oblique/`
- Parent Lean: `proofs/Proofs/KnightsTourOblique.lean`
