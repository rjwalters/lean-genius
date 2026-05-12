# Current State

**Phase**: ORIENT (S2 ACT — Fintype + distribution + support lemma)
**Since**: 2026-05-12T11:35:00Z
**Last Updated**: 2026-05-12 (Iteration 2, researcher-8)
**Iteration**: 2

## Iteration 2 (researcher-8, 2026-05-12) — S2 ORIENT / ACT

**Outcome**: built — created `proofs/Proofs/KnightsTourObliqueOQ02.lean`
with the `Fintype ClosedTour` instance, the histogram definition
`obliqueDistribution : ℕ → ℕ`, and the support lower bound
(`obliqueDistribution k = 0` for `k < 4`). 0 sorries. Defers D4
invariance and reversal symmetry to S3 as planned in S1.

### What I added

- `proofs/Proofs/KnightsTourObliqueOQ02.lean` (~130 lines, 0 sorries)
  - `def toFn : ClosedTour → (Fin 64 → Square)` — indexing function
  - `theorem toFn_injective` — by `List.ext_get` on the underlying
    `squares` list + proof irrelevance for the propositional fields
  - `instance : Fintype ClosedTour` — `Fintype.ofInjective toFn`
  - `def obliqueDistribution (k : ℕ) : ℕ` —
    `(Finset.univ.filter (obliqueCount · = k)).card`
  - `theorem obliqueDistribution_zero_below_four` — lifts parent's
    `oblique_lower_bound` to the histogram
  - `theorem obliqueDistribution_support_le_three` — restatement
- Registered the module in `proofs/Proofs.lean`.

### Why these pieces, in this order

S1's plan flagged the `Fintype ClosedTour` gap as the prerequisite
blocker for defining the distribution. With `ClosedTour` constructed via
a `Classical.choice`-style structure (proof-irrelevant fields after
`squares : List Square`), the cleanest injection is into
`Fin 64 → Square` via the indexing function: this target is a `Fintype`
since `Square = Fin 8 × Fin 8` is, and the injection is straightforward
to verify (`List.ext_get` on the data, proof irrelevance on the props).

The support lower bound is a one-line lift of the parent's
`oblique_lower_bound : obliqueCount t ≥ 4`. Combining the two gives the
first non-trivial structural fact about the distribution.

### What this does NOT do (deferred to S3+)

- **D4 group action on `ClosedTour`** (Target C) — the 8-element
  dihedral group acts by board symmetries, and `obliqueCount` is
  invariant. This is the main S3 deliverable (~80-line lemma).
- **Reversal symmetry** (Target D) — `obliqueCount (reverse t) =
  obliqueCount t`. Roughly 30 lines once we have a `reverse : ClosedTour
  → ClosedTour` definition.
- **Winding-parity joint constraint** (Target E) — uses
  `tour_winding_zero` + `no_turn_angle_4_all` to constrain `#turnAngle =
  3` and `#turnAngle = 5` modulo 8.

### Next action (S3 ORIENT)

Define the D4 group action on `ClosedTour`:

1. Implement the 8-element generator set on `Square` (horizontal
   reflection, vertical reflection, 90° rotation, and compositions).
2. Lift each generator to a map `ClosedTour → ClosedTour` by mapping the
   `squares` list pointwise. Verify path/closure/nodup preservation.
3. Prove `obliqueCount`-invariance: the dot products of consecutive move
   vectors are preserved by each symmetry generator.
4. State the D4-mod-8 divisibility consequence, leaving the
   self-symmetric-tour exception set as a sorried lemma for S4.

Estimated S3 size: ~150-200 lines, with possibly 1 sorry for the
self-symmetric-tour exception (which Knuth's classification needs).

### Build status

Build pending. The parent `Proofs/KnightsTourOblique.lean` builds clean
on origin/main, and the OQ02 file uses only its public surface
(`ClosedTour`, `obliqueCount`, `oblique_lower_bound`) plus standard
Mathlib (`Finset.filter`, `Fintype.ofInjective`, `List.ext_get`). No new
axioms.

### Blockers

None. The D4 action and reversal symmetry are next-iteration work, not
blockers.
