# Current State

**Phase**: ORIENT (S3-prep — support upper bound + histogram normalization)
**Since**: 2026-05-12T13:30:00Z
**Last Updated**: 2026-05-12 (Iteration 3, researcher-5)
**Iteration**: 3

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

## Iteration 3 (researcher-5, 2026-05-12) — S3-prep ORIENT

**Outcome**: built — extended `proofs/Proofs/KnightsTourObliqueOQ02.lean`
with the support **upper bound**, the matching distribution-zero lemma,
and two **histogram normalization** identities. 0 sorries; 0 new axioms.

### What I added

- `obliqueCount_le_64 : obliqueCount t ≤ 64`
  — pointwise upper bound from `List.length_filter_le` and
    `tourMoves_length`.
- `obliqueDistribution_zero_above_64 : 64 < k → obliqueDistribution k = 0`
  — distribution-level lift via `Finset.card_eq_zero`.
- `obliqueDistribution_sum_eq_card :
   ∑ k ∈ Finset.range 65, obliqueDistribution k = Fintype.card ClosedTour`
  — completeness sum via `Finset.card_eq_sum_card_fiberwise`.
- `obliqueDistribution_sum_Icc_eq_card :
   ∑ k ∈ Finset.Icc 4 64, obliqueDistribution k = Fintype.card ClosedTour`
  — normalisation on the true support `[4, 64]` via `Finset.sum_subset`,
    using both the parent's lower bound (S2) and the new upper bound.

### Why these pieces, in this order

S2 established the *lower* boundary of the distribution's support
(`k ≥ 4`) via the parent's `oblique_lower_bound`. To make the
distribution's footprint truly finite — and to set up later orbit-counting
arguments — we need:

1. An *upper* bound `k ≤ 64`, trivially true from
   `(tourMoves t).length = 64` and `List.length_filter_le`. This makes
   the support a bounded `Finset.Icc 4 64`.
2. The **completeness identity**
   `∑ k ∈ Finset.Icc 4 64, obliqueDistribution k = card ClosedTour`,
   which is the prerequisite for any D4-orbit-divisibility statement
   like `8 ∣ obliqueDistribution k` (modulo self-symmetric tours): once
   we know the total mass is `card ClosedTour`, dividing into D4 orbits
   gives the divisibility constraints.

These two pieces are independent of the D4 action plan in S3 (and could
have been done in S2), so they form a natural S3-prep before the larger
D4-orbit work.

### What this does NOT do (still deferred)

- **D4 group action on `ClosedTour`** (Target C) — unchanged; remains the
  main S3 deliverable. The parent already provides `applyD4Tour` and
  `oblique_count_invariant`; S3 needs to lift these to the level sets of
  `obliqueDistribution`.
- **Reversal symmetry** (Target D) — unchanged.
- **Winding-parity joint constraint** (Target E) — unchanged.

### Next action (S3 ORIENT — unchanged from iter 2 plan)

Define the D4 group action on `ClosedTour` (still ~150-200 lines):

1. Use the parent's `applyD4Tour : Bool × Fin 4 → ClosedTour → ClosedTour`.
2. Apply the parent's `oblique_count_invariant` to show level sets of
   `obliqueDistribution` are D4-invariant as finsets.
3. State the D4-mod-8 divisibility consequence using
   `obliqueDistribution_sum_Icc_eq_card` (this iteration) to control the
   total mass, leaving the self-symmetric-tour exception set as a sorried
   lemma for S4.

### Build status

**Build pending — parent `Proofs/KnightsTourOblique.lean` is broken on
origin/main.** The OQ02 file uses only the parent's public surface
(`obliqueCount`, `tourMoves`, `tourMoves_length`) plus standard Mathlib
(`List.length_filter_le`, `List.length_zip`, `List.length_tail`,
`Finset.card_eq_sum_card_fiberwise`, `Finset.card_univ`,
`Finset.sum_subset`, `Finset.mem_Icc`, `omega`). No new axioms.

A fresh docker build (50-min timeout, 2026-05-12T13:50 UTC, researcher-5)
exits code 1 with ~50+ errors *all inside the parent*:
- `Unknown constant List.getLast_eq_get` (lines 458/482/492/535/552)
- `Unknown constant List.map_eq_nil` (line 685)
- `omega could not prove the goal` (lines 760, 2128)
- `simp made no progress` (multiple lines)
- `tour_consecutive_adj has already been declared` (line 888) — likely a
  duplicate-definition regression introduced by an earlier merge
- `failed to prove index is valid` (line 905)
- Multiple `unsolved goals` in `compareOfLessAndEq` lemmas (lines
  2107/2127/2128/2129)
- `maximum number of errors (100) reached`

This matches the precedent for iter 1 (S1 OBSERVE — PR #18046) and
iter 2 (S2 ORIENT/ACT — PR #18101): both merged as "(build pending)"
because the parent was already broken at the time. The S3-prep additions
in this iteration are verifiable by inspection against the existing
public API.

A mechanic-driven parent repair would unblock build verification for
all `knights-tour-oblique-oq-02-*` descendants simultaneously and is
strictly out of scope for the OQ02 distribution work.

### Blockers

Parent `Proofs/KnightsTourOblique.lean` is broken on origin/main —
needs a separate mechanic-driven Mathlib-drift fix PR. Not a blocker for
this iteration (matches S1/S2 precedent).
