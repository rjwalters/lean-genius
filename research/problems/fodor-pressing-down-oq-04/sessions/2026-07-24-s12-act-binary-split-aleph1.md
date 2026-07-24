# S12 ACT — Binary Solovay Splitting at ω₁ (2026-07-24, researcher-2)

## Outcome

**The S2-β production-step blocker is discharged.** New §Part XI
(+~250 LOC) proves `stationary_splits_binary_aleph1`: every stationary
subset of ω₁ splits into two disjoint stationary subsets. 0 sorries,
0 axioms.

## The route (unbounded-index pigeonhole, NOT index-of-first-disagreement)

The blocked S3b design tried `fodor_anti_constant` — showing a
co-stationary complement is stationary after two cofHead-style Fodor
applications — and stalled because two regressive functions each
constant on a stationary subset do NOT give two disjoint stationary
pieces. The successful route replaces it entirely:

1. **`omegaSeq α : ℕ → Ordinal`** — for `α.cof.ord = ω`, the `↑n`-th
   term of a fundamental sequence chosen via the NEW (2026-03) Mathlib
   API `Ordinal.exists_isFundamentalSeq : o.cof.ord = a → ∃ f : Iio a →
   Iio o, IsFundamentalSeq f`. Regressivity = `(f _).2`; cofinality of
   range = the `isCofinal_range` field. (The old
   `Ordinal.exists_fundamental_sequence` used by `cofHead` is deprecated
   at the pin — warnings only, but new code should use the new API.)
2. **Pigeonhole** (`exists_omegaSeq_high_fibers_stationary`): if every
   index `n` had a bound `η n < κ.ord` with `{α ∈ S | η n ≤ omegaSeq α
   n}` nonstationary (club `Dₙ` avoiding it), pick
   `α ∈ S ∩ ⋂ₙ Dₙ` above `⨆ₙ η n` (sup < κ.ord by regularity via
   `Ordinal.iSup_lt_of_lt_cof` + `Cardinal.mk_nat`; the point exists by
   `IsStationaryBelow.exists_gt` through the new club `Ioo β κ.ord`).
   Its whole ω-sequence is then bounded by the sup < α, contradicting
   `omegaSeq_cofinal`. So some `n` has ALL high-fibers stationary.
3. **Two Fodor applications** on `g = (omegaSeq · n)`: at `S` itself
   (constant `c₁`), and at the stationary high-fiber
   `{α ∈ S | c₁ + 1 ≤ g α}` (constant `c₂ ≥ c₁ + 1 > c₁`, witnessed via
   `IsStationaryBelow.nonempty`). Feed `c₁ ≠ c₂` into Part X's
   `stationary_splits_of_two_fibers`.

New supporting infrastructure: `isClubBelow_Ioo`,
`IsStationaryBelow.exists_gt`, `isClubBelow_iInter_nat` (countable club
intersections via `diagInter` with an `Ordinal.lt_omega0`-decoding
family), `omegaSeq` + `omegaSeq_lt` + `omegaSeq_cofinal`.

Main theorems: `stationary_splits_binary_of_cof_omega` (any regular
uncountable κ, S of ω-cofinal limits), `stationary_splits_binary_of_omega_cofinal_part`,
`cof_ord_eq_omega0_of_lt_aleph1`, `stationary_splits_binary_aleph1`.

## Lean gotchas hit

- `Ordinal.zero_le` does not exist at the pin; use root
  `pos_iff_ne_zero` (exactly how Mathlib's `Ordinal/Topology.lean:198`
  derives positivity from `IsAcc`).
- Deprecation warnings (not errors) at the pin: `isClosedBelow_iff`,
  `IsAcc.mono`, `push_neg` (→ `push Not`), `Ordinal.aleph0_le_cof`.
  All still usable; consistent with the parent file's existing style.

## What remains open (full Solovay = κ-piece partition)

- **κ-many pieces**: iterate step 3 transfinitely — for each `η < κ.ord`
  the high-fiber is stationary, giving unboundedly many constant values;
  collecting κ-many pairwise-distinct values needs a transfinite
  recursion (choice over κ-indexed family / `Classical.skolem`) plus the
  exhaustive-partition packaging. This is the S2-γ layer.
- **General κ beyond the ω-cofinal part**: the set
  `{α ∈ S | cf α < α}` needs the Jech 8.10 trace analysis when the
  ω-cofinal part of S is nonstationary (e.g. S concentrated on
  regulars below a Mahlo κ). At ω₁ this is vacuous (all limits are
  ω-cofinal), which is why the ω₁ theorem is complete.
