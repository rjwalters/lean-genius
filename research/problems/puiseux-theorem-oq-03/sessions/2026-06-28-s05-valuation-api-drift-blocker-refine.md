# 2026-06-28 — S05: Refining the analytic-bridge blocker (Mathlib valuation-API drift)

**Researcher**: researcher-5
**Branch**: `research/puiseux-theorem-oq-03-work`
**Mode**: ORIENT (re-assess the standing blocker against the drifted Mathlib cache)
**Outcome**: doc-only. No Lean change — the combinatorial API is complete and the
remaining open core is confirmed **BLOCKED**, but the blocker is now stated *precisely*
(which primitive is present, which is absent) instead of "no Mathlib bearer".

## Context

By the end of S04 + the 2026-06-28 researcher-1 session, the **combinatorial** Newton
polygon theorem is fully formalized in `proofs/Proofs/PuiseuxTheoremOQ03.lean`
(1081 lines, 53 theorems, **0 sorries / 0 axioms**): all three invariants —
sorted edge slopes (valuations), positive widths summing to the index span
(multiplicities), and the slope×width vertical drop (valuation of the root product) —
now hold on the **same concrete hull** `exists_lowerHull` produces.

The single remaining gap is the **analytic bridge**: slopes/widths of the polygon ↔
actual valuations/multiplicities of the roots of `P ∈ K⸨x⸩[Y]`. Every prior session
recorded this as "blocked on a `K((x))[Y]` valuation API absent from Mathlib 4.26.0."

## What I checked (against the live `.lake` Mathlib cache, drifted past 4.26.0)

**PRESENT — the base-field valuation now exists.** `Mathlib/RingTheory/LaurentSeries.lean`
provides a genuine valuation on `K⸨X⸩`:

- `Valued.v : Valuation K⸨X⸩ ℤᵐ⁰` with `valuation_def : Valued.v = (PowerSeries.idealX K).valuation _`.
- Monomial API: `valuation_X_pow (s : ℕ)`, `valuation_single_zpow (s : ℤ)`,
  `coeff_zero_of_lt_valuation`, `valuation_le_iff_coeff_lt_eq_zero`,
  `eq_coeff_of_valuation_sub_lt`, plus the `RatFunc`/adic-completion comparison theorems.

This is strictly more than the "absent" the standing note assumed — the **base field**
`K⸨x⸩` is now a valued field in Mathlib, integer (`ℤᵐ⁰`) valued.

**ABSENT — the Puiseux extension, the object the bridge actually needs.**

- No `PuiseuxSeries` anywhere in the cache (`find -iname '*puiseux*'` → ∅;
  `grep -rln 'PuiseuxSeries\|Puiseux'` → ∅).
- No ℚ-valued / rational-exponent valuation (`HahnSeries ℚ K` model) → ∅.

## Why this is the precise blocker (not cosmetic, a real type mismatch)

The polygon's edge slopes / root valuations are **`ℚ`-valued** (`edgeSlope : ... → ℚ`,
`rootValuation`), because the roots of `P ∈ K⸨x⸩[Y]` live in the **ramified** Puiseux
field `K⸨x^{1/n}⸩`, whose valuation is `ℚ`-valued (a root of `Y² − x` has valuation `½`).
The valuation Mathlib now supplies is on the **unramified** base `K⸨x⸩` and is
**`ℤᵐ⁰`-valued**. So the available primitive cannot even *state* the correspondence
`edgeSlope = −v(root)` — the codomains (`ℚ` vs `ℤ`) don't match without first
constructing the ramified Puiseux extension and its `ℚ`-valued valuation.

**Verdict: still BLOCKED**, now for a concrete reason. The missing primitive is a
`PuiseuxSeries` / `HahnSeries ℚ K` field together with its `ℚ`-valued valuation (and
the fact that `K⸨x⸩` embeds with the valuation scaling by the ramification index).
This is foundational, >1000-line Mathlib-grade infrastructure that does not exist
upstream — squarely the role's BLOCKED category (needs > 1000 lines foundational work),
not a tactic-search gap. Submitting it to Aristotle would not help (no statement to prove
until the field is built).

## Concrete pointer for the next ACT session (if/when attempted)

The smallest real step toward the bridge is to **construct the valued Puiseux field**,
not to add more combinatorial lemmas:

1. Define `PuiseuxSeries K := ⋃ₙ K⸨x^{1/n}⸩` (or `HahnSeries ℚ K` restricted to
   finitely-generated-denominator support) and its `ℚ`-valued valuation.
2. Prove `K⸨x⸩ ↪ PuiseuxSeries K` scales valuation by the ramification index.
3. Only then is `edgeSlope = −v(root)` statable; the combinatorial side (this file)
   already supplies everything on the polygon side.

Until (1)–(3) exist upstream or are built here as a separate large infrastructure PR,
`puiseux-theorem-oq-03` is **combinatorially complete, analytically blocked**.

## Verification

No Lean edit this session; the file remains the S04+researcher-1 state (verified
`0 sorries / 0 axioms`). Findings above are from reading the in-tree Mathlib cache
`proofs/.lake/packages/mathlib/Mathlib/RingTheory/LaurentSeries.lean` and exhaustive
`find`/`grep` for Puiseux/rational-valuation modules.
