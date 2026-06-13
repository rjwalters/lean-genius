# iter7 S6 AUDIT — `Legendre.legendre_conjecture` is a dead axiom assuming the OPEN conjecture

**Slug:** `bertrands-postulate-oq-02` (Legendre's conjecture for square intervals)
**Researcher:** researcher-1
**Date:** 2026-06-13
**Phase:** OBSERVE / AUDIT (build-free — Docker hung [`docker info`/`docker run` time out], Aristotle 404; 0 Lean edits)
**Predecessor:** iter6 S5-ACT-B′ (researcher-2, 2026-06-12, PR #22905 — `prime_gap_sqrt_bound_above_implies_legendre`, Docker-verified before the current daemon hang)

## Finding

`proofs/Proofs/LegendrePartial.lean:148` declares

```lean
axiom legendre_conjecture : LegendreConjecture
```

inside `namespace Legendre` (lines 18–165). This axiom **directly asserts the
open Legendre conjecture** — the strongest possible assumption, with no
hypotheses. It is a vestige of an early iteration that "stated the full
conjecture as an axiom" (its own docstring, lines 142–147).

**It is dead.** Across the entire `proofs/Proofs/` tree, `legendre_conjecture`
(the `Legendre.`-namespaced one) appears only in:

- its declaration (`LegendrePartial.lean:148`), and
- three **docstring/comment** lines: `LegendreGapEquivalence.lean:38` and `:197`,
  `LegendrePrimeGapSqrtBoundSuffices.lean:257`.

No theorem anywhere invokes it as a term (verified:
`grep -rn legendre_conjecture proofs/Proofs/` → every non-declaration hit is a
comment). The separate `axiom legendre_conjecture (n) (hn : n ≥ 1) : …` in
`BertrandsPostulateOQ03.lean:194` is a *different* axiom in a different
namespace/slug and is unrelated.

**The sibling docstrings are inaccurate.** `LegendreGapEquivalence.lean:38`
claims "This file … uses `Legendre.legendre_conjecture`." It does not. That
file's theorems are:

- unconditional reformulation **equivalences** (`legendreAt_iff_gap`,
  `legendre_iff_distance_form`, …) — proved with no assumption, and
- small-case **instances** (`legendre_gap_1 := (legendreAt_iff_gap 1).mp
  legendre_1`) — discharged from the `native_decide` witnesses `legendre_1 … legendre_20`
  in `LegendrePartial.lean`, **not** from the conjecture axiom.

The whole honest architecture of this slug is the *conditional* reduction
(`LegendrePrimeGapSqrtBoundSuffices.lean`: "if the √-prime-gap bound holds then
Legendre", 0 axioms) plus reformulation equivalences (0 axioms). None of it
needs — or uses — the brute `legendre_conjecture` axiom.

## Why it matters (axiom integrity)

An `axiom` asserting an open conjecture is the most assumption-heavy artifact a
gallery file can contain. Here it is also **unused**, so it buys nothing and
only:

- inflates the slug's true assumption count, and
- creates a live footgun: any future theorem that does `exact
  Legendre.legendre_conjecture …` would be silently assuming the open problem
  while looking "proved".

Removing it is genuine **axiom elimination** (the highest-value researcher
action per the role guide) and costs no mathematical content, because the
conditional reductions stand on their own.

## Recommended ACT (build-gated — do NOT blind-ship under the blackout)

When a reliable build is available:

1. **`#print axioms` confirmation first.** Syntactic non-usage is strong but the
   definitive check is: for the slug's headline theorems
   (`prime_gap_sqrt_bound_above_implies_legendre`, the `legendre_iff_*`
   equivalences, the `legendre_gap_*` instances), run `#print axioms <thm>` and
   confirm `Legendre.legendre_conjecture` is **not** in any axiom set. (Expected:
   only `propext`/`Classical.choice`/`Quot.sound` + `native_decide`'s
   `Lean.ofReduceBool`.)
2. **Delete** `axiom legendre_conjecture : LegendreConjecture`
   (`LegendrePartial.lean:148`) and its lead-in docstring (lines ~142–147).
3. **Fix the two inaccurate docstrings**: `LegendreGapEquivalence.lean:38` and
   the `:197` / `LegendrePrimeGapSqrtBoundSuffices.lean:257` "uses
   `Legendre.legendre_conjecture` … is unchanged" notes — replace with the truth
   (the files are unconditional; the small cases come from the `native_decide`
   witnesses).
4. **Rebuild** all dependents
   (`Proofs.LegendrePartial`, `Proofs.LegendreGapEquivalence`,
   `Proofs.LegendrePrimeGapSqrtBoundSuffices`,
   `Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle`, `Proofs.lean`)
   to confirm nothing referenced it.

Expected delta: the slug's `LegendrePartial.lean` axiomCount 1 → 0; no theorem
lost. If `#print axioms` reveals a transitive dependence I missed (it should
not, given zero syntactic uses), keep the axiom and instead correct the
docstrings only.

## Honest accounting

- Lean delta: none (removal is build-gated; the blackout bars verification).
- Evidence level: syntactic non-usage is **verified** repo-wide; transitive
  axiom-independence is **not** yet confirmed (`#print axioms` needs a build).
- This is an axiom-integrity audit lead, not a discharge. The slug's recent
  conditional-reduction work (iter6) is sound and unaffected.
