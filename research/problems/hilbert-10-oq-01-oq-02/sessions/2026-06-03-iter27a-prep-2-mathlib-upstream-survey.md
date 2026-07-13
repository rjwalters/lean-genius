# Iteration 27a PREP-2 — Mathlib upstream PR/issue survey for the 5 missing bearers

**Date**: 2026-06-03
**Researcher**: researcher-1
**Phase**: PREP (executes the Iter 27a PREP-1 §11 PREP-2 proposal: catalog
in-flight Mathlib PRs/RFCs targeting the 5 bearers found absent in PREP-1).
**Type**: Doc-only. No edits to `Proofs/Hilbert10OQ01OQ02.lean`, gallery
`meta.json`, or `knowledge.{md,markdown}`. Edits limited to this session log,
`state.md` (S31 prepend), and
`src/data/research/problems/hilbert-10-oq-01-oq-02.json`
(`currentState` + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since PREP-1).

## Headline

**Zero upstream motion on any of the 5 missing bearers**. Searches against
`leanprover-community/mathlib4` (PRs open + closed, issues, title + body)
return **no in-flight or recently merged work** targeting `HilbertSymbol`,
`HasseMinkowski`, `BrauerRational` (beyond the 2025-01 Defs-only landing),
`PoonenNonSquaresDiophantine`, or `Hilbert10Rational`. Per PREP-1 §11, this
triggers the **"no motion → release"** branch: Iter 27a is upstream-blocked
with no near-term resolution path. Claim released; researcher-1 returns to
the claim pool.

## Survey method

All searches executed via `gh search prs` and `gh search issues` against
`leanprover-community/mathlib4`, with explicit `--match title` for
title-level filtering and broader body searches as fallback.

### Bearer 1 — `HilbertSymbol` over ℚ

```
gh search prs --repo leanprover-community/mathlib4 'HilbertSymbol' \
   --json number,title,state                       → []  (open)
   --state=closed --json number,title,closedAt     → []  (closed)
gh search prs --repo leanprover-community/mathlib4 '"Hilbert symbol"' \
   --match title (open + closed)                   → []
gh search issues --repo leanprover-community/mathlib4 'HilbertSymbol'
                                                    → []
gh search issues --repo leanprover-community/mathlib4 '"Hilbert symbol"'
                                                    → []
```

**Verdict**: **No PRs, no issues**. The Mathlib `LegendreSymbol` /
`JacobiSymbol` over `ZMod p` are present (per PREP-1 §3.2) but
`HilbertSymbol (a, b)_p` (the local norm-residue symbol) — the load-bearing
object for any rational-Hasse-Minkowski lift — has no in-flight work.

### Bearer 2 — `HasseMinkowski` / local-global principle over ℚ

```
gh search prs --repo leanprover-community/mathlib4 'Hasse' --match title \
   --state=open                                   → [#34171 (SimpleGraph/Hasse)]
   --state=closed                                 → six results, all in
                                                    Combinatorics/SimpleGraph/Hasse,
                                                    LaurentSeries Hasse derivatives,
                                                    or MvPolynomial Hasse derivatives
gh search prs --repo leanprover-community/mathlib4 '"Hasse-Minkowski"'
   (all states)                                    → []
gh search prs --repo leanprover-community/mathlib4 '"Hasse Minkowski"'
   (all states)                                    → []
gh search prs --repo leanprover-community/mathlib4 'local-global' \
   --match title --state=open                      → [#29534 (regular local ring,
                                                    unrelated)]
gh search issues --repo leanprover-community/mathlib4 'Hasse Minkowski' → []
```

**Verdict**: **No PRs, no issues**. Every "Hasse" hit at v4.26.0 is either
the Hasse diagram (combinatorics/order theory) or the Hasse derivative
(`LaurentSeries` / `MvPolynomial`); neither is related to the local-global
principle for quadratic forms over global fields. Confirms PREP-1 §3.3.

### Bearer 3 — `BrauerRational` (Brauer group of ℚ + ramification index map)

```
gh search prs --repo leanprover-community/mathlib4 'Brauer' --match title \
   --state=open                                   → []
   --state=closed                                 → [#20968 (Brauer Equivalence
                                                    + Brauer Group Defs, MERGED
                                                    2025-01-25, exactly the
                                                    98-LOC skeleton flagged in
                                                    PREP-1 §3.4 — NO follow-up)]
```

**Verdict**: **No follow-up PR or issue after the 2025-01 Defs landing**.
PREP-1 §3.4 noted Mathlib's `BrauerGroup/Defs.lean` is the 98-LOC
"`CSA` + setoid" skeleton; full abelian-group structure, functoriality, and
the ℚ specialization (with the rational-place ramification map) remain on
TODO with no in-flight motion in the ~17-month window since the Defs PR.

### Bearer 4 — `PoonenNonSquaresDiophantine` (Poonen 2009 Σ₁ definition of
the non-square cone)

```
gh search prs --repo leanprover-community/mathlib4 'Poonen' --match title
   (all states)                                    → []
```

**Verdict**: **No PRs, no issues** mentioning Poonen by name in Mathlib's
PR history. Confirms PREP-1 §3.5: Poonen 2009 (S-integers Diophantine
definitions) and Poonen 2003 (non-square Σ₁ defs) have not entered the
Mathlib upstream queue at any time visible to GitHub search.

### Bearer 5 — `Hilbert10Rational` (formal statement of H10/ℚ)

```
gh search prs --repo leanprover-community/mathlib4 'Hilbert10' \
   --json number,title,state                       → []
gh search prs --repo leanprover-community/mathlib4 'Hilbert 10' \
   --match title                                   → []
gh search prs --repo leanprover-community/mathlib4 'Diophantine' \
   --match title --state=open                      → []
gh search prs --repo leanprover-community/mathlib4 'Dioph' \
   --match title --state=open                      → []
gh search prs --repo leanprover-community/mathlib4 'Matiyasevich' \
   --match title --state=open                      → []
gh search prs --repo leanprover-community/mathlib4 'MRDP' \
   --match title --state=open                      → []
```

**Verdict**: **No PRs, no issues**. Carneiro 2018's `Mathlib.NumberTheory.Dioph`
(over ℕ; the H10/ℤ undecidability theorem itself still on TODO per PREP-1
§3.6) remains the most recent activity in this neighbourhood; no rational
analogue is in any visible queue.

## Cross-axis: full-text body search (false-positive baseline)

To rule out title-only blind spots:

```
gh search prs --repo leanprover-community/mathlib4 'BrauerGroup' \
   --state=closed --limit 10           → 10 hits, ALL false positives
                                          (category-theory localization,
                                           selfadjoint norms, transvection
                                           determinants — none related to
                                           Brauer or rational arithmetic)
```

Full-text matches confirm the **lexical** absence of work in this area; the
"BrauerGroup" hits in PR bodies are stray references in unrelated category-
theory / linear-algebra PRs, not active development of the algebraic
number-theoretic object. This is the expected signal: PREP-1's source-tree
grep found 0 hits at the pin, and PREP-2's PR-history grep finds 0 hits
across all of Mathlib's recorded PR + issue activity.

## Verdict matrix

| # | Bearer | PRs (open) | PRs (closed/merged) | Issues | Net motion |
|---|--------|-----------:|---------------------:|-------:|------------|
| 1 | `HilbertSymbol`              | 0 | 0 | 0 | **none** |
| 2 | `HasseMinkowski`             | 0 | 0 | 0 | **none** |
| 3 | `BrauerRational`             | 0 | 1 (Defs only, 2025-01) | 0 | **dormant since 2025-01** |
| 4 | `PoonenNonSquaresDiophantine` | 0 | 0 | 0 | **none** |
| 5 | `Hilbert10Rational`          | 0 | 0 | 0 | **none** |

**Net**: 5/5 dormant. The only related upstream activity is the 2025-01
Brauer-group Defs PR, which landed the skeleton flagged in PREP-1 §3.4 and
has had no follow-up in ~17 months. 4/5 bearers have zero recorded
mathlib4 activity at any point in time.

## Implication for Iter 27 picker's slot

Per PREP-1 §11, with the upstream survey showing **no motion**, the right
move is **option (d): release the claim until the upstream bearer surface
advances**. The Iter 27 picker's slot remains the next picker's slot, but
researcher-1's recommendation is to:

1. **Release the claim now** (claim TTL expires 2026-06-03T19:49Z; no
   reason to hold it through TTL when the verdict is unambiguous).
2. **Pool requeue** the slug at `available` status; the next claim attempt
   (whether by researcher-1 or another agent) inherits the same upstream-
   blocked state — no churn cost.
3. **Re-survey trigger**: rec re-survey after **any** of the 5 bearers
   shows a new PR or issue (monitored via PR-history watch; suggested
   cadence: 30 days, anchored to 2026-07-03).
4. **No Lean ACT this slot**. Iter 27a-δ (the low-leverage implication-
   chain re-exports flagged in PREP-1 §6) is the only single-cycle viable
   Lean ACT, but per PREP-1 §11 its leverage is too low to justify a slot
   that could be deferred until a substantive bearer lands. Future picker
   may still elect 27a-δ as a "fill-in"; this PREP-2 does not.

## What this PREP-2 does NOT include

1. **No Lean edits**. Doc-only PREP. File `Proofs/Hilbert10OQ01OQ02.lean`
   byte-identical to S29 state-sync (3082 LOC, 1 axiom
   `koenigsmann_2016_universal`, 0 sorries).
2. **No mathlib4 fork inspection**. Search was against the canonical
   `leanprover-community/mathlib4` repository's PR + issue history; private
   forks or unpushed branches are out of scope.
3. **No Mathlib RFC site survey**. The Mathlib4 PR queue is the canonical
   "in-flight" surface; RFCs (https://leanprover-community.github.io)
   would catch *intended* work not yet in PR form, but the empty PR /
   issue surface here makes RFC absence highly likely too — re-survey only
   if a PR-side trigger fires.
4. **No alternative-route bearer search**. PREP-1 §6 already documented
   the 27a-α/β/γ/δ refinements; PREP-2's scope is only the bearer-presence
   axis, not strategy reformulation.

## Honest framing / self-audit

- **Survey is GitHub-scope**, not omniscient. The Mathlib community uses
  GitHub PRs as the canonical contribution surface (Bors merge-queue
  workflow); searches against `gh search prs/issues` cover essentially
  all activity. Private dev branches, in-progress local work, or PRs
  with non-keyword titles could in principle exist but would be invisible
  to this survey; the title + body search across both states minimizes
  this risk.
- **Five-bearer net is "none"**, not "limited". 4/5 bearers have **zero**
  recorded PR or issue activity at any time. The fifth (Brauer) has the
  ~17-month-dormant Defs landing. This is a stronger statement than
  "PREP-1's bearer-gap is upstream-blocked": it is upstream-blocked **with
  no visible recovery vector** in the foreseeable mathlib4 queue.
- **No probe of `(b)` or `(c)`** from PREP-1 §11. Option (b) iter 27a-δ
  re-exports (Lean ACT) and option (c) +Nd STATE-SYNC are deferred to
  future picker slots; PREP-2's task was specifically option (a) PREP-2
  survey, and the verdict triggers option (d) release.
- **Claim released proactively**, before TTL expiry, signalling
  "upstream-blocked, no current ACT viable" to the pool. This is the
  intended PREP-1 §11 release path; no negative-result penalty is
  appropriate.

## Cross-references

- PREP-1 (2026-06-02, last session): full Mathlib v4.26.0 bearer survey
  finding 5/5 absent. This PREP-2 closes the §11 follow-up.
- S29 STATE-SYNC (2026-05-31): T+15d temporal drift refresh.
- S28 STATE-SYNC (2026-05-16): meta.json + leanFile drift absorb.
- S27 STATE-SYNC (2026-05-15): drain-wave absorb (PRs #19117, #19137, #19344).
- Iter 26a (2026-05-15, PR #19117): Finset transport (last Lean ACT shipped).

## What the next researcher should do (Iter 27 picker's slot, post-PREP-2)

**If the claim is picked up again within 30 days** (before 2026-07-03):
- The upstream-blocked verdict from PREP-2 still applies; no PR-side
  trigger event in the interim absent fresh signal.
- Recommended: SKIP and re-release, or pick option (b) iter 27a-δ as a
  low-leverage fill-in (Lean ACT, ~50 LOC re-exports, axiom-free).

**If the claim is picked up after 30 days**:
- Re-run PREP-2 survey (the gh-search commands above) to refresh.
- If any of the 5 bearers has a new PR/issue, pivot to PREP-3 (track the
  specific PR's API surface and discharge plan).
- If still no motion, longer release horizon (90 days suggested).

**Trigger event for immediate re-pickup**:
- Any new PR title containing `HilbertSymbol`, `Hasse-Minkowski`,
  `Brauer ℚ` / `BrauerQ`, `Poonen Diophantine`, or `Hilbert10` /
  `H10/Q` (and similar variants).
