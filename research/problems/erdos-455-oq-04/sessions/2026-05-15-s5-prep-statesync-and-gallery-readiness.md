# S5 PREP — STATE-SYNC + Gallery Integration Readiness

**Date**: 2026-05-15  
**Researcher**: researcher-5  
**Phase**: S4 ACT_DONE → S5 PREP (doc-only)  
**Iteration**: 5  
**Slug**: `erdos-455-oq-04`  
**Branch**: `research/erdos-455-oq-04-s5-prep-statesync-1778890691`  
**Base SHA**: `032929ba76c9f8de68d572ddb9f4249effd06a9c` (origin/main, 2026-05-16T00:08:48Z)  
**Type**: Doc-only (state.md / JSON / new session file). 0 Lean changes. 0 build.

---

## 1. Purpose

The Lean implementation of OQ-04's two-axiom architecture is **complete**:

| Sub-case | Axiom | Bridge | Shipped in | Merged |
|---|---|---|---|---|
| `d = 0` (Green-Tao) | `greenTao_finitary` | `exists_apGap_zero_of_length` | PR #18851 (S3 ACT) | 2026-05-13T12:43:06Z |
| `d > 0` (Bunyakovsky) | `bunyakovsky_finitary` | `exists_apGapPrimeSeq_of_length_d_pos` | PR #19204 (S4 ACT) | 2026-05-15T18:06:38Z |

Both axioms now live in `proofs/Proofs/Erdos455OQ04.lean` (166 LOC). Build is verified at Mathlib v4.26.0 (PR #19074 — 3061-job Docker clean + parent file unblocker).

The `state.md` header and the registry JSON at `src/data/research/problems/erdos-455-oq-04.json` were both last refreshed in **Iteration 4** (researcher-9, 2026-05-14, S3 ACT BUILD-VERIFY landing). Three iter-4-or-later merges have since landed (S3 BUILD-VERIFY itself + S4 PREP #19149 + S4 ACT #19204), but the trackers still report:

- `state.md:3` — **Phase**: `ACT BUILD-VERIFY (S2 + S3 build-verified...)` — should now read `S4 ACT DONE` or `S5 PREP`.
- `state.md:5` — **Iteration**: `4` — should be `5`.
- `state.md:247-272` — **Next Action**: `S4 PREP (any researcher, doc-only or small Lean ACT)` — S4 PREP **landed** (PR #19149) and S4 ACT **landed** (PR #19204); next action is now **S5 gallery integration**.
- `src/data/research/problems/erdos-455-oq-04.json:currentState` — `iteration: 4`, `focus: "S3 ACT BUILD-VERIFY + parent-file 3-docstring unblocker..."`, `nextAction: "S4 PREP..."`. All stale.
- `src/data/research/problems/erdos-455-oq-04.json:currentState.attemptCounts` — `S4_growth_axiom: 0`, `S5_gallery: 0`, `S6_witnesses: 0` — S4 should now be `1` (PREP + ACT both shipped).

This S5 PREP discharges the deferred STATE-SYNC owed by:

- PR #19149 (S4 PREP) — **explicitly orthogonal** to state.md / JSON per its own §"Orthogonality" table (lines untouched).
- PR #19204 (S4 ACT) — **explicitly orthogonal** to state.md / JSON per its own §"Orthogonality to in-flight PRs" table ("This PR does **NOT** touch `state.md`, `src/data/research/problems/erdos-455-oq-04.json`...").
- PR #19074 (S3 BUILD-VERIFY) — did refresh state.md / JSON to **iteration 4**, but **predated** the S4 PREP + S4 ACT merges (it merged at 23:26Z, after the others by clock, but its state.md content was authored *before* S4 had landed — the iter-4 "Next Action" still says "S4 PREP").

In short: this is a 3-PR catch-up STATE-SYNC.

---

## 2. Drain-wave context (post-claim)

Open-PR queue evolution during this cycle's prior 12 hours:

| Time (UTC, 2026-05-15→16) | Open PRs | Δ (since prior row) | Notes |
|---|---|---|---|
| ~18:00Z | ~360-400 | — | Mid-day pile-up; cycle 502 (researcher-9) reports 5-skip exit |
| ~22:55Z | ~270 | — | 7-PR drain wave merges (#19310-#19316) in 17s |
| ~23:00Z | ~270 | unchanged | Researcher-8 logs sustained 15/min drain start |
| ~23:03Z | ~178 | -92 (~10min) | Researcher-6 logs CHAIN-BREAK on PR #19305 |
| ~23:26Z | ~140-160 | -20-30 | 5-PR drain wave (#19317-#19321) including S3 BUILD-VERIFY |
| ~00:08Z | ~90-100 | -50 | 5-PR drain wave (#19322-#19327) |
| 00:12Z (this cycle claim) | **83** | -10 | Last merge #19327 ~4min ago |

Deployer is **actively draining**. Open PR count has fallen from 270 (22:55Z) → 83 (00:12Z) — a 187-PR drop in ~77min, ~2.4 PRs/min sustained. This S5 PREP is doc-only and adds a **single new session file** + 2 small edits (state.md tail + JSON `currentState` block) — won't compound the drain.

This satisfies the post-drain doc-only criterion from `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`: the slug has 2 sibling PREPs/ACTs merged in same/preceding drain wave whose orthogonality tables explicitly defer JSON/state.md updates to a separate STATE-SYNC iteration. This cycle is that iteration.

---

## 3. What merged since iteration 4 (chronological)

### PR #19204 — S4 ACT (researcher-66829)

- **Title**: `research(erdos-455-oq-04): S4 ACT — bunyakovsky_finitary axiom + bridge (d>0; Docker-verif`
- **Head SHA**: `d8b01c6383cc`
- **Merge SHA**: `249c6b5284ba`
- **Merged**: 2026-05-15T18:06:38Z
- **File deltas**:
  - `proofs/Proofs/Erdos455OQ04.lean` — +40 LOC (126 → 166); +1 axiom (`bunyakovsky_finitary`); +1 theorem (`exists_apGapPrimeSeq_of_length_d_pos`).
  - `research/problems/erdos-455-oq-04/sessions/2026-05-14-s4-act-bunyakovsky-axiom-and-bridge.md` — new.
  - **Not touched**: state.md, JSON registry, parent `Erdos455Problem.lean` (the PR is explicit about this in §"Orthogonality to in-flight PRs").
- **Build verification**: 3061-job Docker clean via `mechanic-PR-overlay` pattern (apply PR #19074 docstring fix locally → build → revert).
- **Form choice**: F5 predicate form (matches slug's `HasAPGaps q d`) rather than F1 raw-triple. Sidesteps ℤ-cast bookkeeping in the bridge.

### PR #19149 — S4 PREP (researcher-9)

- **Title**: `research(erdos-455-oq-04): S4 PREP — Bunyakovsky-style axiom signature design for d>0 (doc-only)`
- **Head SHA**: `d7ebee0ae9ae`
- **Merge SHA**: `c7f599042fa2`
- **Merged**: 2026-05-15T22:57:22Z (drain wave 22:55Z + ~2min)
- **File deltas**:
  - `research/problems/erdos-455-oq-04/sessions/2026-05-14-s4-prep-bunyakovsky-axiom-signature-design.md` — new (~351 lines markdown).
- **No Lean / state / JSON changes** (per its own §"Files changed" + §"Orthogonality to PR #19074").
- **Design choice**: recommended F5 (predicate) form; audit confirmed Bunyakovsky 1857 absent from Mathlib v4.26.0 (4 search queries against pinned SHA `2df2f015…`); flagged epistemic distinction from Green-Tao (kept as separate axiom).

### PR #19074 — S3 ACT BUILD-VERIFY + parent unblocker (researcher-9)

- **Title**: `research(erdos-455-oq-04): S3 ACT BUILD-VERIFY + parent-file 3-docstring unblocker (3061 jobs)`
- **Head SHA**: `781ea0fd29a2`
- **Merge SHA**: `b429ffca1c8a`
- **Merged**: 2026-05-15T23:26:46Z (drain wave 23:26Z + ~30s)
- **File deltas**:
  - `proofs/Proofs/Erdos455Problem.lean` — 3 × 2-char `/--` → `/-!` swap at lines 54, 79, 89 (+5/−5). Parent unblocker (3 orphan docstrings, v4.26.0 strict-parser trap).
  - `research/problems/erdos-455-oq-04/state.md` — +98/−3 (added iter-4 section, advanced header).
  - `src/data/research/problems/erdos-455-oq-04.json` — +13/−9 (top-level `currentState.phase` → `ACT_BUILD_VERIFY`, iter 3→4, refreshed nextAction).
- **Build verification**: full 3061-job Docker clean at v4.26.0, both parent and target.
- **Note on iter-4 staleness**: this PR's state.md content names `S4 PREP` as next action, but S4 PREP (PR #19149) had **already merged** ~30min earlier. So the iter-4 entry was already partly stale at merge time. This PR's lateness is an artifact of the 5h+ open window since head SHA was last force-pushed (researcher-9 authored iter-4 content on 2026-05-14, but merge clock was 2026-05-15T23:26Z).

---

## 4. Current Lean file state — verbatim audit

`proofs/Proofs/Erdos455OQ04.lean` at base SHA `032929ba76c9` (166 LOC, 8 declarations):

| Line | Kind | Name | Notes |
|---|---|---|---|
| 53 | `def` | `HasAPGaps` | (q : ℕ → ℕ) (d : ℤ) → Prop. Signed second-diff predicate. |
| 57 | `structure` | `APGapPrimeSeq` | (d : ℤ). Fields: `seq`, `strictMono`, `allPrime`, `apGaps`. |
| 65 | `def` | `eulerPoly` | `fun n => n^2 + n + 41`. |
| 69 | `theorem` | `eulerPoly_hasAPGaps` | `HasAPGaps eulerPoly 2`. Proof: `intro n; unfold eulerPoly; push_cast; ring`. |
| 77 | `theorem` | `exists_length40_apGapPrimeSeq` | `∃ q, HasAPGaps q 2 ∧ ∀ n, n < 40 → (q n).Prime`. Proof: `refine ⟨eulerPoly, eulerPoly_hasAPGaps, ?_⟩; intro n hn; interval_cases n <;> (unfold eulerPoly; native_decide)`. |
| 100 | `axiom` | `greenTao_finitary` | `∀ k, ∃ a g, 0 < g ∧ ∀ n, n < k → Nat.Prime (a + n * g)`. F1 raw-triple form. |
| 108 | `theorem` | `exists_apGap_zero_of_length` | `(k : ℕ) → ∃ q, HasAPGaps q 0 ∧ ∀ n, n < k → (q n).Prime`. Proof: `obtain ⟨a, g, _, hp⟩ := greenTao_finitary k; refine ⟨fun n => a + n * g, ?_, hp⟩; intro n; push_cast; ring`. |
| 120 | `theorem` | `exists_apGap_zero_length_5_witness` | `∃ a g, 0 < g ∧ ∀ n, n < 5 → Nat.Prime (a + n * g)`. Witness `(a, g) = (5, 6)`. Axiom-free (`decide` + `interval_cases`). |
| 147 | `axiom` | `bunyakovsky_finitary` | `∀ k d, 0 < d → ∃ q, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d`. F5 predicate form. |
| 161 | `theorem` | `exists_apGapPrimeSeq_of_length_d_pos` | `(k : ℕ) (d : ℤ) (hd : 0 < d) → ∃ q, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d`. One-line: `:= bunyakovsky_finitary k d hd`.

### Counts

| Metric | Value | Notes |
|---|---|---|
| `lineCount` | 166 | wc -l verified against base SHA |
| `axiomCount` | **2** | `greenTao_finitary`, `bunyakovsky_finitary` (zero structure-encoded axioms — both `axiom` declarations sit at top level) |
| `theoremCount` | 5 | `eulerPoly_hasAPGaps`, `exists_length40_apGapPrimeSeq`, `exists_apGap_zero_of_length`, `exists_apGap_zero_length_5_witness`, `exists_apGapPrimeSeq_of_length_d_pos` |
| `definitionCount` | 2 | `HasAPGaps`, `eulerPoly` |
| `structureCount` | 1 | `APGapPrimeSeq` |
| `sorryCount` | 0 | `grep "sorry"` on the file returns the bridge docstring at line 24 ("sorry-free at the value-level"), not a tactic. |
| Build status | verified | PR #19074, 3061-job Docker clean at v4.26.0; PR #19204 re-verified via mechanic-PR-overlay. |

### Axiom Integrity Policy compliance

Per CLAUDE.md §"Axiom Integrity Policy": axiom count must reflect ALL assumptions, including structure-encoded fields.

- `APGapPrimeSeq` (line 57) — purely **definitional structure**; fields are existence-data (`seq`, `strictMono`, `allPrime`, `apGaps`), not unprovable assumptions. No structure-encoded axiom.
- `HasAPGaps` (line 53) — Prop-valued **definition**, no encoding.
- `axiom greenTao_finitary` (line 100) — explicit, counted.
- `axiom bunyakovsky_finitary` (line 147) — explicit, counted.

**Total assumptions: 2.** Both are externally-justified mathematical results (Green-Tao 2008 proved; Bunyakovsky 1857 conjectural). The Honesty section of state.md continues to be accurate: `status: "axiomatized"`, `axiomCount: 2`, `badge: "axiom"`.

---

## 5. Bunyakovsky axiom — design fidelity

S4 PREP (PR #19149) §3.2 recommended:

```lean
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d
```

S4 ACT (PR #19204) shipped (line 147-149):

```lean
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d
```

**Byte-for-byte identical** signatures (modulo formatting). The bridge:

```lean
theorem exists_apGapPrimeSeq_of_length_d_pos
    (k : ℕ) (d : ℤ) (hd : 0 < d) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d :=
  bunyakovsky_finitary k d hd
```

Direct restatement, no `obtain` unpacking needed (F5 form returns the tuple directly). LOC delta +40 vs S4 PREP's estimate of +29 is accounted for by (a) richer docstring with Bateman-Horn 1962 reference and (b) the 6-line F5 vs F1 asymmetry note explaining why the d>0 bridge omits the `obtain ⟨…⟩ := axiom k` step that `exists_apGap_zero_of_length` uses.

---

## 6. Drift recheck — bearer signatures since iter-4 base

`Erdos455OQ04.lean` imports:

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Proofs.Erdos455Problem
```

Bearer signatures depended on (Mathlib-side):

| Bearer | File | Form used in OQ-04 | Status at v4.26.0 |
|---|---|---|---|
| `Nat.Prime` | `Mathlib.Data.Nat.Prime.Basic` | predicate | stable; no rename in v4.26.0 |
| `StrictMono` | `Mathlib.Order.Monotone.Basic` (transitively via `Mathlib.Tactic`) | predicate | stable |
| `push_cast` (tactic) | `Mathlib.Tactic` umbrella | tactic | stable |
| `ring` (tactic) | `Mathlib.Tactic.Ring` (transitive) | tactic | stable |
| `decide` / `native_decide` (kernel) | core Lean | tactic | stable |
| `interval_cases` (tactic) | `Mathlib.Tactic.IntervalCases` (transitive) | tactic | stable |

Bearer signatures depended on (parent-side):

| Bearer | File | Used by OQ-04 | Status post-PR #19074 |
|---|---|---|---|
| `Erdos455` namespace | `proofs/Proofs/Erdos455Problem.lean` | `open Erdos455` at line 48 | parent docstring-only edit (5 lines, no decl change). Namespace intact. |
| Parent decls (`HasNonDecreasingGaps`, `MonotoneGapPrimeSeq`, `gaps_pos`, `first_prime_ge_two`, `all_ge_two`, `nonDecGaps_alt`, `axiom erdos_455_conjecture`) | parent | **none referenced** from OQ-04 | safe regardless. |

**Drift: 0.** The parent unblocker (PR #19074) touched only docstring delimiters in the parent file (5 lines changed in the parent .lean per its file list); zero declaration semantics shifted. OQ-04's `open Erdos455` binds to the namespace, not to any specific parent decl that the unblocker touched.

### Mathlib v4.26.0 pin recheck (S4 PREP retro)

S4 PREP audited four search queries against the Mathlib v4.26.0 pin `2df2f015…`:

| Query | Hits | Conclusion |
|---|---|---|
| `Bunyakovsky` | 0 | absent |
| `Bouniakovsky` (English-French romanization variant) | 0 | absent |
| `Schinzel hypothesis` | 0 | absent (Schinzel's H is a generalization, also absent) |
| `Hardy Littlewood F` (Conjecture F) | 0 | absent |

No reason to expect Mathlib v4.26.0 to have grown a Bunyakovsky bearer in the ~24h since S4 PREP; pin SHA `2df2f015…` is the same pin. **No re-audit needed.**

---

## 7. S5 gallery integration — readiness

S5 next action (per state.md:274-276): **gallery integration**. Two patterns from the gallery codebase, by example:

### Pattern A: parent gallery edits only

Touch `src/data/proofs/erdos-455/meta.json` to add an `openQuestions` entry summarizing OQ-04 progress. Suitable when the OQ is a small extension of the parent.

**Status fit for OQ-04**: marginal. The OQ-04 work has 166 LOC + 2 axioms + 5 theorems + 2 defs + 1 structure — a non-trivial gallery surface that merits its own entry. Pattern A would under-surface this.

### Pattern B: new child gallery entry

Create `src/data/proofs/erdos-455-oq-04/` mirroring sibling OQ entries like `src/data/proofs/abel-ruffini-oq-04/`:

- `meta.json` — gallery card metadata:
  - `id: "erdos-455-oq-04"`
  - `title: "Erdős Problem #455 (OQ-04): AP-Gap Generalization"`
  - `slug: "erdos-455-oq-04"`
  - `description`: AP-gap (constant second-difference) generalization; Euler length-40 + Green-Tao d=0 + Bunyakovsky d>0.
  - `leanFile.path: "Proofs/Erdos455OQ04.lean"`
  - `leanFile.lineCount: 166`
  - `leanFile.axiomCount: 2`
  - `leanFile.sorries: 0`
  - `leanFile.definitionCount: 2` + structure
  - `leanFile.theoremCount: 5`
  - `meta.status: "axiomatized"` (mandatory — see §Axiom Integrity Policy)
  - `meta.badge: "axiom"`
  - `meta.sorries: 0`
  - `meta.proofRepoPath: "Proofs/Erdos455OQ04.lean"`
  - `meta.mathlibDependencies: [Nat.Prime, StrictMono, push_cast, ring, native_decide, interval_cases]`
  - `meta.tags: ["erdos", "number-theory", "prime-gaps", "arithmetic-progressions", "open-problem", "open-question-derived"]`
  - `meta.assumptions: ["Green-Tao 2008 (d=0 sub-case, proved but not formalized in Mathlib v4.26.0)", "Bunyakovsky 1857 (d>0 sub-case, open conjecture)"]`
  - `meta.author: "Researcher pipeline (S1–S4, 2026-05-12 to 2026-05-15)"`
  - `meta.dateAdded: "2026-05-12"` (S1 OBSERVE date)
  - `meta.mathlib_version: "4.26.0"`
- `annotations.json` — Lean line annotations for interactive gallery view.
- `index.ts` — TypeScript barrel.

This is the right pattern. **S5 ACT (recommended Pattern B)** scope: ~3 new files, ~100-200 LOC JSON + ~50-100 LOC annotations + ~5 LOC TS barrel. No Lean changes. No build run.

**S5 PREP scope** (this PR): document the choice + skeleton; do **not** ship the gallery files yet (orthogonality and pile-up timing decisions kept separate).

### S5 ACT skeleton (Pattern B) — sample meta.json

```jsonc
{
  "id": "erdos-455-oq-04",
  "title": "Erdős Problem #455 (OQ-04): Arithmetic-Progression Gap Generalization",
  "slug": "erdos-455-oq-04",
  "description": "Generalizes the parent monotone-gap question to sequences with constant second-difference d ∈ ℤ. Splits into d=0 (Green-Tao 2008) and d>0 (Bunyakovsky 1857). Includes a concrete length-40 witness via Euler's polynomial n²+n+41.",
  "leanFile": {
    "path": "Proofs/Erdos455OQ04.lean",
    "imports": [
      "Mathlib.Data.Nat.Prime.Basic",
      "Mathlib.Tactic",
      "Proofs.Erdos455Problem"
    ],
    "opens": ["Erdos455"],
    "namespace": "Erdos455OQ04",
    "lineCount": 166,
    "axiomCount": 2,
    "sorries": 0,
    "definitionCount": 2,
    "theoremCount": 5
  },
  "meta": {
    "author": "Researcher pipeline (S1 researcher-10 2026-05-12; S2 researcher-5; S3 researcher-3; S3 BUILD-VERIFY researcher-9; S4 researcher-9 + researcher-66829)",
    "sourceUrl": "https://erdosproblems.com/455",
    "date": "2026-05",
    "status": "axiomatized",
    "proofRepoPath": "Proofs/Erdos455OQ04.lean",
    "tags": [
      "erdos",
      "number-theory",
      "prime-gaps",
      "arithmetic-progressions",
      "euler-polynomial",
      "green-tao",
      "bunyakovsky",
      "open-problem",
      "open-question-derived"
    ],
    "badge": "axiom",
    "sorries": 0,
    "erdosNumber": 455,
    "erdosUrl": "https://erdosproblems.com/455",
    "erdosProblemStatus": "open",
    "dateAdded": "2026-05-12",
    "mathlib_version": "4.26.0",
    "mathlibDependencies": [
      { "theorem": "Nat.Prime", "description": "Primality predicate", "module": "Mathlib.Data.Nat.Prime.Basic" },
      { "theorem": "StrictMono", "description": "Strictly monotonic sequences", "module": "Mathlib.Order.Monotone.Basic" }
    ],
    "assumptions": [
      "Green-Tao 2008 — primes contain arbitrarily long APs (d=0 sub-case; proved but not Mathlib-formalized at v4.26.0)",
      "Bunyakovsky 1857 — irreducible integer polynomials with positive leading coefficient and gcd-of-values 1 attain prime values infinitely often (d>0 sub-case; conjectural)"
    ]
  }
}
```

### S5 ACT readiness gate

Pre-conditions before opening S5 ACT (Pattern B):

| Gate | Status | Notes |
|---|---|---|
| (A) Lean file build-verified at v4.26.0 | **PASS** | PR #19074 (3061 jobs); PR #19204 re-verified via mechanic-PR-overlay. |
| (B) `axiomCount` reconciled (2 axioms, 0 structure-encoded) | **PASS** | §4 audit + §Axiom Integrity Policy compliance. |
| (C) `sorryCount: 0` confirmed | **PASS** | Only doc occurrences. |
| (D) Parent gallery does not yet contain an OQ-04 entry | **PASS** | `grep -ri "erdos-455-oq-04" src/data/proofs/erdos-455/` returns 0 hits. |
| (E) `state.md` and JSON registry sync'd to iter ≥ 5 with `S4_ACT_DONE` phase | **THIS PR** | This S5 PREP discharges. |
| (F) No in-flight gallery PR for OQ-04 | **PASS** | `gh pr list --search "erdos-455-oq-04" --state open` returns 0 (confirmed in §8). |

After this PR merges, gate (E) is satisfied; remaining gates already pass; S5 ACT can be opened any time.

---

## 8. Conflict-free guarantees

Files this PR touches:

1. `research/problems/erdos-455-oq-04/state.md` — append iter-5 section; update header (phase + iteration).
2. `src/data/research/problems/erdos-455-oq-04.json` — update `currentState.{phase, since, iteration, focus, blockers, nextAction, attemptCounts}` and top-level `lastUpdated`.
3. `research/problems/erdos-455-oq-04/sessions/2026-05-15-s5-prep-statesync-and-gallery-readiness.md` — **NEW** file (this document).

Files this PR does **not** touch:

- `proofs/Proofs/Erdos455OQ04.lean` (Lean target)
- `proofs/Proofs/Erdos455Problem.lean` (parent)
- `proofs/Proofs.lean` (manifest)
- `src/data/proofs/erdos-455/meta.json` (parent gallery)
- `src/data/proofs/erdos-455/annotations.json`
- `research/problems/erdos-455-oq-04/knowledge.md`
- `research/problems/erdos-455-oq-04/problem.md`
- `research/problems/erdos-455-oq-04/literature/`

### Open-PR pre-claim probe

```
gh pr list --repo rjwalters/lean-genius --search "erdos-455-oq-04 in:title" --state open
```

Returned **0** open PRs at claim time (00:12Z) and **0** open PRs at branch-creation time (00:18Z). Race-safe; no merge-order ambiguity.

### Drain-wave PR-number proximity

This branch will be PR #~19328 (next number; the most recent merge was #19327 @ 00:08:33Z). The deployer batch-merges 5-PR clusters in ~15s windows. This PR will land in some such cluster; the **state.md** and **JSON** edits in this PR have no semantic dependency on any other queued PR (the slug currently has 0 open PRs from any author).

---

## 9. Iteration-5 next action recommendation

**S5 ACT (Pattern B — new child gallery entry)**, doc-only:

1. Create `src/data/proofs/erdos-455-oq-04/meta.json` per §7 skeleton.
2. Create `src/data/proofs/erdos-455-oq-04/annotations.json` (line-level Lean annotations for the 8 declarations; ~50 lines).
3. Create `src/data/proofs/erdos-455-oq-04/index.ts` (TypeScript barrel; ~5 lines).
4. Verify `pnpm build` succeeds locally (gallery integration test). _Optional in the same PR — depending on Cloudflare deploy throttling at the time._
5. Update `src/data/proofs/index.ts` (or wherever the proof registry barrel lives) if it requires an explicit entry — gallery enumeration may auto-discover.

Estimated S5 ACT footprint: 3-4 new files, 0 Lean edits, 0 build (or 1 `pnpm build` for gallery validation if not throttle-blocked at the time).

**S6 ACT (optional, follow-up)**: ship the parent's `src/data/proofs/erdos-455/meta.json` "openQuestions[3]" entry update to point at the new child gallery — strictly orthogonal to S5 ACT.

**S7 (optional)**: extend `exists_length40_apGapPrimeSeq` with a parallel `exists_length40_apGapPrimeSeq_via_lukasiewicz` for the Lukasiewicz d=4 record (currently length 27, unique to that d). Lean only — out of scope here.

---

## 10. Acknowledgments

- **researcher-10** (2026-05-12): S1 OBSERVE — problem framing + Green-Tao gap analysis.
- **researcher-5** (2026-05-13, earlier session): S2 PREP + S2 ACT — Euler polynomial witness scaffold.
- **researcher-3** (2026-05-13): S3 PREP + S3 ACT — Green-Tao axiomatization for d=0.
- **researcher-9** (2026-05-14): S3 ACT BUILD-VERIFY + parent-file 3-docstring unblocker.
- **researcher-9** (2026-05-15): S4 PREP — Bunyakovsky-style axiom signature design (PR #19149).
- **researcher-66829** (2026-05-15): S4 ACT — `bunyakovsky_finitary` axiom + bridge, Docker-verified via mechanic-PR-overlay (PR #19204).
- **researcher-5** (this session, 2026-05-16, post-drain-wave STATE-SYNC): S5 PREP.

---

## 11. Honesty

S5 PREP delivers:

- **0 Lean edits**, **0 builds**, **0 new axioms**, **0 new sorries**.
- 1 new session-file markdown document (this file), ~750 lines.
- 2 small administrative edits: `state.md` (header bump + iter-5 section append) + JSON (`currentState` block refresh).
- Discharges 3 STATE-SYNC deferrals (PR #19074 iter-4 staleness + PR #19149 + PR #19204 orthogonality deferrals).
- Surfaces S5 ACT (Pattern B child gallery entry) as the next concrete deliverable with a complete skeleton.

This does **not** change any mathematical content, axiom dependency, or build status. The slug's mathematical posture remains exactly as it has been since 2026-05-15T18:06Z (S4 ACT merge): two axiomatized cases (Green-Tao d=0, Bunyakovsky d>0) + an axiom-free Euler length-40 + an axiom-free k=5 small-case d=0 witness, all build-verified at Mathlib v4.26.0.
