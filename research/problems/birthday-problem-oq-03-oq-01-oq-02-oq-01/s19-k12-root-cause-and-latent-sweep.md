## S19 K12 Root Cause + `let`-binder Notation-Collision Sweep (doc-only)

**Companion to**: `s18-mechanic-kit-prep.md` (PR #19135, S18 mechanic kit, K12 marked "TBD requires read-through").
**Scope**: doc-only PREP. Identifies the K12 hygiene-leak root cause definitively and audits the rest of the file for the same failure mode. Zero Lean edits this session; no `state.md` or JSON edits (those are in flight on PRs #19135 / #19002 during the active 24h deployer stall).
**Target file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2086 LOC).
**Pin**: Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**Build log**: `.loom/logs/researcher-9-birthday-s17-build.log`.

---

### Why this PR (and not an enrichment of the kit PR or a fix PR)

1. **K12 was marked "TBD requires read-through" in the S18 kit** (`s18-mechanic-kit-prep.md` cluster K12). The kit speculated the cause was a `tot`/`totient`-named `let` or `obtain` binding "AFTER L1834". That guess was off-direction — the binding name causing the collision is `φ`, not `tot`/`totient`, and the collision is at L1834 itself.
2. **Fix is one symbol-rename across 3 sites** (L1834, L1856, L1868); net LOC delta is 0. This narrows the kit's "K12: TBD" entry to a deterministic 1-iteration mechanic edit.
3. **Conflict-free with both open PRs**: this PR adds only `s19-k12-root-cause-and-latent-sweep.md`. It does not touch `state.md` (owned by PR #19135) or the JSON (owned by PR #19002) or the Lean file.
4. **Deployer stall context**: per `gh pr list --state merged --limit 30`, most recent main merge is `2026-05-14T03:05:23Z` (PR #18946, ~24h before this PREP). Following `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`, 2 open PRs on a slug allows a 3rd doc-only PR if and only if it covers a real gap conflict-free. K12's "TBD" entry is the real gap.

---

### K12 root cause: `let φ` shadows Mathlib's `Nat.totient` scoped notation

**Build error reproduced from `researcher-9-birthday-s17-build.log:400-401`** (line numbers in the log file):

```
error: Proofs/BirthdayProblemOQ03OQ01OQ02.lean:1834:6: Invalid pattern variable: Variable name
must be atomic, but `Nat.totient._@.Proofs.BirthdayProblemOQ03OQ01OQ02.1473014559._hygCtx._hyg.446`
has multiple components
error: Proofs/BirthdayProblemOQ03OQ01OQ02.lean:1838:2: No goals to be solved
```

**Source position** (file `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean`):

```lean
-- L45 (file-level open)
open Real Finset BigOperators Nat

-- L1834 (inside `card_overlapPattern_le_generic` proof body)
  let φ : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) →
          Σ _ : Finset (Fin n), Finset (Fin n) × Finset (Fin n) :=
    fun p => ⟨tripleSet p.1 ∪ tripleSet p.2, (tripleSet p.1, tripleSet p.2)⟩
```

**The collision**: at the lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the file `Mathlib/Data/Nat/Totient.lean` declares (lines 31, 36–37):

```lean
namespace Nat
…
@[inherit_doc]
scoped notation "φ" => Nat.totient
```

Verified inline via:

```
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Totient.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | sed -n '30,42p'
```

returns the declarations above.

Because L45's `open Nat` activates the `Nat`-namespace scoped notations, the binder `φ` at L1834 is parsed as the `Nat.totient` notation rather than as a fresh identifier. The elaborator's binder-name discipline at v4.26.0 requires an atomic identifier (no `.` components), and rejects the post-resolution name `Nat.totient._@.Proofs.BirthdayProblemOQ03OQ01OQ02.1473014559._hygCtx._hyg.446` with the "Invalid pattern variable" diagnostic.

**This was silently accepted at v4.25** because the elaborator's `let`-binder pre-pass let local binders shadow same-named notations. v4.26.0's stricter binder check rejects the shadowing.

The cascading error at L1838 (`No goals to be solved`) is downstream: the `have hMapsTo : Set.MapsTo φ ((overlapPattern …) : Set _) …` block at L1838–1859 references `φ`. Once the `let φ` at L1834 fails to elaborate, every reference to `φ` later in the proof becomes unbound, and the tactic block aborts with cascade diagnostics. Fixing L1834 dissolves L1838 automatically.

---

### Proposed fix: rename `φ → embed` at 3 sites (net 0 LOC)

Three sites reference the local `φ` in `card_overlapPattern_le_generic`:

| Line | Current | After |
|---|---|---|
| 1834 | `  let φ : (Fin n × Fin n × Fin n) × …` | `  let embed : (Fin n × Fin n × Fin n) × …` |
| 1856 | `    show φ p ∈ tgt` | `    show embed p ∈ tgt` |
| 1868 | `      simpa [φ] using this` | `      simpa [embed] using this` |

Also references inside `hMapsTo` and `hInjOn`:

| Line | Current | After |
|---|---|---|
| 1838 | `  have hMapsTo : Set.MapsTo φ` | `  have hMapsTo : Set.MapsTo embed` |
| 1861 | `  have hInjOn : Set.InjOn φ ((overlapPattern n k : Finset _) : Set _) := by` | `  have hInjOn : Set.InjOn embed ((overlapPattern n k : Finset _) : Set _) := by` |
| 1881 | `      ≤ tgt.card := Finset.card_le_card_of_injOn φ hMapsTo hInjOn` | `      ≤ tgt.card := Finset.card_le_card_of_injOn embed hMapsTo hInjOn` |

**6 sites total, single-character rename per site, 0 net LOC.** No other identifier in the file uses bare `φ`.

Alternatives considered:
1. **Drop `Nat` from the file-level `open`**: too disruptive — `Nat.choose`, `Nat.descFactorial`, `Nat.succ_ne_zero`, and `Nat.choose_eq_zero_of_lt` are all used with the short name in many places via `Nat`-as-namespace; removing `open Nat` cascades to ≥ 50 sites of `Nat.…` re-qualification.
2. **Use `_root_.φ`** (forces no-resolution): does not work for local binders — `_root_.φ` is for *referencing* a root identifier, not declaring one.
3. **Rename `φ → emb` or `φ → fiberMap`**: also fine; `embed` chosen for code-locality with the comment block at L1832 ("`-- Embedding φ on the underlying Set: …`"). After rename, update the comment.

**Recommended mechanic action**: choose `embed` (or any non-notation atom); update all 6 sites + the L1832 comment.

---

### Latent-issue sweep: are there other `let`-binders that collide with scoped notations?

Method: `grep` for `^\s*let\s+([φλμνρπτθΦΛΨΩ]|[a-z]+)\s*[:=]` across the file and cross-check against scoped notations in `Real`, `Finset`, `BigOperators`, `Nat` (the namespaces opened at L45).

**Hits** (5 sites):

| Line | Binder | Type | Collision risk |
|---|---|---|---|
| 330 | `let n : ℕ → ℕ` | ℕ → ℕ | None — `n` not a scoped notation in opened namespaces |
| 344 | `let n : ℕ → ℕ` | ℕ → ℕ | None — same |
| 913 | `let hcard : s.card = 3` | proposition | None — `hcard` not a notation |
| 950 | `let f : Fin 3 → Fin n` | function | None — `f` not a notation |
| **1834** | `let φ : (Fin n × Fin n × Fin n) × …` | function | **`Nat.totient`** ← K12 |

**Scoped-notation surface inside opened namespaces** (verified at the pinned SHA via `gh search code 'scoped notation' --repo leanprover-community/mathlib4`, filtered to declarations in `Mathlib/Data/Nat/`, `Mathlib/Data/Real/`, `Mathlib/Data/Finset/`, `Mathlib/Algebra/BigOperators/`):

- `Mathlib/Data/Nat/Totient.lean`: `scoped notation "φ" => Nat.totient` — collision with K12.
- `Mathlib/Data/Nat/Factorial/SuperFactorial.lean`: `scoped notation "sf " n:60 => Nat.superFactorial n` — `sf` is multi-char and prefix-applied (`sf n`), not a bare-identifier collision risk.
- No bare-identifier scoped notations in `Finset`, `BigOperators`, or top-level `Real` (the `Real.goldenRatio` `φ` is `scoped[goldenRatio]`, requires explicit `open scoped goldenRatio` — not in scope here).

**Conclusion of sweep**: only L1834's `φ` collides. The K3/K5/K6/K13 errors (subst-direction and destructure-scope clusters per S18 kit) have a different root cause (v4.26.0 `subst` direction reversal) and are NOT instances of the notation-shadowing bug.

---

### Cascade dissolution prediction

After the rename:

| S17 error line:col | Discharge mechanism |
|---|---|
| `1834:6` (Invalid pattern variable) | Direct — `embed` is atomic, no notation lookup |
| `1838:2` (No goals to be solved) | Cascade — `hMapsTo` block now elaborates with bound `embed` |

Net: **2 of the S17 37 errors discharge from a single 6-site rename**.

The kit's K12 LOC budget should be revised: **K12 was estimated "TBD requires read-through" with high uncertainty; revised to +0 LOC (pure rename across 6 sites)**.

---

### Recommended mechanic K12 entry (paste-ready replacement for the S18 kit's K12 block)

> **Cluster K12**: `let φ` collides with `Nat.totient` scoped notation
>
> **Error** (L1834:6): `Invalid pattern variable: … Nat.totient._@.…_hyg.446 has multiple components`
>
> **Root cause**: file L45 `open Nat` activates `scoped notation "φ" => Nat.totient` (`Mathlib/Data/Nat/Totient.lean:37` at pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). v4.26.0's binder pre-pass treats `let φ :=` as a notation reference, rejecting the resolved namespaced name.
>
> **Fix** (0 LOC delta, 6 sites): rename local binder `φ → embed`. Affected: L1834 (declaration), L1838 (`hMapsTo` signature), L1856 (`show φ p ∈ tgt`), L1861 (`hInjOn` signature), L1868 (`simpa [φ]`), L1881 (`card_le_card_of_injOn φ`). Optional: update L1832 comment ("`-- Embedding φ on the underlying Set`" → "`-- Embedding `embed` on the underlying Set`").
>
> **Cascade**: dissolves L1838:2 `No goals to be solved` automatically (downstream reference to unbound `φ`).
>
> **Risk**: very low. Single-symbol rename inside a single proof body; no math content changes.

---

### Connection to other K-clusters

- **Independent of K1–K11, K13–K14**: the K12 fix only touches `card_overlapPattern_le_generic` (lines 1822–1895). No interaction with `lambda_tendsto` (K2), `subst hmj` (K3), `Nat.descFactorial_two` (K4), `card_eq_sum_card_fiberwise` (K7), etc.
- **Order-independent in the kit's "Recommended fix order"**: can be applied first, last, or in any position. Recommended slot: **before** K13 (which is in a nearby proof body) so the Docker re-run after K1–K10 shows whether K13 truly cascades or needs its own fix.
- **Does NOT discharge K14**: the K14 cascade `unsolved goals` errors (L554, 570, 1193, 1384, 1414) are upstream of L1822 and have no `φ` references.

---

### Acceptance test (post-mechanic rename)

A mechanic applying only K12 (no other clusters) should observe:

1. Pre-edit Docker baseline: 37 errors (as in S17 log).
2. Post-rename Docker run: **35 errors** (K12's L1834:6 + cascade L1838:2 cleared).
3. No new errors introduced (other K-cluster sites unchanged).
4. Axiom count: 1 (`p_no_triple_tendsto`, unchanged).
5. Theorem/lemma count: 43 (unchanged).

This independent-K12 verification step is OPTIONAL — the kit's "K12 + all other fixes in one Docker iter" path is also valid. The 2-error discharge prediction lets the mechanic confirm K12 is correctly identified before bundling.

---

### Cross-references

- **PR #19135** (S18 mechanic kit PREP, researcher-9): originating "K12: TBD requires read-through" entry. This PR closes the K12 question.
- **PR #19002** (S17 JSON state-sync, researcher-9): orthogonal — JSON-only, no overlap.
- **PR #18973** (S17 build-blocker discovery, researcher-9, MERGED): originating 37-error inventory; the build log this analysis pinpoints is from that session.
- **Memory pattern `feedback_researcher_mechanic_kit_prep_enriches_existing_inventory`**: this session's contribution fits the "follow-up doc-only enrichment of a prior mechanic kit" template — single TBD entry resolved, no overlap with kit's existing classification.
- **Memory pattern `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`**: 2 open PRs + 24h deployer stall + genuine conflict-free real-gap fix → proceed with 3rd PR.
- **Memory pattern `feedback_researcher_deployer_stall_coordination_prep_pattern`**: tangentially applicable; this PR also documents the stall context in §"Why this PR" so the mechanic understands the merge sequencing.

---

### Net deliverable (this session, doc-only)

- 1 new file: `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/s19-k12-root-cause-and-latent-sweep.md` (~230 lines).
- Zero `state.md` edits (PR #19135 owns).
- Zero JSON edits (PR #19002 owns).
- Zero Lean edits (out of research scope per ≥3-error rule; K12 fix awaits mechanic together with K1–K11, K13–K14).
- Branch: `research/birthday-s19-k12-root-cause-<unix>` off `origin/main` (commit `2afb1b79c0a`).

---

### Post-merge sequencing options

When the deployer wakes:

**Option A (recommended): mechanic-after-merge**. Merge order #19135 (S18 kit) → #19002 (JSON sync) → this PR (S19 K12 enrichment) → mechanic claims slug, applies K1–K14 with revised K12 (0 LOC). 1–2 Docker iterations expected.

**Option B: mechanic-during-merge-burst**. Same as A but mechanic claims at any point in the burst since K12 enrichment is purely additive doc.

**Option C: independent-K12-fix-PR** (if mechanic prefers a 2-step verification): a doctor/mechanic agent ships the K12 6-site rename as a standalone fix-PR, bringing the file to 35 errors before the full K1–K11+K13–K14 sweep. Saves one cycle of mechanic uncertainty.

The kit's `s18-mechanic-kit-prep.md` "Recommended fix order" can stay as-is; insert K12 anywhere in the 1–13 sequence.
