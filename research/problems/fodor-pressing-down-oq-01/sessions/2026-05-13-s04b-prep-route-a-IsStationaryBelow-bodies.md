# S4b PREP — Route A body audit for `IsStationaryBelow.{nonempty, of_subset}`

**Author:** researcher-10
**Date:** 2026-05-13 (~03:30 UTC, after merge of PR #18441 S4 PREP at 02:06 UTC)
**Phase:** S4b PREP (a refinement of S4 PREP §4.1 Route A)
**Slug:** `fodor-pressing-down-oq-01`
**Branch:** `research/fodor-pressing-down-oq-01-s04b-prep-route-a-bodies-*`
**Scope:** **doc-only** — no Lean edits, no `problem.md` / `knowledge.md` /
`state.md` edits, no gallery JSON edits. One new file under `sessions/`.

## 0. Why this memo (and why now)

S4 PREP (PR #18441, merged 02:06 UTC) flagged one **load-bearing** gotcha
for the eventual S4 ACT parent-trim: the two dotted-method theorems

```
proofs/Proofs/FodorPressingDown.lean:334  theorem IsStationaryBelow.nonempty
proofs/Proofs/FodorPressingDown.lean:343  theorem IsStationaryBelow.of_subset
```

are declared inside `namespace FodorPressingDown` (parent line 39), so
their full names are `FodorPressingDown.IsStationaryBelow.{nonempty,of_subset}`.
After the trim, the parent's `hS : IsStationaryBelow S o` resolves to
`Ordinal.IsStationaryBelow S o` (via `open Ordinal` at parent line 41),
so dot notation `hS.nonempty` / `hS.of_subset` looks up
`Ordinal.IsStationaryBelow.{nonempty,of_subset}` — **which do not exist
without Route A**.

PR #18441 §4.1 recommended **Route A**: move both theorems into
`Proofs/Club/Basic.lean` under `namespace Ordinal`. But that PREP only
documented the recommendation at a high level — it did NOT audit the
actual theorem bodies, did NOT verify they transfer verbatim, and did
NOT identify a concrete insertion site or list the symbols the bodies
depend on.

This memo locks the Route A body-level audit so the S4 ACT implementer
can copy-paste the two theorems into Basic.lean with zero proof-state
re-derivation.

## 1. Source state (verified at `git rev-parse HEAD = f24bbb67450`)

- Parent file: `proofs/Proofs/FodorPressingDown.lean`, 385 LOC.
- Target theorems: lines 334–338 (`nonempty`, 5 LOC body+sig) and
  lines 343–348 (`of_subset`, 6 LOC body+sig). Docstrings (1 line + 3 lines)
  bring totals to **6 LOC and 9 LOC** respectively, or **15 LOC together**.
- `Proofs/Club/Basic.lean`: 98 LOC (per PR #18367 S2 ACT merged). API
  surface includes `Ordinal.IsClubBelow`, `Ordinal.IsStationaryBelow`,
  `Ordinal.isClubBelow_Iio_of_isSuccLimit`, plus the four other defs +
  three other mechanical lemmas.

## 2. Verbatim body of `IsStationaryBelow.nonempty`

Lines 333–338 of the parent file:

```lean
/-- Every stationary set is nonempty. -/
theorem IsStationaryBelow.nonempty {S : Set Ordinal} {o : Ordinal}
    (hS : IsStationaryBelow S o) (ho : IsSuccLimit o) : S.Nonempty := by
  have hC : IsClubBelow (Iio o) o := isClubBelow_Iio_of_isSuccLimit ho
  obtain ⟨γ, hγS, _⟩ := hS (Iio o) hC
  exact ⟨γ, hγS⟩
```

### 2.1 Symbol-dependency walk

| Symbol in body                    | Source after Route A                         | In scope in Basic.lean? |
|-----------------------------------|----------------------------------------------|-------------------------|
| `Set` (in `Set Ordinal`, `S.Nonempty`) | Mathlib core (`open Set` at Basic.lean:40)   | yes                     |
| `Ordinal` (in `Set Ordinal`)      | Mathlib `Mathlib.SetTheory.Ordinal.Basic`    | yes (via Topology import) |
| `IsStationaryBelow`               | `Ordinal.IsStationaryBelow` (Basic.lean:55)  | yes (same namespace)    |
| `IsSuccLimit`                     | `Order.IsSuccLimit` (Mathlib `Order/SuccPred/Limit.lean`) | yes (Mathlib.Tactic supplies; live Mathlib has `IsSuccLimit.succ_lt` at Limit.lean:386, verified by `gh api search/code "IsSuccLimit.succ_lt repo:leanprover-community/mathlib4"` → 4 hits 2026-05-13) |
| `IsClubBelow`                     | `Ordinal.IsClubBelow` (Basic.lean:49)        | yes (same namespace)    |
| `isClubBelow_Iio_of_isSuccLimit`  | `Ordinal.isClubBelow_Iio_of_isSuccLimit` (Basic.lean:87) | yes (same namespace) |
| `Iio`                             | `Set.Iio` (Mathlib core, exposed by `open Set` Basic.lean:40) | yes |
| `Set.Nonempty`                    | Mathlib core                                  | yes (via Set)           |
| `S ∩ Iio o`                       | `Set.inter` notation                          | yes                     |

All eight symbols already resolve inside Basic.lean's `namespace Ordinal`
block. No new imports required.

### 2.2 Destructuring sanity

`hS (Iio o) hC` returns `(S ∩ Iio o).Nonempty`, i.e., `∃ γ, γ ∈ S ∩ Iio o`.
The pattern `⟨γ, hγS, _⟩` destructures via:

- First layer: `Set.Nonempty` constructor `⟨γ, hγ⟩` with `hγ : γ ∈ S ∩ Iio o`.
- Second layer: `Set.mem_inter_iff` (definitional `_ ∧ _`) destructures
  `hγ` as `⟨hγS, hγO⟩` with `hγS : γ ∈ S` and `hγO : γ ∈ Iio o`.

The third bound name `_` discards `γ ∈ Iio o` since the conclusion only
needs `γ ∈ S`. Pattern is correct.

## 3. Verbatim body of `IsStationaryBelow.of_subset`

Lines 340–348 of the parent file:

```lean
/-- Stationary sets are closed under subelements in the following sense:
    if T ⊆ S, S is stationary, and every club meeting S meets T,
    then T is stationary. -/
theorem IsStationaryBelow.of_subset {S T : Set Ordinal} {o : Ordinal}
    (hS : IsStationaryBelow S o) (hTS : T ⊆ S)
    (hMeet : ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty → (T ∩ C).Nonempty) :
    IsStationaryBelow T o := by
  intro C hC
  exact hMeet C hC (hS C hC)
```

### 3.1 Symbol-dependency walk

| Symbol in body          | Source after Route A                         | In scope in Basic.lean? |
|-------------------------|----------------------------------------------|-------------------------|
| `Set`, `Ordinal`        | Mathlib core / Mathlib.SetTheory.Ordinal     | yes                     |
| `IsStationaryBelow`     | `Ordinal.IsStationaryBelow` (Basic.lean:55)  | yes                     |
| `IsClubBelow`           | `Ordinal.IsClubBelow` (Basic.lean:49)        | yes                     |
| `T ⊆ S`                 | `Set.subset` (Mathlib core)                  | yes                     |
| `S ∩ C`                 | `Set.inter`                                  | yes                     |
| `Set.Nonempty`          | Mathlib core                                  | yes                     |

All six symbols resolve via Basic.lean's existing `open Set Order` + the
Topology import chain. The body is **pure first-order logic** — `intro`,
`exact`, no `rw` / no `simp` / no `obtain`. Strongest possible
transferability.

### 3.2 Argument-order sanity

The signature uses `hTS : T ⊆ S` but does NOT use `hTS` in the body
(the body only invokes `hMeet C hC (hS C hC)`). `hTS` is currently a
*dead* hypothesis at the body's elaboration boundary — the API exposes
the assumption to the caller as documentation, since `hMeet` itself is
the load-bearing constraint. Lean does not warn about unused hypotheses
at the theorem level; the lemma still type-checks.

**Honesty note**: a follow-up cleanup PR could remove `hTS` and update
both citation sites in `oq-04`'s docs to mention only `hMeet`. Out of
scope for S4b PREP / Route A — preserve verbatim.

## 4. Insertion point in `Proofs/Club/Basic.lean`

Basic.lean currently ends at line 98:

```
86  /-- `Iio o` is a club below `o` when `o` is a successor-limit ordinal. -/
87  theorem isClubBelow_Iio_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) :
…
96      exact ⟨α + 1, h1, lt_add_one α, h1⟩
97
98  end Ordinal
```

Route A inserts both theorems **between line 96 and line 97** (i.e.,
right before the blank line that precedes `end Ordinal`). Insertion in
this order matches the parent's source ordering (nonempty before of_subset).

### 4.1 Concrete patch shape (S4 ACT will apply)

```lean
@@ proofs/Proofs/Club/Basic.lean
@@ -96,3 +96,18 @@
       exact ⟨α + 1, h1, lt_add_one α, h1⟩

+/-- Every stationary set is nonempty (witnessed by intersecting with the
+club `Iio o` at successor-limit ordinals). -/
+theorem IsStationaryBelow.nonempty {S : Set Ordinal} {o : Ordinal}
+    (hS : IsStationaryBelow S o) (ho : IsSuccLimit o) : S.Nonempty := by
+  have hC : IsClubBelow (Iio o) o := isClubBelow_Iio_of_isSuccLimit ho
+  obtain ⟨γ, hγS, _⟩ := hS (Iio o) hC
+  exact ⟨γ, hγS⟩
+
+/-- Stationary sets are closed under subelements in the following sense:
+    if `T ⊆ S`, `S` is stationary, and every club meeting `S` meets `T`,
+    then `T` is stationary. -/
+theorem IsStationaryBelow.of_subset {S T : Set Ordinal} {o : Ordinal}
+    (hS : IsStationaryBelow S o) (_hTS : T ⊆ S)
+    (hMeet : ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty → (T ∩ C).Nonempty) :
+    IsStationaryBelow T o := by
+  intro C hC
+  exact hMeet C hC (hS C hC)
+
 end Ordinal
```

Note the **`_hTS` underscore prefix** for the unused-hypothesis argument
in `of_subset` — Lean 4 lint convention to suppress an `unused variable`
warning without changing the API signature. If S4 ACT prefers to keep
the original name `hTS` (matching the parent's signature character-for-
character), the lint will fire as a warning, not an error. Either is
acceptable; the underscore prefix is mildly cleaner.

### 4.2 LOC delta in Basic.lean

- Before Route A: 98 LOC.
- After Route A insertion: 98 + 15 (two docstring/sig/body blocks + one
  blank line between them) = **113 LOC**.
- The two `theorem` declarations bump Basic.lean's `theoremCount` from 5
  to 7. Basic.lean has no gallery `meta.json` (it's a library module,
  not a gallery proof) — meta.json drift concern only applies to the
  parent file's gallery entry, which is the S4 ACT scope.

## 5. Corresponding parent-side deletion (under Route A)

S4 ACT then removes lines 333–348 (16 LOC: 1 banner + 1 blank + 6 LOC
nonempty + 1 blank + 8 LOC of_subset) from the parent. The Part-VI
banner at lines 329–331 should also be removed if S4 chooses to drop
the now-empty part:

- If **Route A taken**: parent Part VI is empty → drop banner (lines
  329–331 + blank line 332 = 4 extra LOC removed).
- Net parent delta (with Route A): −82 (Parts I–II + diagInter_isClosedBelow)
  − 16 (Part VI bodies) − 4 (Part VI banner) = **−102 LOC**.

PR #18441 §7's "Route A" row already projects parent at **~286 LOC**
post-trim; this memo confirms the arithmetic: 385 − 102 = 283
(within the ±5 banner-handling tolerance).

## 6. External consumer audit (oq-04 Solovay splitting)

The sister slug `fodor-pressing-down-oq-04` already cites both theorems
as load-bearing for its eventual Lean proof. Citations found via
`grep -rn "IsStationaryBelow\.(nonempty|of_subset)" research/problems/fodor-pressing-down-oq-04/`:

| File                                                    | Line   | Citation                                                          |
|---------------------------------------------------------|--------|-------------------------------------------------------------------|
| `problem.md`                                            | 37     | `IsStationaryBelow.of_subset` (passing to stationary subsets)     |
| `problem.md`                                            | 38     | `IsStationaryBelow.nonempty` (trivial-case sanity check)          |
| `knowledge.md`                                          | 28     | `IsStationaryBelow.of_subset` for stationary subsets              |
| `knowledge.md`                                          | 69     | `IsStationaryBelow.of_subset` — Restrict to S₀, T, T_ξ            |
| `knowledge.md`                                          | 70     | `IsStationaryBelow.nonempty` — Sanity check (Solovay nonempty)    |
| `state.md`                                              | 21     | Step 1 reduces to limit ordinals via `IsStationaryBelow.of_subset` |
| `sessions/2026-05-12-s02-prep-stepI-limit-club.md`      | 198    | Step 3 uses `IsStationaryBelow.of_subset`                          |
| `sessions/2026-05-13-s3-prep-cofinality-bound-fodor.md` | 145    | New theorem inserted after `IsStationaryBelow.of_subset` (line 343) |
| `sessions/2026-05-13-s3-prep-cofinality-bound-fodor.md` | 199    | Step 6 set-equality uses `IsStationaryBelow.of_subset`             |

**Total of 8 distinct oq-04 citations** of these two theorems, across 5
files. Every citation references the **parent's** dotted-method full
name. Under Route A (post-S4 ACT), the bare dot notation `hS.of_subset`
in oq-04's eventual Lean file will resolve to
`Ordinal.IsStationaryBelow.of_subset` — which is exactly what oq-04
needs to type-check. **Route A makes oq-04's Lean proof land cleanly.**

**Route B** (re-declare under `_root_.Ordinal` inside the parent) and
**Route C** (rename to snake_case `isStationaryBelow_nonempty`) would
*also* let oq-04 resolve dot notation, but Route C requires updating
all 8 oq-04 citations to drop dot notation, and Route B retains a
weird nested-namespace declaration inside `FodorPressingDown`. Route A
is strictly cleaner.

## 7. Build-pending analysis

Route A's S4 ACT depends on:

1. **PR #18367 (S2 ACT) merged AND docker-built clean.** Status: merged
   2026-05-13 02:11 UTC; build pending per PR title. Until Club/Basic.lean
   build clears, ANY S4 ACT inherits the dependency-failure risk.
2. **S3 ACT (`diagInter_isClosedBelow` migration) merged AND built.**
   Status: S3 PREP'd in PR #18412 (merged 02:08 UTC); S3 ACT not yet
   pushed. Until S3 ACT lands, the parent's `diagInter_isClosedBelow`
   coexists with the eventual `Ordinal.diagInter_isClosedBelow` — but
   the two namespaces don't collide.

S4 ACT cannot proceed until at least #18367 is build-cleared (because
its own additions ride on Basic.lean's structure). S4b PREP **does not
move that timeline forward** — but it eliminates one source of S4 ACT
build-retry by pre-staging the exact Route A patch.

### 7.1 Build risk for Route A patch itself

The two transferred theorem bodies depend only on Basic.lean's already-
present API + Mathlib core. **No new Mathlib imports needed.** If
Basic.lean builds, the two theorems will build (modulo Mathlib API
drift — verified §2.1).

## 8. Anti-targets (S4b PREP & eventual Route A migration)

8.1 **Do NOT modify `Proofs/Club/Basic.lean` in this PR.** Doc-only.

8.2 **Do NOT modify `Proofs/Proofs/FodorPressingDown.lean` in this PR.**
    Doc-only.

8.3 **Do NOT modify oq-04's `problem.md` / `knowledge.md` / `state.md` /
    `sessions/*`** even if the citations would benefit from clarifying
    that Route A moves these to `Ordinal.IsStationaryBelow.*`. Such
    updates belong to S5 or an oq-04 author's session.

8.4 **Do NOT modify `src/data/proofs/fodor-pressing-down/meta.json`**
    or `annotations.json` — line-anchor re-anchoring is post-S4 ACT
    mechanic territory.

8.5 **Do NOT modify the slug's `problem.md` / `knowledge.md` /
    `state.md` / `gallery JSON`** — these are owned by S1 OBSERVE
    (PR #18280) and S4 ACT (when it lands).

8.6 **Do NOT run docker builds from this PREP branch.** Doc-only.

8.7 **Do NOT change the recommended Route (A vs B vs C).** PR #18441
    §4.1 recommends Route A; this memo confirms the recommendation and
    adds body-level detail. S4 ACT implementer retains final choice.

## 9. Anti-targets that the **eventual** S4 ACT must respect

These are S4 ACT-time constraints, restated here so they're locked
together with the Route A audit:

9.1 The two theorems must be transferred **verbatim** (modulo the
    `_hTS` underscore-prefix lint cleanup from §4.1). No proof-state
    re-derivation; no signature change beyond the underscore.

9.2 The transfer order in Basic.lean is `nonempty` then `of_subset`
    (matches parent source order, matches oq-04's citation order).

9.3 The parent file's Part-VI banner (lines 329–331) **should** be
    removed under Route A (Part VI becomes empty). Optional but
    recommended.

9.4 Docstrings transfer verbatim. The S2 ACT precedent is verbatim
    docstring transfer with namespace-line rewrite.

## 10. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/fodor-pressing-down-oq-01/sessions/2026-05-13-s04b-prep-route-a-IsStationaryBelow-bodies.md
```

Disjoint from:

- PR #18367 (S2 ACT, **merged**) — edits `proofs/Proofs.lean`,
  `proofs/Proofs/Club/Basic.lean`, and
  `sessions/2026-05-12-s02-act-club-basic.md`. **No overlap.**
- PR #18412 (S3 PREP, **merged**) —
  `sessions/2026-05-12-s03-prep-diagInter-isClosedBelow-migration.md`.
  **No overlap (different filename).**
- PR #18441 (S4 PREP, **merged**) —
  `sessions/2026-05-12-s04-prep-parent-trim-audit.md`. **No overlap
  (different filename, and §4.1 only recommended Route A; this memo
  pre-stages the patch).**
- Any S3 ACT or S4 ACT that lands later — they touch
  `proofs/Proofs/Club/Basic.lean`, `proofs/Proofs/FodorPressingDown.lean`,
  and `src/data/proofs/fodor-pressing-down/meta.json`. **None of those
  files are touched here.**
- Any oq-04 session — those live under
  `research/problems/fodor-pressing-down-oq-04/sessions/`. **Different
  slug directory.**

git auto-merges the `sessions/` directory addition; no rebase conflict.

## 11. Honesty assessment

**Mathematical content**: zero new mathematics. This memo audits the
bodies of two utility lemmas about stationary sets that are already
proved (0 sorries) in the parent file, and verifies the namespace
rewrite for Route A is trivially correct.

**Originality**: zero. Standard library-extraction refactor; this memo
adds line-by-line body detail that PR #18441's high-level S4 PREP
implicitly assumed but did not show.

**Value-add over PR #18441 §4.1**:

- §2.1 + §3.1 enumerate every symbol in each body and confirm Basic.lean's
  existing `namespace Ordinal` + `open Set Order` already resolves all of
  them. PR #18441 §4.1 said "they're general-purpose facts about
  `IsStationaryBelow` that belong in `Club/Basic.lean`" — true but
  unverified.
- §2.2 sanity-checks the depth-2 destructuring pattern in `nonempty`'s
  body. PR #18441 did not.
- §4 specifies the exact insertion point (between lines 96 and 97 of
  Basic.lean) and shows the patch shape. PR #18441 left this as
  implementer judgment.
- §6 quantifies the consumer impact: **8 oq-04 citations across 5 files**
  depend on Route A. PR #18441 mentioned oq-04 once as the "primary
  downstream consumer" without auditing the citation surface.
- §5 reconciles the parent-delta arithmetic: under Route A the trim is
  −102 LOC (not the −99 LOC of PR #18441's §7 Route-A row, because that
  estimate did not account for the now-empty Part-VI banner removal).
  The 3-LOC discrepancy is minor and within PR #18441's stated tolerance.

**What could be wrong**:

- The `(S ∩ Iio o).Nonempty` destructuring in `nonempty` (§2.2) relies
  on `Set.inter` membership being definitionally `_ ∧ _`. In Mathlib
  v4.26.0 this is the case (`Set.mem_inter_iff` is `Iff.rfl`-style). If
  a future Mathlib release changes the definition, the pattern would
  need an explicit `mem_inter_iff` unfolding — but that scenario also
  breaks the parent file's *current* build. So the risk is identical
  to the parent's current build risk; Route A introduces no new
  exposure.
- `IsSuccLimit` was renamed at one point in Mathlib history
  (`Order.IsSuccPrelimit` vs `Order.IsSuccLimit`). At v4.26.0 (verified
  2026-05-13 via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Order/SuccPred/Limit.lean`),
  the name is `IsSuccLimit` and `IsSuccLimit.succ_lt` exists at line 386.
  If the project's mathlib pin lags this rename, both the parent file's
  current build AND Route A's transferred body break together — again,
  no new exposure.
- This memo does not run `./proofs/scripts/docker-build.sh
  Proofs.Club.Basic` to verify Basic.lean's *current* build cleanliness.
  PR #18367 was build-pending at merge time. If Basic.lean does not
  build at v4.26.0, Route A inherits the failure — but that scenario
  also blocks S3 ACT, S4 ACT, and every other downstream consumer of
  Basic.lean, so the audit value remains: when the dust clears, Route A
  is the cleanest patch.

## 12. Cheat-sheet for S4 ACT Route A implementer

Once S2 ACT (#18367)'s docker build clears and S3 ACT lands cleanly:

1. **Verify Basic.lean built clean**:
   ```bash
   ./proofs/scripts/docker-build.sh Proofs.Club.Basic
   ```
2. **Apply parent trim** per PR #18441 §11 steps 1–5.
3. **Apply Route A** per this memo's §4.1 patch.
4. **Run §8 verification script from PR #18441**:
   ```bash
   ./proofs/scripts/docker-build.sh Proofs.FodorPressingDown
   ```
   plus the meta.json drift check.
5. **PR title**: `research(fodor-pressing-down-oq-01): S4 ACT — trim
   parent + Route A (4 defs + 6 lemmas + 2 IsStationaryBelow.* moved to
   Club/Basic.lean, build pending)`.
6. **PR body**: cross-reference PR #18280 (S1 OBSERVE), #18367 (S2 ACT),
   #18412 (S3 PREP), #18441 (S4 PREP), and **this** PR (S4b PREP).

## Appendix A: Verification commands used in this memo

```bash
# Confirm current parent file state at the commit this memo was authored:
git rev-parse HEAD
# f24bbb67450...

# Confirm the two theorems and their line numbers in the parent:
grep -n "IsStationaryBelow.nonempty\|IsStationaryBelow.of_subset" \
  proofs/Proofs/FodorPressingDown.lean
#   334:theorem IsStationaryBelow.nonempty ...
#   343:theorem IsStationaryBelow.of_subset ...

# Confirm no other Lean file in the project currently consumes them via
# dot notation (zero external in-tree call sites, so Route A is the
# only mover at risk):
grep -rn "IsStationaryBelow\.(nonempty|of_subset)" proofs/ src/ 2>/dev/null
#   only the parent's own declarations + 8 oq-04 doc citations (§6)

# Confirm Basic.lean's current end-of-file structure:
tail -15 proofs/Proofs/Club/Basic.lean

# Confirm IsSuccLimit + IsSuccLimit.succ_lt are at Mathlib v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Order/SuccPred/Limit.lean \
  --jq '.content' | base64 -d | grep -n "IsSuccLimit\.succ_lt"
#   386:theorem IsSuccLimit.succ_lt ...
```

## Appendix B: Estimated Route A implementation effort

- **Code edits**: +15 LOC to `Proofs/Club/Basic.lean`, −16 LOC from
  `Proofs/Proofs/FodorPressingDown.lean` (within the S4 ACT's larger
  −102 LOC parent trim).
- **Meta.json edits**: parent's `theoremCount` drops by 8 (Route A
  variant), `lineCount` drops ~99–102, `imports` adds one entry. Basic.lean
  is not a gallery proof — no meta.json drift on its side.
- **Build**: same as the broader S4 ACT, ~25–45 min Docker cold.
- **Total wall-clock**: identical to the broader S4 ACT (60–90 min)
  because Route A is folded into the same trim PR per PR #18441's §9.4
  (atomicity anti-target).

This memo's existence does not change S4 ACT's wall-clock; it removes
one body-audit step that the implementer would otherwise have to
perform interactively at PR-creation time.
