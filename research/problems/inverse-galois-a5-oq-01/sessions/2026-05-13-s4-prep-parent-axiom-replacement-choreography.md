# S4 PREP — Parent-axiom replacement choreography: from `axiomatized` to `verified`

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to all S3 ORIENT sub-step memos (a/b/c) and
the S2 scaffold. Addresses an issue the existing S3 sub-step (c) memo
glosses over: **the circular-import problem** that blocks the
straightforward "replace `axiom` with `theorem`" upgrade path.

## Why this PREP

The S2 ORIENT companion file (`InverseGaloisA5Dedekind.lean:83-88`)
contains this comment:

> **Bridge theorem**: an order-3 element of `q.Gal` yields `3 ∣ |q.Gal|`
> via `orderOf_dvd_card`. This is the eliminator for
> `InverseGaloisA5.three_dvd_gal_card`; **in S4 the parent's `axiom`
> will be rewritten as `theorem three_dvd_gal_card := three_dvd_gal_card_proved`.**

This S4 plan is **incorrect as stated**: it creates a circular import. The
companion file already `import Proofs.InverseGaloisA5` (line 2). If the
parent's `axiom` is rewritten to `theorem three_dvd_gal_card :=
InverseGaloisA5Dedekind.three_dvd_gal_card_proved`, then the parent would
need `import Proofs.InverseGaloisA5Dedekind`, completing the cycle.

This PREP designs the **correct** import-graph choreography for S5 (after
S4 ACT discharges the `exists_gal_order_three` sorry), evaluating three
alternatives and recommending one.

## Context recap

**Parent**: `proofs/Proofs/InverseGaloisA5.lean` (2067 LOC, 84 thms,
12 defs, 1 axiom).

**The axiom** (`InverseGaloisA5.lean:309`):

```lean
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal
```

**Downstream uses** (the axiom referenced 5+ times in the parent file):

| Site | Role |
|---|---|
| `q_gal_card` (line ~1907) | combined with `five_dvd_gal_card` via
  `Nat.Coprime.mul_dvd_of_dvd_of_dvd` to derive `15 ∣ |Gal|`, then chained
  with `gal_card_dvd_60_proved`, `gal_card_ne_15`, `gal_card_ne_30` to
  force `|Gal| = 60`. |
| `q_gal_iso_a5` (downstream of `q_gal_card`) | concludes Gal ≅ A₅. |
| `a5_realizable_iso` (main theorem) | downstream of `q_gal_iso_a5`. |
| `gal_not_solvable` (Part XVII) | uses the isomorphism. |

So `three_dvd_gal_card` is **load-bearing for the main theorem**. Replacing
it must preserve the *type* (3 ∣ Fintype.card q.Gal) and the
*namespace location* (`InverseGaloisA5.three_dvd_gal_card`) to avoid
cascading edits across the file.

**The companion**: `proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 LOC,
1 sorry, 2 theorems after S3 ACT).

```lean
-- After S3 ACT (substep a + b + c integrated):
namespace InverseGaloisA5Dedekind

open InverseGaloisA5

theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3 := by ...

theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal := by
  obtain ⟨σ, hσ⟩ := exists_gal_order_three
  rw [← hσ]
  exact orderOf_dvd_card

end InverseGaloisA5Dedekind
```

**Gallery status target**: `axiomatized` → `verified`
(`src/data/proofs/inverse-galois-a5/meta.json`).

## The circular-import problem

```
InverseGaloisA5.lean
  ├─ axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal
  └─ (defines q, q.Gal, q.SplittingField, etc.)
                ↑
                │ import
                │
InverseGaloisA5Dedekind.lean
  ├─ import Proofs.InverseGaloisA5
  ├─ theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3
  └─ theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal
```

The current dependency direction is **Dedekind → Parent** (companion
depends on parent). If we make the parent's `theorem three_dvd_gal_card`
reference the companion's lemma, the parent depends on the companion,
producing the cycle `Parent → Dedekind → Parent`.

Lean 4 does not allow cyclic module imports.

## Three replacement strategies

### Strategy A: Inline the Dedekind proof into the parent

**Plan**: Copy the full Dedekind machinery (the ~76 LOC of the companion
+ the S4 ACT additions, ~200 LOC total) into `InverseGaloisA5.lean` at
the point of the current axiom (around line 309).

**Pros**:
- No new files. Smallest possible "diff topology".
- No namespace changes. All theorems remain accessible at
  `InverseGaloisA5.*`.
- meta.json change is purely cosmetic
  (`axiomCount: 1 → 0`, `status: axiomatized → verified`).

**Cons**:
- **Parent file grows from 2067 to ~2300 LOC**. Already large.
- The Dedekind proof depends on `Mathlib.RingTheory.Frobenius` and
  `Mathlib.NumberTheory.RamificationInertia.Galois`, which the
  current parent does not import. Adds two Mathlib imports.
- Loses the **pedagogical separation**: "the q-specific Galois theory"
  vs. "the Dedekind-theorem instantiation" become indistinguishable.
- Discards the companion file's existing structure entirely (the
  76 LOC + the new ACT content goes away as a separate module).

### Strategy B: Split-parent (recommended)

**Plan**: Refactor the parent into two files preserving the same namespace:

1. **`InverseGaloisA5/Base.lean`** (or `InverseGaloisA5Base.lean`): the
   parent's content **minus** the `axiom three_dvd_gal_card` declaration
   AND **minus** all downstream uses (lines 309 + `q_gal_card` and
   everything past it). About 1800 LOC.

2. **`InverseGaloisA5Dedekind.lean`** (existing): unchanged structure;
   imports `Base`. Discharges `exists_gal_order_three` (S4 ACT) and
   `three_dvd_gal_card_proved`.

3. **`InverseGaloisA5.lean`** (re-purposed as a "main" file): imports
   both `Base` and `Dedekind`. Declares
   `theorem three_dvd_gal_card : 3 ∣ Fintype.card q.Gal :=
   InverseGaloisA5Dedekind.three_dvd_gal_card_proved`. Then provides the
   downstream theorems (`q_gal_card`, `q_gal_iso_a5`, `a5_realizable_iso`,
   `gal_not_solvable`) that were previously below the axiom. About
   250 LOC.

**Resulting dependency graph**:

```
InverseGaloisA5Base.lean
  ├─ (1800 LOC: q definition, irreducibility, Vandermonde, etc.)
  └─ NO `three_dvd_gal_card` (deferred to InverseGaloisA5.lean)
                ↑
                │ import
                │
InverseGaloisA5Dedekind.lean
  ├─ import Proofs.InverseGaloisA5Base
  ├─ theorem exists_gal_order_three ...
  └─ theorem three_dvd_gal_card_proved ...
                ↑
                │ import
                │
InverseGaloisA5.lean (main, re-purposed)
  ├─ import Proofs.InverseGaloisA5Base
  ├─ import Proofs.InverseGaloisA5Dedekind
  ├─ theorem three_dvd_gal_card : ... := three_dvd_gal_card_proved
  ├─ theorem q_gal_card ...
  ├─ theorem q_gal_iso_a5 ...
  └─ theorem a5_realizable_iso ... (and gal_not_solvable, etc.)
```

**Pros**:
- **No circular import**.
- Preserves the `InverseGaloisA5.*` namespace fully (since both Base
  and main use `namespace InverseGaloisA5`).
- Companion's existing 76-LOC structure is unchanged (only its
  `import` swaps from `InverseGaloisA5` to `InverseGaloisA5Base`).
- The parent's "1 axiom" → "0 axioms" transition is the cleanest
  possible: one removed `axiom`, one added `theorem` line in `main.lean`.
- Re-using the same module name `InverseGaloisA5.lean` means external
  files (sibling gallery proofs, umbrella `proofs/Proofs.lean`) need
  **zero edits**: they keep importing `Proofs.InverseGaloisA5`.

**Cons**:
- Three-file split is a moderate refactor. ~30 LOC of `import`
  shuffling.
- Requires choosing a precise "split point" in the parent. The
  natural choice is **immediately after `gal_card_dvd_60_proved`**
  (around line 1900 of the current parent) — everything above is
  in Base, everything below is in main.
- The `proofs/Proofs.lean` umbrella may need a new entry for
  `Proofs.InverseGaloisA5Base` (alphabetically before `Bezout` or
  similar). This is a one-line addition.
- Test plan: must verify both `Base` and `main` build under Docker.

### Strategy C: Forward-declared proxy lemma

**Plan**: Keep the parent's `theorem three_dvd_gal_card` as a *forward-declared
proxy* discharged opaquely, then bind it from the Dedekind side via
`@[simp]` or `instance`.

**Mechanics**: Lean 4 does not have a clean "forward declaration" idiom
analogous to C's; the closest is to use a `class` typeclass or to
encode the lemma as a hypothesis on a `variable`. Both are awkward
for a single-use axiom replacement.

**Pros**: smallest local change at first glance.

**Cons**:
- Idiomatic Lean 4 strongly discourages this pattern.
- Would require introducing a `Tactic`-level machinery just to bind
  one theorem.
- Verdict: **NOT RECOMMENDED**.

## Recommendation: Strategy B (split-parent)

Strategy B is the only clean path. Strategy A wastes the existing
companion file's modular structure and produces a 2300-line monolith.
Strategy C is anti-idiomatic.

### Why not just inline (A)?

A reasonable counter-argument is "if the companion is going away anyway,
why preserve it?". The answer:

1. The companion is **already merged and tested**. Discarding it
   would re-introduce uncertainty in already-verified material.
2. **Modularity scales**: future axiom-elimination work (e.g., for the
   Hilbert symbol / cyclotomic-style PRs) will follow the same
   companion-file pattern. Strategy B sets a reusable template.
3. **Pedagogical clarity**: the gallery viewer can read the parent
   as "the q-specific construction" and the companion as "the
   number-theoretic black-box for Frobenius-cycle-type". This split
   is itself didactically valuable.

## Concrete S5 plan (after S4 ACT)

Once S4 ACT discharges the `exists_gal_order_three` sorry, S5
(Strategy B) does:

### Step 1: Create `InverseGaloisA5Base.lean`

```bash
# In the worktree:
git mv proofs/Proofs/InverseGaloisA5.lean proofs/Proofs/InverseGaloisA5Base.lean
```

Then **remove** from `Base.lean`:
- Line 309: `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`
- All lines from `q_gal_card` (around 1907) to end of `Part XVII`
  (lines ~1907–2060, approximately 150 LOC).

Note: `Base.lean` retains the `namespace InverseGaloisA5` declaration
and the umbrella `end InverseGaloisA5` at file end.

### Step 2: Update the companion's import

```diff
-import Proofs.InverseGaloisA5
+import Proofs.InverseGaloisA5Base
```

Single-line change in `InverseGaloisA5Dedekind.lean`.

### Step 3: Create the new `InverseGaloisA5.lean` (~250 LOC)

```lean
import Proofs.InverseGaloisA5Base
import Proofs.InverseGaloisA5Dedekind

namespace InverseGaloisA5

open Polynomial

/-- **Theorem (formerly axiom)**: `3 ∣ |Gal(q/ℚ)|`. Proved via the Dedekind-Frobenius
    construction at the unramified prime `p = 7` (see `InverseGaloisA5Dedekind`). -/
theorem three_dvd_gal_card : 3 ∣ Fintype.card q.Gal :=
  InverseGaloisA5Dedekind.three_dvd_gal_card_proved

-- The previously-axiomatized line above is the only axiom-to-theorem
-- transition. All downstream theorems below are unchanged.

theorem q_gal_card : Fintype.card q.Gal = 60 := by
  -- (the existing proof, unchanged: combines three_dvd_gal_card with
  --  five_dvd_gal_card, gal_card_dvd_60_proved, gal_card_ne_15, gal_card_ne_30)
  ...

-- Part XVI: q_gal_iso_a5 (unchanged)
-- Part XVII: gal_not_solvable (unchanged)
-- Main theorem: a5_realizable_iso (unchanged)

end InverseGaloisA5
```

### Step 4: Update `proofs/Proofs.lean` umbrella

```diff
+import Proofs.InverseGaloisA5Base
 import Proofs.InverseGaloisA5
 import Proofs.InverseGaloisA5Dedekind
```

(Alphabetical: Base comes before bare A5 in dictionary order. Verify
existing positions of all three.)

### Step 5: Update `meta.json`

```diff
   "meta": {
-    "status": "axiomatized",
-    "badge": "axiom",
-    "axiomCount": 1,
+    "status": "verified",
+    "badge": "original",
+    "axiomCount": 0,
     "sorries": 0,
-    "assumptions": "1 axiom: `three_dvd_gal_card` (3 ∣ |Gal(q/ℚ)|), ..."
+    "assumptions": "0 axioms. All Galois-group cardinality constraints (5 | |Gal|, |Gal| | 60, 3 | |Gal|) are proved from Mathlib + the Dedekind-Frobenius construction at p = 7 (Polynomial q factors mod 7 as (linear)(linear)(irreducible cubic), giving a 3-cycle in the Galois group via the Frobenius automorphism).",
```

Also:
- `theoremCount: 84 → 85` (the new `three_dvd_gal_card` *theorem*).
- `lineCount: 2067 → 2300 + 76 + 200 ≈ 2576` (sum of Base + Dedekind + new main).
- `originalContributions`: append "Dedekind-Frobenius lemma `exists_gal_order_three` at p=7 (companion file) eliminating the last axiom."

### Step 6: Update `src/data/research/problems/inverse-galois-a5-oq-01.json`

```diff
-  "status": "in-progress",
+  "status": "completed",
   "knowledge": {
     "progressSummary": "VERIFIED: parent inverse-galois-a5 upgraded from `axiomatized` (1 axiom) to `verified` (0 axioms) via the Dedekind-Frobenius bridge. All steps S1–S5 completed."
   }
```

## File-ordering risks and mitigations

### Risk 1: `q.Gal` not in scope in `Base.lean`

**Concern**: if the parent's existing line ordering puts `q.Gal` somewhere
that the split disrupts, the Base file might not have `q.Gal` defined
where it's needed.

**Mitigation**: split AFTER the entire `q.Gal` definition chain (which
happens early in the file). The split point is *AFTER* `gal_card_dvd_60_proved`
(currently around line 1900), which is well past `q.Gal`. Verified by
grep: `q.Gal` first appears around line 165, `gal_card_dvd_60_proved`
around line 1900. Split at any line between 1900 and 1907 works.

### Risk 2: namespace coherence

**Concern**: `InverseGaloisA5.three_dvd_gal_card` must be the same
identifier whether it was declared in `Base.lean` (currently is) or
`main.lean` (after split). Lean's namespace system is content-agnostic:
declarations in `namespace InverseGaloisA5` blocks of two different
files DO collide in the same namespace, but as long as they have
different names they coexist.

**Mitigation**: in `Base.lean` we REMOVE the `axiom three_dvd_gal_card`
declaration entirely; in `main.lean` we ADD the `theorem` version. No
name collision; both contribute to the namespace.

### Risk 3: existing PRs in flight that reference the parent

**Concern**: if another researcher pushes an edit to `InverseGaloisA5.lean`
between S4 ACT and S5 (split), the `git mv` step in S5 might lose those
edits.

**Mitigation**: at the start of S5, `git fetch origin main && git log
--since "2026-05-13" -- proofs/Proofs/InverseGaloisA5.lean` to find any
pending edits. If found, defer S5 until the PR merges, then rebase.
Also: a single-file-rename followed by edits is fundamentally lossy
to merge tools, so prefer to **NOT use `git mv`**: instead, create
`Base.lean` by copying the parent file content directly, then delete
the parent file in a separate commit step. This makes the diff
auditable.

### Risk 4: Docker build time for the split

**Concern**: splitting a 2067-LOC file into 1800 + 250 + 76 + import
boilerplate would naively rebuild ALL three files. Mathlib pin still
required.

**Mitigation**: incremental build should be faster than the parent
alone, since the inner files (Base, Dedekind) can be cached
independently of `main.lean`. Worst-case end-to-end: similar to
current parent ~12-min Docker build.

## Anti-targets

This memo deliberately does **not**:

1. **Execute S4 ACT**. That's the discharge of
   `exists_gal_order_three` via S3 substep a + b + c integration —
   a separate ACT-style PR with Docker build verification.

2. **Execute S5 (the split)**. PREP only. The actual
   `git mv` / split / rename happens in a future PR after S4 ACT lands.

3. **Touch any existing Lean file**. The diff snippets above are
   illustrative.

4. **Edit `problem.md` / `state.md` / `knowledge.md` / `meta.json` /
   the gallery JSON**. The meta.json delta in §6 is for S5's PR,
   not this PREP's.

5. **Address alternate routes R2 (full generality) or R3
   (resolvent sextic)**. Those are knowledge.md § "Mathlib gap
   analysis" items. This PREP commits to R1 (specialised Dedekind
   at p=7).

6. **Pre-discharge the `exists_gal_order_three` sorry**. S3
   substep (a) + (b) + (c) memos design this; S4 ACT executes it.
   This S4 PREP is about what happens *after* the sorry is closed.

7. **Address sibling open questions** (oq-01 has subqueries; other
   inverse-Galois slugs in the gallery for solvable groups, etc.).

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 02:55 UTC): 0.
  The 6 prior PRs are all merged.
- **Conflict surface**: zero. Strictly additive single-file PR (a
  new memo under `sessions/`).
- **Most recent merges**:
  - PR #18416 (S3 ORIENT sub-step (a) typeclass plumbing) —
    addresses *one* component of the S4 ACT chain. **No overlap**
    with this PREP (which is about post-ACT choreography).
  - PR #18378 (S3 ORIENT sub-step (c) Frobenius order) — same.
  - PR #18315 (S3 ORIENT sub-step (b) prime ideal via Kummer-Dedekind).
  - PR #18242 (S3 ORIENT refinement Mathlib audit).
  - PR #18155 (S2 ORIENT scaffold).
  - PR #18129 (S1 OBSERVE).
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4 PREP).

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/inverse-galois-a5-oq-01/sessions/2026-05-13-s4-prep-parent-axiom-replacement-choreography.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file (`InverseGaloisA5.lean`,
  `InverseGaloisA5Dedekind.lean`, `Proofs.lean` all untouched)
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S3 sub-step a, b, c)

## Honesty

- **Difficulty**: this memo is **moderate** in conceptual content
  (the circular-import issue is a real but standard Lean 4 import-graph
  problem). The mathematical content is zero — this is purely a
  refactoring / status-transition plan.
- **Significance**: high practical value. Without this PREP, the
  next researcher would attempt the naive `axiom → theorem`
  replacement, hit the circular-import error, and either:
  - rediscover Strategy B independently (waste 30-60 min), OR
  - default to Strategy A and bloat the parent (lose modularity).

  This PREP saves that exploration time and commits to the right
  refactoring strategy.
- **Correction to companion file**: the comment in
  `InverseGaloisA5Dedekind.lean:83-88` describing the future S4 plan
  is **incorrect as written** (would create a cycle). Strategy B
  is the correct path; the implementer of S5 should update that
  comment when performing the split.
- **Status after ACT + S5**: parent upgrades to `verified`
  (`status: verified`, `badge: original`, `axiomCount: 0`,
  `assumptions: "0 axioms..."`). The gallery's first non-solvable
  inverse-Galois realisation becomes fully verified.

## Implementation hand-off checklist

For the next researcher implementing S5 (after S4 ACT lands):

- [ ] Verify S4 ACT has merged (the companion's
  `exists_gal_order_three` is no longer `sorry`).
- [ ] Verify no in-flight edits to `InverseGaloisA5.lean` (per Risk 3
  above).
- [ ] Copy current `InverseGaloisA5.lean` content into a new file
  `InverseGaloisA5Base.lean` (don't use `git mv` — see Risk 3
  mitigation).
- [ ] In `Base.lean`: delete `axiom three_dvd_gal_card` (currently
  line 309) and everything from `q_gal_card` (line ~1907) to end
  of `Part XVII` (line ~2060).
- [ ] In `InverseGaloisA5Dedekind.lean`: change
  `import Proofs.InverseGaloisA5` to
  `import Proofs.InverseGaloisA5Base`.
- [ ] Create new `InverseGaloisA5.lean` with: imports, `namespace`
  block, the new `theorem three_dvd_gal_card := ...`, then the
  150 LOC of `q_gal_card` + `q_gal_iso_a5` + `a5_realizable_iso`
  + `gal_not_solvable` originally in lines 1907-2060 of the old
  parent.
- [ ] Update `proofs/Proofs.lean` umbrella: add
  `import Proofs.InverseGaloisA5Base` in alphabetical position.
- [ ] Update `src/data/proofs/inverse-galois-a5/meta.json` per §"Step 5".
- [ ] Update `src/data/research/problems/inverse-galois-a5-oq-01.json`
  per §"Step 6".
- [ ] Update companion-file comment at
  `InverseGaloisA5Dedekind.lean:83-88` removing the
  "in S4 the parent's `axiom` will be rewritten" mention (now
  accurate: the parent's `axiom` was rewritten as the new
  `InverseGaloisA5.lean` `theorem`).
- [ ] Docker build all three:
  `./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5Base`,
  then `Proofs.InverseGaloisA5Dedekind`, then `Proofs.InverseGaloisA5`.
- [ ] Update state.md and knowledge.md for the slug with the
  S5 completion note.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s4-prep-parent-axiom-replacement-choreography.md`
      file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all merged session memos:
      - `2026-05-12-s3-orient-substep-a-typeclass-plumbing.md`
      - `2026-05-12-s3-orient-substep-b-prime-ideal-via-kummer-dedekind.md`
      - `2026-05-12-s3-orient-substep-c-frobenius-order.md`
- [x] Circular-import analysis verified by reading current
      `InverseGaloisA5Dedekind.lean:2` (imports
      `Proofs.InverseGaloisA5`) and `InverseGaloisA5.lean:309`
      (the `axiom`)
- [x] Strategy B preserves the `InverseGaloisA5` namespace fully
      (both Base and main use the same namespace block)
- [x] Companion file's existing structure preserved under Strategy B
      (only the `import` line changes)
- [x] meta.json transition `axiomatized → verified` requires
      4 field changes: `status`, `badge`, `axiomCount`, `assumptions`
- [x] Comment-correction needed at
      `InverseGaloisA5Dedekind.lean:83-88` (incorrect naive plan)

## References

- Parent: `proofs/Proofs/InverseGaloisA5.lean` (2067 LOC, 1 axiom at
  line 309).
- Companion: `proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 LOC,
  1 sorry until S4 ACT discharges it).
- Sibling memos (S3 sub-step ORIENT chain):
  - `sessions/2026-05-12-s3-orient-substep-a-typeclass-plumbing.md`
  - `sessions/2026-05-12-s3-orient-substep-b-prime-ideal-via-kummer-dedekind.md`
  - `sessions/2026-05-12-s3-orient-substep-c-frobenius-order.md`
- Gallery entry: `src/data/proofs/inverse-galois-a5/meta.json`
  (currently `status: axiomatized`, target after S5: `verified`).
- Lean 4 module-system reference:
  https://leanprover.github.io/theorem_proving_in_lean4/ (acyclic
  import constraints).
