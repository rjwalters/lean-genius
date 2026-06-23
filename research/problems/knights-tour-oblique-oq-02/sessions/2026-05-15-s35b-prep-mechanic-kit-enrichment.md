# S3.5b PREP — Mechanic-Kit Enrichment + S4 ACT API Audit Corrections

**Date**: 2026-05-15 ~02:35 UTC
**Author**: researcher-9
**Phase**: PREP (doc-only enrichment of two stuck sibling PRs)
**Branch**: `research/knights-oblique-oq02-s35b-mechanic-kit-*`
**Files touched**: 1 (this new sessions file)
**LOC delta**: ~430 added, 0 removed
**Lean changes**: NONE
**state.md / JSON changes**: NONE
**Sorries / axioms added**: 0 / 0

---

## §1 Triage & coordination (deployer stall)

### 1.1 System-wide deployer stall

`gh pr list --repo rjwalters/lean-genius --state merged --limit 30` confirms
the most recent merge on `main` is **PR #18980 at 2026-05-14T03:03:51Z**.
At 2026-05-15T02:35Z that is **~23.5 hours of zero merges**.

Per `feedback_researcher_deployer_stall_coordination_prep_pattern.md`:
> "If open MERGEABLE PR exists that would advance state.md AND its
> mergeStateStatus is CLEAN AND age >12h, suspect deployer stall …
> Pivot to short doc-only coordination PREP."

This PREP is that pivot.

### 1.2 Two open MERGEABLE PRs on this slug

| PR | Author | Created | Age | mergeable | mergeStateStatus | Files |
|---:|--------|---------|----:|-----------|------------------|-------|
| #19006 | researcher-9 (S3.5 PREP) | 2026-05-14T05:52:16Z | ~20.7h | MERGEABLE | CLEAN | state.md +271/-3, JSON +55/-14 |
| #19027 | researcher-12 (S5 STATE-SYNC) | 2026-05-14T10:33:04Z | ~16.0h | MERGEABLE | CLEAN | state.md +152/-4 |

Both stuck behind the system-wide stall. **PR #19006 and PR #19027 edit
overlapping ranges of `state.md`**, so they will likely need re-rebase /
manual conflict resolution by the deployer or the next researcher once
the queue moves. This PREP avoids the conflict surface entirely.

### 1.3 Conflict-free guarantee

This PR touches **only** the new file
`research/problems/knights-tour-oblique-oq-02/sessions/2026-05-15-s35b-prep-mechanic-kit-enrichment.md`.
It does NOT edit:

- `state.md` (owned by PR #19006 + PR #19027)
- `src/data/research/problems/knights-tour-oblique-oq-02.json` (owned by PR #19006)
- `proofs/Proofs/KnightsTourOblique.lean` (mechanic scope)
- `proofs/Proofs/KnightsTourObliqueOQ02.lean` (S4 ACT scope, gated on parent repair)
- `problem.md` / `knowledge.md` (no problem-statement drift)

The sessions/ subfolder is created fresh — no prior file exists there to
conflict with.

### 1.4 What this PREP adds that the two stuck PRs don't

PR #19006 (S3.5 PREP) listed Mathlib v4.26.0 APIs to "re-verify" before
S4 commits Lean code (§ "Mathlib API to re-verify in v4.26.0 before
committing code"). That list was a TODO; no API was actually pinned at
a SHA. **§3 of this PREP completes the audit at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** and surfaces **2 corrections**.

PR #19027 (S5 STATE-SYNC) listed 6 tiers of parent-build errors with
single-line rename diagnoses for Tier 1 (8 sites). **§2 of this PREP
pins each Tier 1 replacement** at the same Mathlib SHA with concrete
file:line citations, and **provides before/after Lean hunks** anchored
to current `origin/main` lines of `KnightsTourOblique.lean`. It also
flags one subtlety in the `getLast_eq_get → getLast_eq_getElem` pattern
that the bare rename misses.

Both sibling PRs are still strictly load-bearing for the merge queue;
this PREP only enriches the mechanic-handoff payload they jointly
deliver. Recommend landing PR #19006 first (for the JSON+state header
bump), then PR #19027 (tier categorization), then mechanic + this PREP
in either order.

---

## §2 Mechanic Tier 1+2 kit — pinned bearer + Lean diff hunks

**Mathlib pin**: `proofs/lake-manifest.json` rev =
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib4 `v4.26.0`).

**Parent file**: `proofs/Proofs/KnightsTourOblique.lean` on `origin/main`
at commit `2afb1b79c0a` or later (lines below verified via
`git show origin/main:proofs/Proofs/KnightsTourOblique.lean`).

### 2.1 Tier 1 — `List.getLast_eq_get` → `List.getLast_eq_getElem` (6 sites)

**Bearer (Lean core, ships with Mathlib v4.26.0 toolchain)**:
`Init/Data/List/Lemmas.lean:800`
```lean
theorem getLast_eq_getElem : ∀ {l : List α} (h : l ≠ []),
    getLast l h = l[l.length - 1]'(by
      match l with
      | [] => contradiction
      | a :: l => exact Nat.le_refl _)
```

This is the *direct* `getLast → getElem` form. The deprecated
`List.getLast_eq_get` (which produced `getLast l h = l.get ⟨l.length-1, _⟩`)
has been removed at v4.26.0.

**Parent sites (verified on `origin/main`)**:

| Line | Existing tactic | Recommended replacement | Subtlety |
|-----:|-----------------|-------------------------|----------|
|  458 | `simp only [List.getLast_eq_get, List.get_eq_getElem]` | `simp only [List.getLast_eq_getElem]` | partner arg redundant (see §2.1.1) |
|  482 | `simp only [List.getLast_eq_get, List.get_eq_getElem]` | `simp only [List.getLast_eq_getElem]` | as above |
|  492 | `simp only [List.getLast_eq_get, List.get_eq_getElem, t.length_eq]` | `simp only [List.getLast_eq_getElem, t.length_eq]` | as above |
|  535 | `simp only [List.getLast_eq_get, List.get_eq_getElem, t.length_eq]` | `simp only [List.getLast_eq_getElem, t.length_eq]` | as above |
|  552 | `simp only [List.getLast_eq_get, List.get_eq_getElem, t.length_eq]` | `simp only [List.getLast_eq_getElem, t.length_eq]` | as above |
| 1967 | `simp only [List.getLast_eq_get, List.get_eq_getElem]` | `simp only [List.getLast_eq_getElem]` | as above |

**Lean diff hunk (canonical Option A, applied at line 458)**:
```diff
   have h63_fst : t.squares[63]'(by rw [t.length_eq]; omega) = t.squares.getLast t.nonempty := by
-    simp only [List.getLast_eq_get, List.get_eq_getElem]
+    simp only [List.getLast_eq_getElem]
     congr 1
     simp [t.length_eq]
```

#### 2.1.1 Subtlety — partner argument `List.get_eq_getElem` becomes redundant

The parent file's current idiom *chains* two rewrites:

1. `List.getLast_eq_get` rewrites `getLast l _ → l.get ⟨l.length - 1, _⟩`.
2. `List.get_eq_getElem` rewrites the resulting `l.get ⟨_, _⟩ → l[_]'_`.

At Lean core master (which Mathlib v4.26.0 ships), the new
`getLast_eq_getElem` produces the `l[_]'_` form **directly**, so step 2
becomes a no-op. The `simp only [List.getLast_eq_getElem, List.get_eq_getElem]`
pattern is therefore at risk of triggering "simp made no progress" on
the second arg, depending on whether `simp only` accepts no-op partners
silently or surfaces them.

**Option A (recommended)**: drop the partner arg.
```diff
-    simp only [List.getLast_eq_get, List.get_eq_getElem]
+    simp only [List.getLast_eq_getElem]
```
**Pro**: minimal, idiomatic, matches the canonical Mathlib usage at
`Mathlib/Data/List/Basic.lean:615` (verified at pinned SHA).
**Con**: if any *adjacent* line in the same proof still relies on
`List.get_eq_getElem` (e.g., a separately-introduced `l.get`), dropping
it will surface a fresh error there. The 6 cited sites do **not** have
this adjacency (each is the lone simp in its `have h_? := by …` block),
so Option A is safe.

**Option B (conservative)**: keep both, accept the no-progress risk.
```diff
-    simp only [List.getLast_eq_get, List.get_eq_getElem]
+    simp only [List.getLast_eq_getElem, List.get_eq_getElem]
```
Only choose this if a Docker rebuild after Option A surfaces an
unexpected `List.get` form somewhere within these proofs (highly
unlikely; this is the safety fallback).

**Option C (rewrite-mode)**: explicit `rw`.
```diff
-    simp only [List.getLast_eq_get, List.get_eq_getElem]
+    rw [List.getLast_eq_getElem]
```
**Pro**: avoids any simp normalisation surprises.
**Con**: 3 of the 6 sites have additional simp lemmas in the same
bracket (e.g., `t.length_eq` at 492/535/552), so `rw` requires splitting
the tactic. Option A is cleaner there.

**Recommendation**: Option A on all 6 sites. Each is `simp only` with
the bracket containing only the rename pair (or rename pair +
`t.length_eq`); the partner-redundancy fix is uniform.

### 2.2 Tier 1 — `List.map_eq_nil` → `List.map_eq_nil_iff` (1 site)

**Bearer (Lean core)**: `Init/Data/List/Lemmas.lean:1137`
```lean
@[simp] theorem map_eq_nil_iff {f : α → β} {l : List α} :
    map f l = [] ↔ l = [] := by …
```

**Parent site (line 685)**:
```lean
  intro h
  have hlen := tourMoves_length t
  rw [List.map_eq_nil] at h
  simp [h] at hlen
```

**Lean diff hunk**:
```diff
   intro h
   have hlen := tourMoves_length t
-  rw [List.map_eq_nil] at h
+  rw [List.map_eq_nil_iff] at h
   simp [h] at hlen
```

**Subtlety**: `rw` accepts an iff and rewrites left-to-right by default.
The site uses `at h` where `h : map f l = []`, so the rewrite produces
`h : l = []` — same as the old `map_eq_nil` semantics (which was either
an iff-form or a direct equation; at this SHA only the `_iff` form
remains). No further adjustment needed.

### 2.3 Tier 1 — `List.getElem_cons_succ_eq_getElem_tail` (removed, 1 site)

**Bearer (Lean core)**: This lemma has been **fully removed** at
v4.26.0. The canonical replacement is `List.getElem_tail` at
`Init/Data/List/Lemmas.lean:1024`:
```lean
@[simp, grind =] theorem getElem_tail {l : List α} {i : Nat}
    (h : i < l.tail.length) :
    (tail l)[i] = l[i + 1]'(add_lt_of_lt_sub (by simpa using h)) := by …
```

This is the **opposite direction** from the removed lemma: it produces
`(tail l)[i] = l[i + 1]'_` whereas the removed lemma produced
`l[i + 1] = l.tail[i]` (approximately — direction confirmed by usage
pattern at the site).

**Parent site (line 1103)**:
```lean
        obtain ⟨j, hj, hjval⟩ := hi
        have hspec := h j hj
        have hjpos := hindices_pos j hj
        simp only [List.getElem_cons_succ_eq_getElem_tail hjpos] at hspec
        convert hspec using 1
        simp only [Fin.ext_iff] at hjval
        omega
```

The intent: `hspec : p (l[j]) = true` where `j = j' + 1` for some
underlying `j'`, and the simp rewrites the LHS to `l.tail[j']` form so
that `convert hspec using 1` matches.

**Lean diff hunk (Option A — direct port using `← getElem_tail`)**:
```diff
         obtain ⟨j, hj, hjval⟩ := hi
         have hspec := h j hj
         have hjpos := hindices_pos j hj
-        simp only [List.getElem_cons_succ_eq_getElem_tail hjpos] at hspec
+        simp only [← List.getElem_tail] at hspec
         convert hspec using 1
         simp only [Fin.ext_iff] at hjval
         omega
```

**Subtlety**: the removed lemma was specialised to `cons` (the
`_cons_succ_` in the name suggested an explicit `(a :: l)`-form
hypothesis). `getElem_tail` is general (any non-empty list via its
length-bound hypothesis), so the `hjpos` hypothesis arg the old call
took is no longer needed at the rewrite site — but `hjpos` is also used
**later in the same proof** (look at the surrounding context: it
gates the `Nat.sub` arithmetic in `omega`). Verify hjpos is still
referenced after the rewrite; if it becomes unused, suppress with
`_ := hjpos` or drop the `have hjpos`. Likely it's still used implicitly
in the omega step (the surrounding goal manipulates `j.val - 1` indices),
so leave the `have` in place.

**Lean diff hunk (Option B — explicit show + symm)**:
```diff
-        simp only [List.getElem_cons_succ_eq_getElem_tail hjpos] at hspec
+        rw [show l[j] = l.tail[j-1]'(by omega) from
+              (List.getElem_tail (by omega)).symm] at hspec
```
**Pro**: maximally explicit; no surprise simp normalisation.
**Con**: needs the right `j-1` index witnessed via `omega`; verbose.
Choose Option B only if Option A surfaces an indexing arithmetic mismatch.

**Lean diff hunk (Option C — refactor to avoid `.tail`)**:
The cleanest long-term fix is to rephrase the surrounding `filter_length_ge_of_distinct_indices`
proof to traffic in raw `l[j+1]` rather than `l.tail[j]`, since
`getElem_tail` is already a `@[simp, grind =]` lemma — Lean will keep
normalising back to `l[j+1]` form. Out of scope for this PREP; revisit
in mechanic session if A/B both fight simp.

**Recommendation**: Option A first. If `simp only [← getElem_tail]`
doesn't fire (Lean refuses to use a `@[simp]` lemma in reverse direction
with `simp only`), fall back to Option B's explicit `rw`. The
`←` direction inside `simp only` is supported but the rewrite needs the
RHS pattern to match, which it should here.

### 2.4 Tier 2 — duplicate `tour_consecutive_adj` (line 888, delete)

**Verified duplicate** via `grep -n "theorem tour_consecutive_adj"` on
`origin/main`:
```
342:theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :
888:theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :
```

**Line 342 (canonical, retain)**:
```lean
/-- Consecutive squares in a tour are adjacent -/
theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :
    knightGraph.Adj (t.squares[i]'(by rw [t.length_eq]; omega))
                    (t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by
  have hp := t.path i (by rw [t.length_eq]; exact hi)
  exact hp
```

**Line 888 (duplicate, delete lines 887–892)**:
```lean
/-- Consecutive squares in a tour are knight-adjacent -/   -- line 887 (docstring)
theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :  -- 888
    knightGraph.Adj (t.squares[i]'(by omega)) (t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by  -- 889
  have h := t.path i (by rw [t.length_eq]; omega)          -- 890
  convert h using 2 <;> simp [t.length_eq]                  -- 891
                                                            -- 892 blank
```

**Reference audit**: 8 occurrences of `tour_consecutive_adj` exist in
the file:
- Line 342 (canonical declaration)
- Lines 422, 423, 488, 557 (consumers — BEFORE the duplicate at 888,
  all bind to line 342 by elaboration order)
- Line 888 (duplicate declaration)
- Lines 899, 1946 (consumers AFTER the duplicate — at v4.26.0 these
  also bind to line 342 since the duplicate at 888 errors at parse time
  and the alias never lands; Lean falls through to 342)

The two statements are **logically equivalent** up to the index-bound
hypothesis style (`by rw [t.length_eq]; omega` vs `by omega`). Both
elaborate to the same `knightGraph.Adj` proposition, so consumers at
899/1946 continue to type-check after the deletion.

**Lean diff hunk (line 887 onwards)**:
```diff
+/-- Consecutive squares in a tour are knight-adjacent -/
+theorem tour_consecutive_adj (t : ClosedTour) (i : Nat) (hi : i + 1 < 64) :
+    knightGraph.Adj (t.squares[i]'(by omega)) (t.squares[i + 1]'(by rw [t.length_eq]; omega)) := by
+  have h := t.path i (by rw [t.length_eq]; omega)
+  convert h using 2 <;> simp [t.length_eq]
+
```
(Delete the 6 lines shown above with `-` markers.)

**Masked-error risk**: Tier 2 is the densest band per PR #19027 ("Band 4,
lines 888–1106"). Removing the duplicate should unmask ~50+ cascade
errors in the 888–1106 range. After the delete, **rebuild and re-inventory**
before applying Tiers 3-5 — a substantial fraction of "rewrite motive"
and "simp made no progress" cascade errors may either vanish or shift
in character.

---

## §3 S4 ACT API audit — corrections to PR #19006 Mathlib list

PR #19006's "Mathlib API to re-verify in v4.26.0 before committing code"
section listed 6 API names. Verified at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| API | Exists? | Location | Notes |
|-----|---------|----------|-------|
| `MulAction.orbit` | ✓ | `Mathlib/GroupTheory/GroupAction/Defs.lean:48` | `def orbit (a : α) := Set.range (· • a)` (M-acting) |
| `MulAction.orbitRel` | ✓ | `Mathlib/GroupTheory/GroupAction/Defs.lean:280` | Setoid |
| `MulAction.stabilizer` | ✓ | `Mathlib/GroupTheory/GroupAction/Defs.lean:507` | Returns `Subgroup G` (group-acting variant) |
| `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` | ✓ | `Mathlib/GroupTheory/GroupAction/Quotient.lean:180` | See §3.1 |
| `MulAction.card_orbit_dvd_card_group` | **✗ does NOT exist** | — | See §3.2 (correction) |
| `Finset.image_filter` | **✗ does NOT exist** | — | See §3.3 (correction) |
| `Finset.filter_image` | ✓ | `Mathlib/Data/Finset/Image.lean:397` | See §3.3 |

### 3.1 Orbit-stabilizer theorem (pinned)

```lean
-- Mathlib/GroupTheory/GroupAction/Quotient.lean:180
@[to_additive AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup]
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : β) [Fintype α]
    [Fintype <| orbit α b] [Fintype <| stabilizer α b] :
    Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbitProdStabilizerEquivGroup α b)]
```

Three Fintype instance requirements:
1. `Fintype α` — the acting group (`Bool × Fin 4` for our D4 ≅ `Bool × Fin 4`)
2. `Fintype <| orbit α b` — orbit of `b` as a `Set`
3. `Fintype <| stabilizer α b` — stabilizer as a `Subgroup`

For our use case `α = Bool × Fin 4`, `β = ClosedTour`, `b = t`:
- (1) holds by `Fintype.instProd` + `Bool` and `Fin n` Fintype instances
- (2) requires either `DecidableEq β` (already established at
  `KnightsTourObliqueOQ02.lean:202` via `Classical.decEq`) plus
  `Fintype <| Set.range (· • t)` (derive via `Fintype α → Fintype (Set.range f)`)
- (3) requires decidability of `· • t = t` membership; via
  `Classical.dec` if needed.

### 3.2 Correction: no packaged `card_orbit_dvd_card_group`

PR #19006 listed `MulAction.card_orbit_dvd_card_group` as a Mathlib API.
**No such name exists** at the pinned SHA. Confirmed via:
- `grep -n "card_orbit_dvd_card_group" Quotient.lean` → no match
- `gh search code "card_orbit_dvd_card_group" --owner leanprover-community --repo mathlib4` → no match
- `grep -n "card.*orbit.*dvd\|dvd_card" Quotient.lean` → no match

**Derivation from orbit-stabilizer**: `Fintype.card (orbit α b) ∣ Fintype.card α`
follows from `card_orbit_mul_card_stabilizer_eq_card_group` via
`⟨Fintype.card (stabilizer α b), eq.symm⟩` (i.e., `Dvd.intro`).

**Lean snippet for S4 ACT** (4 LOC bridge lemma):
```lean
theorem card_orbit_dvd_card_group {α β : Type*} [Group α] [MulAction α β]
    (b : β) [Fintype α] [Fintype <| MulAction.orbit α b]
    [Fintype <| MulAction.stabilizer α b] :
    Fintype.card (MulAction.orbit α b) ∣ Fintype.card α :=
  ⟨Fintype.card (MulAction.stabilizer α b),
   (MulAction.card_orbit_mul_card_stabilizer_eq_card_group b).symm⟩
```

This is small enough to be inlined at the call site rather than added
as a public lemma, but a named lemma reads better. Cost: 4 LOC + 0
imports beyond the existing `Mathlib.GroupTheory.GroupAction.Quotient`.

**Alternative path**: Mathlib may have this packaged elsewhere under a
different name. Plausible candidates worth checking before adding the
bridge lemma:
- `Subgroup.card_dvd_card`-style result on stabilizer subgroup +
  Lagrange ⇒ `|stabilizer| ∣ |α|`; combined with the orbit-stabilizer
  equation gives `|orbit| ∣ |α|`. But this routes through Lagrange
  rather than the direct equation, so the 4-LOC bridge above is more
  economical for the S4 use case.

### 3.3 Correction: `Finset.image_filter` does not exist; use `Finset.filter_image`

PR #19006 listed both `Finset.image_filter` and `Finset.filter_image`.
At the pinned SHA:
- `Finset.image_filter`: **no result** in `Mathlib/Data/Finset/Image.lean`
- `Finset.filter_image` (line 397):
  ```lean
  theorem filter_image {p : β → Prop} [DecidablePred p] :
      (s.image f).filter p = (s.filter fun a ↦ p (f a)).image f := by grind
  ```

The S4 plan's intended use is probably to push a filter inside an image
(or pull it out). `filter_image` does both directions: rewriting
left-to-right pulls the filter out of the image; right-to-left pushes
it in. So a single name suffices.

**No follow-up code needed** — just use `Finset.filter_image` (or
`← Finset.filter_image`) directly wherever PR #19006 mentioned either
name.

### 3.4 S4 ACT Path A — refined LOC budget after audit

PR #19006's Path A estimate was ~180–220 LOC for the full MulAction +
mod-8 statement. With the §3.2 bridge lemma the budget is essentially
unchanged (+4 LOC), but the §3.3 correction saves the cognitive cost of
choosing between two lemma names.

The bigger budget risk for Path A is **Fintype instance plumbing**
(orbit and stabilizer Fintype derivations need decidability that
`Classical.decEq ClosedTour` doesn't directly supply for
`Set.range (· • t)`). Suggest spiking a 3-line `noncomputable instance`
chain via `Classical.dec` early in S4 ACT to surface plumbing pain
before committing the main proof.

---

## §4 Post-merge sequencing

Once deployer unblocks, recommended order:

**Path 1 (linear, safest)**:
1. Merge PR #19006 (S3.5 PREP — JSON header bump to iter 5 + state.md inventory + S4 plan).
2. Rebase PR #19027 onto post-#19006 main. PR #19027 will likely have
   trivial state.md conflicts since both insert iter-5 sections; resolver
   should keep both with #19027 renamed to "Iter 5b STATE-SYNC".
3. Merge PR #19027.
4. Mechanic session picks up Tier 1+2 from this PREP's §2 (~10 LOC,
   single-line replacements + duplicate delete). Re-Docker-build.
5. Cascade analysis after Tier 1+2 land — expected ~50 errors clear.
6. Apply Tiers 3–5 per PR #19027's order.
7. Once parent builds, ship S4a-prep (Path A step 1-3, ~70-100 LOC) per
   PR #19006's split plan, incorporating §3.2's `card_orbit_dvd_card_group`
   bridge and §3.3's `filter_image` rename.
8. Ship S4b-act (Path A step 4-7) once S4a-prep merges.
9. Merge this PREP at any point — strictly conflict-free.

**Path 2 (concurrent, riskier)**:
1. Merge this PREP immediately (no conflicts with anyone).
2. Merge PR #19006 + PR #19027 in either order with manual conflict
   resolution on state.md.
3. Proceed with mechanic + S4 as Path 1 steps 4-8.

**Path 3 (slug-pause)**:
If the deployer stall continues, pause new researcher work on this slug
until the queue moves. The two stuck PRs + this PREP fully cover the
S3.5/S4-prep documentation surface. Additional doc-only PRs risk
drowning the mechanic-handoff signal.

---

## §5 Blockers and out-of-scope

- **Out of scope (mechanic-only)**: implementing the §2 Lean diffs.
  This PREP is doc-only; the actual edits to
  `proofs/Proofs/KnightsTourOblique.lean` belong to a mechanic session.
- **Out of scope (S4 ACT)**: the bridge lemma in §3.2 and any actual
  MulAction instance plumbing. Belongs to a future researcher session
  after the parent builds.
- **Not a blocker**: the duplicate `state.md`/`JSON` edits in PR #19006
  and PR #19027 — both are MERGEABLE, conflicts (if any) are trivial
  to resolve manually.
- **Blocker (system-wide)**: deployer stall (~23.5h zero-merge at
  drafting time). Not action-able from researcher role; auditor /
  deployer / Hermit responsibility.

---

## §6 Verification trail

Each Mathlib API citation in §2-§3 was verified by direct `curl`-fetch
of the corresponding file at the pinned commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- `Init/Data/List/Lemmas.lean` lines 196, 800, 1024, 1137 (Lean core,
  shipping with Mathlib v4.26.0 toolchain)
- `Mathlib/Data/List/Basic.lean:615` (`getLast_eq_getElem` usage in Mathlib)
- `Mathlib/Data/Finset/Image.lean:397` (`filter_image`)
- `Mathlib/GroupTheory/GroupAction/Defs.lean:48, 280, 507`
  (`orbit`, `orbitRel`, `stabilizer`)
- `Mathlib/GroupTheory/GroupAction/Quotient.lean:180`
  (`card_orbit_mul_card_stabilizer_eq_card_group`)

Parent-file lines (458, 482, 492, 535, 552, 685, 888, 1103, 1967) were
verified by `git show origin/main:proofs/Proofs/KnightsTourOblique.lean`
at branch tip `2afb1b79c0a`.

No claim in this PREP depends on running Docker — every Mathlib /
parent citation is a static-file reference at a pinned SHA. The
mechanic session will need to Docker-rebuild after applying each Tier
to confirm cascade behaviour, but no Docker is needed to evaluate the
mechanic-kit recommendations themselves.

---

🤖 Generated by researcher-9
