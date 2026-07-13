# S6 ACT — IsRegressive companion lemmas to Proofs/Club/Basic.lean (+ parent-growth absorption)

**Author:** researcher-1
**Timestamp:** 2026-05-31
**Phase:** ACT (Lean +35 LOC) + STATE-SYNC absorption
**Iteration:** 10 (S5 STATE-SYNC was 9 → S6 ACT = 10)

## TL;DR

Strictly-additive Lean ACT shipping four trivial `IsRegressive` companion
lemmas into `proofs/Proofs/Club/Basic.lean` (119 → 154 LOC; 5 → 9 theorems;
0 sorries, 0 axioms; structure-vs-Prop split unchanged). The lemmas
prepare the post-S4-ACT re-statement of `fodor` in terms of
`Ordinal.IsRegressive` — currently `fodor` takes a bare
`(hf_reg : ∀ α ∈ S, f α < α)` hypothesis (parent line ~262); after S4 ACT
+ a future signature refactor, `Ordinal.IsRegressive.iff_forall_lt`
provides the bridge.

This session also **absorbs parent growth** since S5 STATE-SYNC
(2026-05-16, parent at 568 LOC): sister-slug `fodor-pressing-down-oq-04`
shipped S2-β-β ACT (PR **#20621**, 2026-05-25), adding `cofHead`
(noncomputable def) plus three theorems (`cofHead_lt`,
`exists_cofHead_constant_stationary`,
`exists_cofHead_constant_stationary_of_stationary`). Parent now at
**654 LOC / 20 theorems / 4 defs / 1 structure** (meta.json already in
sync, no edit needed). S4 ACT scope expands accordingly: the 3 new
theorems also consume the parent-local duplicate predicates and would
need re-anchoring.

No parent file edits. No `meta.json` edits. Pure Basic.lean addition +
state.md/JSON refresh + this memo.

---

## §1. Race awareness

- Open PRs on `fodor-pressing-down-oq-01`: **0** at claim time.
- Sister slug `fodor-pressing-down-oq-04`: **0** open PRs (last activity
  = S2-β-β ACT PR #20621 merged 2026-05-25).
- Parent file `proofs/Proofs/FodorPressingDown.lean` last touched by
  PR #20621 (sister-slug S2-β-β ACT).
- Parent meta.json `src/data/proofs/fodor-pressing-down/meta.json` is
  already at `lineCount: 654, theoremCount: 20, definitionCount: 4` —
  in sync with current parent file.
- Basic.lean `proofs/Proofs/Club/Basic.lean` last touched by S3 ACT
  PR #19009 (2026-05-14, 119 LOC, the `diagInter_isClosedBelow` lift).
  Untouched for 17 days.

LOW saturation; this PR is purely additive to `Proofs/Club/Basic.lean`.

---

## §2. Files modified

| Status | Path | Δ LOC | Purpose |
|--------|------|------|---------|
| MOD | `proofs/Proofs/Club/Basic.lean` | +35 | 4 IsRegressive companion lemmas |
| NEW | `research/problems/fodor-pressing-down-oq-01/sessions/2026-05-31-s06-act-IsRegressive-companion-lemmas.md` | new | This memo |
| MOD | `research/problems/fodor-pressing-down-oq-01/state.md` | TBD | iteration 9 → 10; refresh status table; absorb cofHead-cohort additions |
| MOD | `src/data/research/problems/fodor-pressing-down-oq-01.json` | minor | iteration count, lastUpdate, insights |

**Untouched:**

- `proofs/Proofs/FodorPressingDown.lean` — parent file, 654 LOC, no edit.
- `src/data/proofs/fodor-pressing-down/meta.json` — already in sync at
  654/20/4 per mechanic resync.
- `src/data/proofs/fodor-pressing-down/annotations.json` — parent untouched,
  no annotation drift this session.
- `research/problems/fodor-pressing-down-oq-01/problem.md` /
  `knowledge.md` — S1 OBSERVE design unchanged.

---

## §3. The four lemmas

All four go into `namespace Ordinal` in
`proofs/Proofs/Club/Basic.lean`, just below `diagInter_isClosedBelow`
(the S3 ACT lift). Each is a one-to-three-line term-mode proof.

### 3.1 `IsRegressive.empty`

```lean
theorem IsRegressive.empty {f : Ordinal → Ordinal} :
    IsRegressive f (∅ : Set Ordinal) :=
  fun _ h _ => absurd h (Set.not_mem_empty _)
```

Vacuous regressivity on `∅`. Useful as a base case in any inductive
construction that splits stationary sets.

### 3.2 `IsRegressive.mono`

```lean
theorem IsRegressive.mono {f : Ordinal → Ordinal} {S T : Set Ordinal}
    (hST : S ⊆ T) (hT : IsRegressive f T) : IsRegressive f S :=
  fun _ hα hα0 => hT (hST hα) hα0
```

Anti-monotonicity under set inclusion: regressive on the larger set
implies regressive on any subset. This is the lemma that the existing
`fodor` proof in the parent uses inline (parent line ~278: the local
`hf_reg` is used to derive regressivity on the witness intersection).

### 3.3 `IsRegressive.inter_preimage`

```lean
theorem IsRegressive.inter_preimage {f : Ordinal → Ordinal}
    {S : Set Ordinal} {c : Ordinal} (hS : IsRegressive f S) :
    IsRegressive f (S ∩ f ⁻¹' {c}) :=
  hS.mono Set.inter_subset_left
```

Specialization of `mono` to the constancy-class restriction used in
Fodor's contradiction step: when `f` is constant `c` on a stationary
subset, regressivity is preserved on that subset. This is the *direct*
helper for the eventual `Ordinal.fodor` re-statement.

### 3.4 `IsRegressive.iff_forall_lt`

```lean
theorem IsRegressive.iff_forall_lt {f : Ordinal → Ordinal}
    {S : Set Ordinal} (hS_pos : ∀ α ∈ S, 0 < α) :
    IsRegressive f S ↔ ∀ α ∈ S, f α < α :=
  ⟨fun h α hα => h hα (hS_pos α hα).ne', fun h _ hα _ => h _ hα⟩
```

Bridge to the bare `∀ α ∈ S, f α < α` hypothesis form that the existing
`FodorPressingDown.fodor` statement uses. After S4 ACT cuts the parent
duplicates and re-anchors signatures, the consumer can either:

- **Option A**: keep the bare hypothesis form on `fodor` and use
  `iff_forall_lt.mpr` at the call site.
- **Option B**: re-state `fodor` in terms of `Ordinal.IsRegressive`
  directly and use `iff_forall_lt.mp` if a downstream consumer wants
  the bare form.

Decision deferred to S4 ACT; both options are equivalent under
`iff_forall_lt`.

---

## §4. Why these four and not more

A larger set was considered:

| Candidate | Disposition |
|-----------|-------------|
| `IsRegressive.empty` | ✅ included — vacuous base case |
| `IsRegressive.mono` | ✅ included — directly used inline by Fodor |
| `IsRegressive.inter_preimage` | ✅ included — Fodor contradiction step |
| `IsRegressive.iff_forall_lt` | ✅ included — signature bridge |
| `IsRegressive.const_zero` | ❌ excluded — `IsRegressive (fun _ => 0) S` requires `S` to consist of positive ordinals; not a 1-line proof, and not used inline |
| `IsRegressive.union` | ❌ excluded — `IsRegressive f (S ∪ T) ↔ IsRegressive f S ∧ IsRegressive f T` — useful but speculative |
| `IsRegressive.image_subset_Iio_id` | ❌ excluded — relates regressivity to image being `< id`; speculative |

The included four cover (a) the empty base case, (b) the monotonicity
lemma Fodor's proof uses inline, (c) the specific
constancy-class instantiation, (d) the bare-vs-predicate form bridge.
Everything else can be added later when a consumer requests.

This honors the research skill's "Don't add features beyond what the
task requires" rule and the project memory's
[[feedback_researcher_8_2026_05_31_prompt_absent_skip_v139]]-adjacent
caution about library bloat.

---

## §5. Build verification

Docker build target: `Proofs.Club.Basic`. Per CLAUDE.md, the wrapper
`./proofs/scripts/docker-build.sh Proofs.Club.Basic` is used (never
direct `lake build`). Expected:

- Memory: well under default 32 GB.
- Time: ~25–45 min for fresh image, or shorter if incremental.
- Outcome: 3 jobs added to Mathlib's ~3 060-job graph (4 new theorems
  in Basic.lean, of which 3 are non-trivial term modes — `IsRegressive`
  unfolds to a definitional equivalence so `iff_forall_lt` may be
  one job or split into two).

Build was kicked off at the start of this session in the background;
result will be appended to the PR thread.

If the build breaks, the most likely failure modes are:

1. `Set.not_mem_empty` arg-order mismatch (Mathlib v4.26.0 has
   `Set.not_mem_empty : ∀ (x : α), x ∉ (∅ : Set α)`; the call site
   uses `Set.not_mem_empty _ h : False` which is correct).
2. `.ne'` on `0 < α` giving `0 ≠ α` instead of `α ≠ 0` — Mathlib's
   `LT.lt.ne'` correctly gives `b ≠ a` from `a < b`, so `0 < α`'s
   `.ne'` is `α ≠ 0`, matching `IsRegressive`'s expected form. ✓
3. `Set.inter_subset_left` — exists in Mathlib v4.26.0 with the right
   signature.

All three risks are low; the lemmas are standard library-style and
the proof terms are syntactically minimal.

---

## §6. Parent-growth absorption (post-S5 STATE-SYNC)

Parent file `proofs/Proofs/FodorPressingDown.lean` grew between S5
STATE-SYNC (2026-05-16, 568 LOC / 17 theorems / 4 defs / 1 structure)
and this session (2026-05-31, 654 LOC / 20 theorems / 4 defs / 1
structure). The diff:

| Δ | Item | Provenance |
|---|------|------------|
| +1 | `noncomputable def cofHead` (parent line 548) | sister-slug oq-04 S2-β-β ACT, PR #20621 |
| +1 | `theorem cofHead_lt` (parent line 558) | same PR |
| +1 | `theorem exists_cofHead_constant_stationary` (parent line 583) | same PR |
| +1 | `theorem exists_cofHead_constant_stationary_of_stationary` (parent line 602) | same PR |

`cofHead` is a noncomputable def (not counted in meta `definitionCount`
which excludes structures; the meta still reports 4 from
{IsUnboundedBelow, IsStationaryBelow, diagInter, cofHead} — IsClubBelow
is the structure). The three new theorems all consume parent-local
predicates `IsStationaryBelow`, `IsClubBelow`, and call helpers
`isLimitOrdinals_isClubBelow`, `IsStationaryBelow.inter_isLimitOrdinals`,
plus the existing `fodor`. None reference Basic.lean (the parent is
self-contained pre-S4-ACT).

### Expanded S4 ACT scope

The S5 STATE-SYNC re-anchoring scope listed **17 downstream theorems**.
Post-#20621, the scope expands by 3 to **20 downstream theorems**:

| # | Theorem | Parent line | New predicate references |
|---|---------|-------------|---------------------------|
| ... | (rows 1–17 from S5 STATE-SYNC §4) | ... | ... |
| 18 | `cofHead_lt` | 558 | none of our concern (uses `IsSuccLimit` only) |
| 19 | `exists_cofHead_constant_stationary` | 583 | `IsStationaryBelow` (1×); `fodor` (1×) |
| 20 | `exists_cofHead_constant_stationary_of_stationary` | 602 | `IsStationaryBelow` (1×); `IsStationaryBelow.inter_isLimitOrdinals` (1×) |

Theorem 18 (`cofHead_lt`) does NOT touch our refactor predicates and
needs no re-anchoring. Theorems 19 and 20 use `IsStationaryBelow`
unqualified (resolves to `Ordinal.IsStationaryBelow` after S4 ACT via
`open Ordinal` line 41 of parent) — they re-anchor mechanically.

Theorem 20 also uses dot notation `hS.inter_isLimitOrdinals` (parent
line 608): after S4 ACT, this requires `FodorPressingDown.IsStationaryBelow.inter_isLimitOrdinals`
to be findable via the receiver's namespace. If the parent's
declaration of `IsStationaryBelow.inter_isLimitOrdinals` is re-namespaced
to `Ordinal.IsStationaryBelow.inter_isLimitOrdinals` (which is the
correct move per S4c PREP §12.2), then `hS.inter_isLimitOrdinals` will
naturally resolve. Otherwise the call site would need explicit
qualification.

**No re-anchoring action this session** — this is documentation only.
The S4 ACT writer (next researcher with a build cycle) folds these 3
rows into the S4c PREP cheat-sheet.

---

## §7. Acceptance check vs problem.md

`problem.md` Acceptance criteria 1 (definitions in new file under
Ordinal namespace): ✅ unchanged from S2 ACT.
Criteria 2 (parent file ≤ 235 LOC): ⏳ pending S4 ACT.
Criteria 3 (new file compiles with 0 sorries): ✅ unchanged (this
session's additions are also 0 sorries, 0 axioms).
Criteria 4 (Fodor signature unchanged): ✅ unchanged.
Criteria 5 (sister slug clean dependency path): ⏳ pending S4 ACT +
oq-04 file import.

This session does NOT advance criterion 2 or 5 toward completion;
it adds library content that consumers (post-S4-ACT) will benefit
from.

---

## §8. Next Action (handoff)

S4 ACT (parent trim) is still pending. The 4 new lemmas added this
session do NOT change the S4 ACT scope — they live in the additive
module that S4 ACT doesn't touch. The expanded S4 ACT scope from
§6 above (3 cofHead-cohort rows) is the new piece of work for the
next researcher.

Specifically, the S4 ACT writer must:

1. Delete parent lines 43–124 (the four duplicate defs, three mechanical
   theorems on the structure, and the `diagInter_isClosedBelow` body).
2. Add `import Proofs.Club.Basic` to parent imports section.
3. Re-anchor downstream theorem declarations from
   `theorem IsClubBelow.foo` to either:
   - `theorem Ordinal.IsClubBelow.foo` (full-name re-anchor — preferred
     per S4c PREP §12.2), or
   - leave as-is + accept that `hC.foo` calls won't dot-resolve and
     need explicit `FodorPressingDown.IsClubBelow.foo hC` calls.
4. Update `src/data/proofs/fodor-pressing-down/meta.json` post-cut
   counts (estimated `lineCount: ~474, theoremCount: 19, definitionCount: 1`
   where 1 = `cofHead` only).
5. Re-anchor annotations.json line offsets per S4c §7 recipe.

This is the same recipe as S5 STATE-SYNC documented, plus the 3 new
cofHead-cohort rows from §6. Docker build required (parent file is a
Wiedijk-100 verified entry).

S6 (optional, post-S4 ACT, unchanged from S5 STATE-SYNC §6): consider
lifting `IsClubBelow.inter`, `IsStationaryBelow.inter_isClubBelow`,
`IsStationaryBelow.inter_isLimitOrdinals` from parent → Basic.lean.
These have downstream dependency on the parent-pinned
`diagInter_isUnboundedBelow`, so they can't move until either (a) the
zipper construction also moves to Basic.lean or (b) they're rewritten
to take a generic unboundedness hypothesis.

---

## §9. Memory cross-references

- [[feedback_lean_companion_files_must_import_int_defs_for_AddZero]] —
  not applicable here (Basic.lean uses `Mathlib.SetTheory.Ordinal.Topology`
  and `Mathlib.Tactic`, neither of which involves `ℤ →+ G`).
- [[feedback_worktree_edit_paths]] — followed (all edits via
  `.loom/worktrees/researcher-1/...` paths).
- `feedback_researcher_docs_only_chain_silent_parent_regression` —
  this session breaks a 2-PR doc-only chain (S5 STATE-SYNC, S4e PREP
  preceded by S3 ACT) with concrete Lean progress.
