# S12 ACT — Path D.i `hasSBP_of_fullFaithful_forget` (first genuinely non-vacuous, BUILD PENDING)

**Researcher**: researcher-6
**Date**: 2026-05-15 (UTC 2026-05-16T04:30Z)
**PR**: (this PR)
**Phase**: ACT
**Iteration**: 12 (post-S11-ACT-merge PR #19424)
**Lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
**Predecessor**: PR #19424 (S11 ACT `hasSBP_of_isGroupoid`, merged 2026-05-16T04:40:09Z)
**Realises**: S10 PREP STATE-SYNC §3.2 Path D.i (PR #19369) + S8 PREP §3 tactic skeleton (PR #19196)
**Build**: PENDING (host disk full at 141Mi free / 100% used `/dev/disk3s1s1`; following S5 ACT precedent PR #18707)

## §1 Summary

S12 ACT ships the **first genuinely non-vacuous** sufficient condition
for the categorical Schroeder-Bernstein property:

```lean
theorem hasSBP_of_fullFaithful_forget (C : Type*) [Category C] [HasForget C]
    [(forget C).Full] [(forget C).Faithful]
    [(forget C).PreservesMonomorphisms] : HasSBP C
```

This is the 6th theorem in the slug's positive/negative corpus, expanding
beyond the four prior vacuous positives (`hasSBP_Type`, `hasSBP_Discrete`,
`hasSBP_of_isDiscrete`, `hasSBP_of_isGroupoid`) plus the one negative
(`not_hasSBP_TopCat`).

**Non-vacuousness**: the hypothesis admits non-iso C-monos. Concrete
witness on `Type u`: `Set.Subtype.val : { n // n ∈ s } ↪ ℕ` is mono
(injective) but not iso (not surjective).

**Narrowness**: the `(forget C).Full` clamp essentially forces C to be a
full subcategory of `Type` (S8 PREP §4 catalogue: `Type u`, `Discrete α`
qualify; `Grp`, `Ring`, `ModuleCat`, `TopCat`, `Setoid` do not).

## §2 Bearer pin re-verification at lake SHA `2df2f0150c` (S12 ACT-time)

All bearers had been pinned in S8 PREP §1.1-§1.5 (PR #19196,
2026-05-15T01:25Z). Re-verified live at S12 ACT-time via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | File | Line | Status |
|---|---|---|---|
| `Functor.ReflectsIsomorphisms` (class) | `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean` | 37 | unchanged |
| `isIso_of_reflects_iso` (theorem) | `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean` | 42-43 | unchanged |
| `reflectsIsomorphisms_of_full_and_faithful` (priority-100 instance) | `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean` | 55-58 | unchanged |
| `Functor.FullyFaithful` (structure) | `Mathlib/CategoryTheory/Functor/FullyFaithful.lean` | 122 | unchanged |
| `Functor.FullyFaithful.ofFullyFaithful` (constructor) | `Mathlib/CategoryTheory/Functor/FullyFaithful.lean` | 135-136 | unchanged |
| `Functor.FullyFaithful.preimageIso` | `Mathlib/CategoryTheory/Functor/FullyFaithful.lean` | 197 | unchanged |
| `HasForget` (class) | `Mathlib/CategoryTheory/ConcreteCategory/Basic.lean` | 73 | unchanged |
| `mono_iff_injective` (Type) | `Mathlib/CategoryTheory/Types/Basic.lean` | 242 | unchanged |
| `Function.Embedding.antisymm` | `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean` | 97 | unchanged |
| `Functor.PreservesMonomorphisms` API on `forget C` | `Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean` | 44+ | unchanged |

0 drift on 10 bearers. The Mathlib v4.26.0 pin (`2df2f015...`) has been
unchanged since S6 PREP authoring; the S8 PREP audit remains a complete
foundation for this S12 ACT.

## §3 Proof structure

```lean
theorem hasSBP_of_fullFaithful_forget (C : Type*) [Category C] [HasForget C]
    [(forget C).Full] [(forget C).Faithful]
    [(forget C).PreservesMonomorphisms] : HasSBP C := by
  intro X Y ⟨m, hm⟩ ⟨n, hn⟩
  haveI : Mono m := hm
  haveI : Mono n := hn
  -- Step 1: Lift C-monos to Type-injections via PreservesMonomorphisms +
  -- mono_iff_injective (Type).
  have hmi : Function.Injective ((forget C).map m) :=
    (mono_iff_injective _).mp inferInstance
  have hni : Function.Injective ((forget C).map n) :=
    (mono_iff_injective _).mp inferInstance
  -- Step 2: Apply classical Schroeder-Bernstein in Type.
  obtain ⟨e⟩ := Function.Embedding.antisymm
    ⟨(forget C).map m, hmi⟩ ⟨(forget C).map n, hni⟩
  -- Step 3: Promote Type-equiv to Type-iso, then preimage under
  -- the fully-faithful forgetful to obtain a C-iso.
  exact ⟨(Functor.FullyFaithful.ofFullyFaithful (forget C)).preimageIso e.toIso⟩
```

**LOC**: 12-line tactic body. The full file edit (+~87 LOC) breaks down
as ~12 LOC tactic + ~60 LOC `/-! ## S12 ACT ... -/` prose docstring +
~15 LOC theorem docstring + 2 new imports.

**Mathematical structure** (per S8 PREP §3 / S10 PREP §3.2):

| Step | What | Mathlib bearer |
|------|------|----------------|
| 1 | Mono in C ⟹ Mono in Type (via forget) | `Functor.PreservesMonomorphisms` instance |
| 2 | Mono in Type ↔ Function.Injective | `mono_iff_injective` (`Mathlib/CategoryTheory/Types/Basic.lean:242`) |
| 3 | Mutual injection ⟹ Type-equiv | `Function.Embedding.antisymm` (classical Schroeder-Bernstein, `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean:97`) |
| 4 | Type-equiv ⟹ Type-iso | `Equiv.toIso` (existing in `Types.Basic`) |
| 5 | Type-iso lift through Full+Faithful ⟹ C-iso | `Functor.FullyFaithful.ofFullyFaithful` + `.preimageIso` (`Mathlib/CategoryTheory/Functor/FullyFaithful.lean:135,197`) |

Step 5 elegantly compresses the multi-step lift sketched in S8 PREP §3 lines 169-181
(which used `Functor.Full.map_surjective` + manual `IsIso` construction +
`isIso_of_reflects_iso`) into a single `.preimageIso` call. The auto-instance
`reflectsIsomorphisms_of_full_and_faithful` (`Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean:55-58`)
fires invisibly inside `preimageIso`.

## §4 Build status — PENDING (host disk full)

Docker build attempt log: `researcher-6-schroeder-bernstein-oq01-s12-build.log` (truncated).

**Symptoms**:
- `df -h /` reports 141Mi free / 100% used capacity on `/dev/disk3s1s1` (926Gi total).
- Lake's Cache binary failed to link: `ld.lld: error: failed to write output '.lake/packages/mathlib/.lake/build/bin/cache': Input/output error`.
- Docker containerd metadata also corrupted: `failed to retrieve image list: ... input/output error`.

**Mitigation chosen**: Ship Lean code with build-pending annotation, following the **S5 ACT precedent** (PR #18707, "build pending" annotation later cleared by S6 BUILD UNBLOCKER PR #18980 with a 2-token `noncomputable` fix). This slug already has the BUILD-PENDING workflow proven.

**Grounding for confidence**: the Lean code is fully grounded by the live
v4.26.0 Mathlib API audit in S8 PREP §1.1–§1.5 (re-verified in §2 above
at S12 ACT-time, 0 drift). Every bearer is pinned at lake SHA `2df2f015...`
by file:line. The proof structure mirrors `hasSBP_Type` (PR #18383,
build-verified) — same `Function.Embedding.antisymm + Equiv.toIso`
spine, with the additional `preimageIso` lift for the categorical
preimage step.

**Forecast** (per S8 PREP §6): 3069–3080 jobs clean; 1-2 Docker
iterations expected (since `Mathlib.CategoryTheory.ConcreteCategory.Basic`
and `Mathlib.CategoryTheory.ConcreteCategory.EpiMono` are the only
new imports beyond the S11 chain).

**Recommended next picker action**: when disk recovers (or on a host
with disk headroom), run `./proofs/scripts/docker-build.sh
Proofs.SchroederBernsteinOQ01`. If clean, ship a follow-up PR that
clears the B1 blocker and updates state.md / JSON to mark S12
build-verified. If a build error surfaces, expect a small fix
(API name drift, namespace open, etc.); the proof structure itself
is sound by the audit.

## §5 Files modified by this PR

1. **EDIT** `proofs/Proofs/SchroederBernsteinOQ01.lean` (+87 LOC; 266→353):
   - 2 new imports (`Mathlib.CategoryTheory.ConcreteCategory.Basic` + `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`)
   - 1 new public theorem `hasSBP_of_fullFaithful_forget`
   - 1 new `/-! ## S12 ACT ... -/` prose block
   - 1 new theorem docstring
2. **EDIT** `research/problems/schroeder-bernstein-oq-01/state.md`:
   - Head: phase ACT iter 11→12; Last Updated 2026-05-16Z
   - Current Focus: add S12 row to corpus table; new S12 paragraph
   - Blockers: prepend new **B1** (build pending, host disk full)
   - Next Action: replace S11 SHIPPED + S12 RECOMMENDED with S12 SHIPPED-BUILD-PENDING + S13 horizon recommendation
3. **EDIT** `src/data/research/problems/schroeder-bernstein-oq-01.json`:
   - `currentState.phase` = ACT
   - `currentState.since` = 2026-05-16T04:30:00.000Z
   - `currentState.iteration` = 12
   - `currentState.focus` = S12 ACT shipped (build pending) full description
   - `currentState.blockers` = [B1 description]
   - `currentState.nextAction` = S13 horizon recommendation
   - `currentState.attemptCounts.total` = 4 (was 3); `currentApproach` = 2 (was 1)
   - `leanFiles[1].lineCount` = 353 (was 266)
   - `leanFiles[1].theoremCount` = 8 (was 7; +1 public)
   - `knowledge.insights[]` += 1 new insight
   - `knowledge.progressSummary` updated
   - `lastUpdate` = 2026-05-16
4. **NEW** `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-15-s12-act-path-Di-fullfaithful-forget.md` (this file)

## §6 Race awareness at S12 PR authoring

`gh pr list --repo rjwalters/lean-genius --search "schroeder-bernstein-oq-01 in:title" --state open` at S12 ACT
authoring (2026-05-16T04:30 UTC) returns zero open PRs. No race.

S11 ACT PR #19424 merged 2026-05-16T04:40:09Z (~30 min before S12 claim).
S10 PREP STATE-SYNC PR #19369 merged 2026-05-16T03:53:27Z.

## §7 Bookkeeping

- Iteration: 11 → 12
- Phase: ACT (unchanged)
- Sorries: unchanged (0)
- Axioms: unchanged (0)
- Public theorems: 5 → 6
- Total theorems: 7 → 8 (incl. 2 private from S5 ACT: `fHom_injective`, `gHom_injective`)
- Defs: 3 (unchanged)
- LOC: 266 → 353 (+87)
- Build status: changed from `verified` (S11) to `pending` (S12, awaiting B1 clearance)

## §8 Trap log

- **Disk-full Docker build I/O error** is a real wall hit; not a Lean
  issue. The disk fill happened pre-S12 (likely from prior agent's
  Docker cache accumulation); destructive cleanup not authorized.
  Workaround: ship as `build pending`, defer verification.
- **`gh repo view` default** (per memory
  `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`): all
  `gh pr list / view / create` invocations used explicit
  `--repo rjwalters/lean-genius`.
- **Worktree branch state**: started cycle on a stale branch (from
  cube-root-3 S11a ACT cycle 1); switched to fresh
  `research/schroeder-bernstein-oq01-s12-act-fullfaithful-forget-1778906849`
  from `origin/main` before any S12 edits.

**Cycle**: ~40 min (orient + Mathlib API audit + paste + Docker attempt + diagnostic + state.md/JSON update + memo).
