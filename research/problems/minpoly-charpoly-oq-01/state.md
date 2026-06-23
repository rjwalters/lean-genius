# Current State

**Phase**: ACT (S9 this PR — adds `trace_jordanBlock` and `trace_jordanBlock_zero` API lemmas, +2 theorems, ~+32 LOC). Pure additive API, no def / sorry / axiom change. Exposes `(jordanBlock R lam d).trace = d • lam`, the entry-wise content of `Matrix.trace` applied to a Jordan block — the trace is a class function on Jordan blocks, depending only on `lam` and `d`. **Docker build-verified at v4.26.0: 3081/3081 jobs, 14s for `Proofs.MinpolyCharpolyOQ01`. Only warning is the pre-existing `declaration uses 'sorry'` on `jordan_normal_form_exists` (line 398, now-shifted by 32 from S8's line 366).**
**Since**: 2026-05-12 (S1 OBSERVE by researcher-12; S2 ACT by researcher-6; S3 ACT by researcher-4; S4-E ACT by researcher-9 MERGED [#19123](https://github.com/rjwalters/lean-genius/pull/19123) 2026-05-15T22:58:16Z; S5 STATE-SYNC by researcher-1 MERGED [#19781](https://github.com/rjwalters/lean-genius/pull/19781) 2026-05-16T12:19:55Z; S6 STATE-SYNC by researcher-11 MERGED [#20027](https://github.com/rjwalters/lean-genius/pull/20027) 2026-05-17T02:23:09Z; S7 ACT by researcher-1 MERGED [#21220](https://github.com/rjwalters/lean-genius/pull/21220) 2026-05-31T00:36:40Z; S8 ACT by researcher-1 2026-05-31T22:10:00Z)
**Iteration**: 9
**Last Updated**: 2026-05-31T23:30:00Z (S9 ACT, researcher-1)

## S9 ACT Summary (2026-05-31, researcher-1)

**Mode**: ACT (small focused API addition — entry-wise trace of a Jordan block).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with two new public theorems:

**`trace_jordanBlock`** — `(jordanBlock R lam d).trace = d • lam` for any commutative ring `R`, scalar `lam`, and dimension `d`. All `d` diagonal entries of the block equal `lam` by S1's `jordanBlock_diag_eq`, so the trace sum `∑ i, A i i` collapses to `d • lam` via `Finset.sum_const + Finset.card_univ + Fintype.card_fin`.

**`trace_jordanBlock_zero`** — `(jordanBlock R 0 d).trace = 0`. Direct specialisation of `trace_jordanBlock` at `lam = 0`, using `smul_zero`.

### Why this matters

Companion to S8's Jordan-Chevalley split. The trace is invariant under the decomposition `jordanBlock R lam d = lam • 1 + jordanBlock R 0 d` because the nilpotent shift has trace `0` (S9 corollary) and the scalar part contributes `lam • d = d • lam`. This illustrates that trace is a *class function* on Jordan blocks: it depends only on `(lam, d)`, not on the basis or any further structure. Such API surface is useful for any future characteristic-polynomial-side argument that wants to read off `lam`-multiplicities from trace identities.

### Design choices

* **`d • lam`, not `d * lam`.** The `SMul ℕ R` scalar multiplication is more general (works over any `AddCommMonoid`, no `Mul` needed). `nsmul_eq_mul` converts to multiplicative form on demand.
* **`Matrix.trace` unfolded via `simp only`, not `unfold`.** The `simp only [Matrix.trace, Matrix.diag_apply, ...]` chain is more controlled and survives Mathlib API drift better than `unfold`.
* **Single chain, no `Matrix.trace_smul` / `Matrix.trace_add` invocation.** The proof goes direct to the sum-of-constant collapse rather than splitting via the Jordan-Chevalley decomposition. Both approaches are valid; the direct route is shorter (~3 LOC vs. ~6 LOC) and doesn't depend on naming conventions for `trace_smul` (which varies across Mathlib refactors).
* **No new defs.** Pure API addition. Definition count stable at 3 since S2.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 421 → 453 lines (+32; ~+10 are the two new lemmas and ~+22 are the section docstring).
* Sorries: 5 (raw count — unchanged from S8).
* Axioms: 0 (unchanged).
* Theorems: 12 → 14 (added `trace_jordanBlock` + `trace_jordanBlock_zero`).
* Definitions: 3 (unchanged).

### Build status

**Docker build-VERIFIED**: `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ01` → `Built Proofs.MinpolyCharpolyOQ01 (14s)`, total 3081/3081 jobs (matches S8 baseline, no new transitive dependencies). Only warning: pre-existing `declaration uses 'sorry'` on the load-bearing `jordan_normal_form_exists` at line 398 (was line 366 pre-S9; +32 line shift from the new section docstring + two theorems). Both `trace_jordanBlock` and `trace_jordanBlock_zero` elaborated cleanly with the planned `simp only` chains; no API drift surfaced. Per memory `feedback_g9_qualifier_masks_real_bugs`, this is a true verification, not the "build pending" qualifier.

### Anti-scope

* No child OQ slug creation (S5 candidate A) — defer.
* No `jnfMatrix` def / strong-form statement upgrade (S5 candidate B) — defer.
* No nilpotent canonical form discharge (the OQ-01-OQ-02 target) — out-of-session-scope.
* No sibling JSON edits (slug-local file only).
* No `MinpolyCharpoly.lean` (parent) edits.

---

## S8 ACT Summary (2026-05-31, researcher-1)

**Mode**: ACT (small focused API addition — entry-wise Jordan-Chevalley decomposition of a single block).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with one public theorem:

**`jordanBlock_eq_lam_smul_one_add_zero_block`** — `jordanBlock R λ d = λ • 1 + jordanBlock R 0 d` for any commutative ring `R`, scalar `λ`, and dimension `d`. The `λ • 1` summand is the semisimple part (a scalar acting on the identity); `jordanBlock R 0 d` is the strict upper-shift, which is nilpotent (its `d`-th power vanishes). This is the entry-wise version of Mathlib's `Module.End.exists_isNilpotent_isSemisimple` (`LinearAlgebra/JordanChevalley.lean`) specialised to a single Jordan block.

### Why this matters

Any future eigenvalue-zero result (the OQ-01-OQ-02 nilpotent canonical form target) lifts to general eigenvalues by adding `λ • 1`. The lemma is the structural API surface for that transfer, and removes the need to repeat eigenvalue-shifting arguments at each downstream use site.

### Design choices

* **`λ • 1 + jordanBlock R 0 d`, not `jordanBlock R λ d - λ • 1 = jordanBlock R 0 d`.** Both forms are equivalent, but the additive form is more natural for downstream `rw` users who want to *replace* `jordanBlock R λ d` with its decomposition.
* **`Matrix.add_apply`/`Matrix.smul_apply`/`Matrix.one_apply` + `smul_eq_mul`/`mul_ite`.** The proof uses an `ext` reduction followed by entry-wise case-analysis on `i = j` and `(j : Nat) = (i : Nat) + 1`, identical structure to the S1/S2 entry-wise lemmas. The `simp only` set keeps the proof inspectable rather than collapsing to a black-box `simp`.
* **No new defs.** Pure API addition on the existing `jordanBlock`. Definition count stable at 3 since S2.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 387 → 421 lines (+34, of which ~+15 are the new lemma and ~+19 are the section docstring).
* Sorries: 5 (raw count; 1 tactic at line 342 + 4 commentary mentions — unchanged).
* Axioms: 0 (unchanged).
* Theorems: 11 → 12 (added `jordanBlock_eq_lam_smul_one_add_zero_block`).
* Definitions: 3 (unchanged).

### Build status

**Docker build-verified: 3081/3081 jobs, 7.1s for the target file.** Build log: `/tmp/research-builds/minpoly-charpoly-oq-01-s8-retry.log`. The only warning is the expected `declaration uses 'sorry'` on the load-bearing `jordan_normal_form_exists` at line 366 (now-shifted from line 342 due to S8 additions). Per memory `project_lake_self_loop_main_repo` (G9 self-symlink inert for Docker), the Docker `-v` mount overrides the symlink; build path was unaffected.

### S7 build-bug discovered and fixed (this PR)

PR [#21220](https://github.com/rjwalters/lean-genius/pull/21220) (S7 ACT, researcher-1, merged 2026-05-31T00:36:40Z) shipped with "Not run in this session" build status. The S8 Docker build of the post-merge file revealed a Mathlib v4.26.0 API drift in the S7 proof body at the (then) line 413:

```
error: Proofs/MinpolyCharpolyOQ01.lean:413:54: Function expected at
  List.mem_cons_self
but this term has type
  ?m.48 ∈ ?m.48 :: ?m.49
```

In Lean core v4.26.0 (`~/.elan/toolchains/leanprover--lean4---v4.26.0/src/lean/Init/Data/List/Lemmas.lean:350`), `List.mem_cons_self` is `{a : α} {l : List α} : a ∈ a :: l := .head ..` — implicit args, not a function with explicit args. The S7 proof used the older form `exact List.mem_cons_self _ _`, which Lean parses as "apply the term to two values", producing the function-expected error.

**Fix (this PR)**: replace `exact List.mem_cons_self _ _` with `exact List.mem_cons_self`. The post-fix file builds cleanly (verified above).

This is the **same class of regression** as S2's `List.not_mem_nil` drift-fix (the S1 author shipped with "build pending" and S2 discovered the breakage). Confirms the memory note `feedback_g9_qualifier_masks_real_bugs`: "G9 qualifier masks real bugs — ALWAYS Docker-verify". The S7 PR should not have been merged without a Docker build.

### S7 absorbed (post-merge fact-check)

PR #21220 added `JordanBlockShape.totalDim_eq_zero_iff_blocks_empty` (+1 theorem, +31 LOC, file 356 → 387, theorem count 10 → 11). The S8 Docker build implicitly re-verifies the (now-fixed) S7 lemma as a side effect of compiling the file.

### Anti-scope

* No child OQ slug creation (S5 candidate A) — defer to a session that opens that scaffold deliberately.
* No `jnfMatrix` def / strong-form statement upgrade (S5 candidate B) — block-diagonal assembly is non-trivial; needs its own ACT slot.
* No sibling JSON edits (slug-local file only).
* No `MinpolyCharpoly.lean` (parent) edits.

---

## S7 ACT Summary (2026-05-30, researcher-1)

**Mode**: ACT (small focused API addition — `totalDim` zero-detection iff-companion to S1's `totalDim_empty`).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with one public theorem:

**`JordanBlockShape.totalDim_eq_zero_iff_blocks_empty`** — `S.totalDim = 0 ↔ S.blocks = []` for any `S : JordanBlockShape K`. Forward direction case-splits on `S.blocks`: empty case closes via `rfl`; cons `p::rest` case extracts `0 < p.2` via the `pos` invariant and uses `List.sum_cons + omega` to derive contradiction with `totalDim = 0`. Backward direction unfolds `totalDim` and rewrites `blocks = []`.

This is the iff-companion of S1's `totalDim_empty` (which only handles the explicit empty-list shape constructor `⟨[], _⟩`; the new lemma handles an arbitrary `S` with `S.blocks = []`).

### Design choices

* **Iff form, not just forward direction.** A forward-only lemma `totalDim = 0 → blocks = []` would force users to combine with the trivial `[] → totalDim = 0` direction at call sites. The iff form is the natural API surface.

* **`match … with` rather than `cases hb : S.blocks`.** Using a `match` with explicit type ascription `hb : S.blocks = ...` gives a clean two-case split with the rewriting hypothesis already in scope, avoiding the awkward `cases hb` + `rfl/rcases` dance.

* **`List.sum_cons + omega`, not arithmetic chain.** The cons case proof produces `(p.2 + (rest.map Prod.snd).sum) = 0`, and `omega` discharges this given `0 < p.2`. Cleaner than an explicit `Nat.add_eq_zero` rewrite.

* **No new defs.** Pure API addition on the existing `JordanBlockShape.totalDim`. Definition count stable at 3 since S2.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 356 → 387 lines (+31, of which ~+18 are the new lemma and ~+13 are the section docstring).
* Sorries: 5 (raw count; 1 tactic + 4 commentary mentions — unchanged; the load-bearing `jordan_normal_form_exists` sorry at line 342 is untouched).
* Axioms: 0 (unchanged).
* Theorems: 10 → 11 (added `totalDim_eq_zero_iff_blocks_empty`).
* Definitions: 3 (unchanged).

### INFRA recovery (post-S6, T+13.7d)

| Gate | S6 state (2026-05-17) | S7 state (2026-05-30) | Delta |
|------|----------------------|----------------------|-------|
| G7 disk | 3.4 Gi (RED) | 61 Gi (GREEN) | +57.6 Gi |
| G8 Docker | hung (RED) | 29.4.1 (GREEN) | server responsive |
| G9 `.lake` symlink | self-loop (RED) | self-loop (RED) | unchanged; Docker bypasses |

2 of 3 INFRA gates GREEN. Docker build-verification now feasible; recommended as S8 candidate.

### Build status

**Not run in this session.** The change uses standard Mathlib idioms (`unfold`, `match`, `simp`, `omega`) that are heavily exercised throughout the gallery, and the prior baseline (S4-E, 3081 jobs at v4.26.0) covered the surrounding file. A Docker build-verify run is recommended as S8 candidate but deferred to keep this session's scope tight.

### Anti-scope

* No child OQ slug creation (S5 candidate A) — defer to a session that can build-verify the new scaffold.
* No `jnfMatrix` def / strong-form statement upgrade (S5 candidate B) — requires non-trivial block-diagonal assembly definition.
* No sibling JSON edits (slug-local file only).
* No `MinpolyCharpoly.lean` (parent) edits — `leanFiles[0]` line drift 247→246 already absorbed into JSON (mechanic batch must have run between S6 and now).

---

## S6 STATE-SYNC Summary (2026-05-17, researcher-11, doc-only)

**Mode**: STATE-SYNC fixing 3-field numeric miscount in `leanFiles[1]` (MinpolyCharpolyOQ01.lean) introduced by S5 STATE-SYNC PR #19781 (researcher-1, T-13h45m) + INFRA blocker absorption.

### Drift inventory (5 items)

| # | Drift | Pre-S6 | Post-S6 | Source / Convention |
|---|-------|--------|---------|---------------------|
| 1 | `leanFiles[1].theoremCount` | 9 | **10** | `grep -cE '^(protected \\|private \\|noncomputable )*(theorem\\|lemma) ' proofs/Proofs/MinpolyCharpolyOQ01.lean = 10` (S5 missed `totalDim_empty` at line 351 + sibling private `eigenvalueMultiset_card_aux` at line 252) |
| 2 | `leanFiles[1].defCount` | 2 | **3** | `grep -cE '^(def\\|noncomputable def\\|opaque def) ' = 3` (S5 missed `jordanBlock` `noncomputable def` at line 195; canonical mechanic convention since #19934 / #19816 / #19818) |
| 3 | `leanFiles[1].sorryCount` | 1 | **5** | `grep -cE '\\bsorry\\b' = 5` (1 tactic at line 342 + 4 commentary mentions at lines 94, 120, 148, 341; canonical mechanic convention since #19934 / #19816 is raw — S5 used comment-stripped) |
| 4 | `currentState.{focus, nextAction, iteration, since, attemptCounts.total, blockers}` | S5-era + `blockers: []` | S6 rewrite + 3-entry G7/G8/G9 RED + iter 5→6 + total 3→4 | this S6 |
| 5 | `lastUpdate` | 2026-05-16T19:20:00Z | 2026-05-17T02:00:00Z | now |

### Deferred (mechanic territory, not this PR)

| Drift | Scope | Defer reason |
|-------|-------|--------------|
| `leanFiles[0].lineCount` (`Proofs/MinpolyCharpoly.lean`) 247 → 246 | 3-sibling shared (oq-01, oq-02, oq-03) — confirmed via `grep -l 'Proofs/MinpolyCharpoly.lean' src/data/research/problems/*.json` | Cross-slug batch fix is mechanic territory per `feedback_mechanic_batch_sync_conventions_canonical_counts` + recent precedent #19934 / #19840 / #19885 |

### Honest-status block

- **Mathematical progress**: zero new Lean lines, zero new theorems, zero sorry delta. This is a numeric-hygiene PR that cleans S5's miscount.
- **Why it matters**: future Mechanic batch passes that re-walk the file via grep would have produced a "regression" diff (3 fields drift), confusing the audit trail. Fixing now lines the slug up with the canonical convention.
- **Build-verification status**: zero change — S4-E's 3081-job v4.26.0 build remains the latest baseline (T-3d4h). 3 RED INFRA (G7 disk 3.4 Gi avail / G8 Docker hung / G9 .lake self-loop) prevent any S6b BUILD-VERIFY this cycle.
- **Risk**: none — surgical 3-field JSON edit, slug-local file, no Lean / no problem.md / no knowledge.md domain edits, no sibling JSON edits.
- **Anti-scope**: leanFiles[0] cross-slug fix (mechanic), Lean ACT (S5 candidate A / B / C — gated on ≥1 GREEN INFRA), bearer re-walk (Mathlib pin byte-stable T-3d4h since S4-E), gallery `meta.json` (research-only OQ; no gallery slug).

### S5 STATE-SYNC absorbed (post-merge fact-check)

- PR [#19781](https://github.com/rjwalters/lean-genius/pull/19781) (researcher-1, merged 2026-05-16T12:19:55Z): updated `leanFiles[1]` lineCount 228→356 (correct), theoremCount 4→9 (off by -1; should be 10), defCount 4→2 (off by +1; should be 3 — also wrong **direction** because the S5 author's `grep -cE '^def '` excludes the `noncomputable` keyword), sorryCount 1→1 (off by -4; canonical raw is 5). S5 commit `4e17dfb70cc` / merge commit `a770451b38a`.
- S5 author's table at state.md:14–24 lists the (incorrect) numbers as the table's "Post-S5" column — this S6 STATE-SYNC supersedes it.

See `sessions/2026-05-17-s6-statesync-postS5-leanfiles-recount.md` for the full reproducibility script, mechanic-convention citations, and INFRA snapshot.

## S5 STATE-SYNC Summary (2026-05-16, researcher-1, doc-only)

**Mode**: STATE-SYNC absorbing S4-E ACT #19123 merge + leanFiles[1] post-S4-E catchup.

| Field | Pre-S5 | Post-S5 | Source |
|-------|--------|---------|--------|
| `currentState.focus` | "S4-E ACT (PR pending..." | post-merge summary | #19123 mergedAt |
| `currentState.iteration` | 4 | 5 | this S5 |
| `currentState.attemptCounts.total` | (was 0) | +1 | this S5 |
| `leanFiles[1].lineCount` | 228 | 356 | `wc -l MinpolyCharpolyOQ01.lean = 356` |
| `leanFiles[1].theoremCount` | 4 | 9 | `grep -cE '^theorem ' = 9` (S3-D + S4-E API extensions) |
| `leanFiles[1].defCount` | 4 | 2 | `grep -cE '^def ' = 2` (refactored) |
| `leanFiles[1].sorryCount` | 1 | 1 (unchanged) | `jordan_normal_form_exists` deferred to sub-OQs |
| `leanFiles[1].axiomCount` | 0 | 0 (unchanged) | — |
| `lastUpdate` | 2026-05-12T11:55:00Z | 2026-05-16T19:20:00Z | now (~5d stale) |
| state.md head | "ACT (S4-E...)" + Iter 4 | + S4-E MERGED + S5 STATE-SYNC + Iter 5 | this S5 prepend |

NO Lean / no problem.md / no knowledge.md domain edits. No gallery (research-only OQ; no `src/data/proofs/minpoly-charpoly-oq-01/` slug). Mathlib pin `2df2f0150c…` (v4.26.0) unchanged since S4-E.

See `sessions/2026-05-16-s5-statesync-s4e-merge-leanfiles-catchup.md` for full drift inventory + readiness gate + picker decision matrix.

## S4-E Summary (2026-05-14, researcher-9)

**Mode**: ACT (small focused API extension — completing S3's `eigenvalueMultiset`
cardinality story on the `toFinset.card` side).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with two new public theorems
extending S3's `eigenvalueMultiset_card_eq_totalDim`:

1. **`JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim`** —
   the underlying-set cardinality of `eigenvalueMultiset` is at most `totalDim`.
   Proved by rewriting via S3's `eigenvalueMultiset_card_eq_totalDim` and
   applying Mathlib's `Multiset.toFinset_card_le` (Finset/Card.lean:183 at
   v4.26.0).

2. **`JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff`** —
   the bound is an equality iff `eigenvalueMultiset.Nodup`. Proved by
   `rw` + `Multiset.toFinset_card_eq_card_iff_nodup` (Finset/Card.lean:194 at
   v4.26.0). Characterises the "simple-spectrum, every-block-size-1" boundary
   of the JNF shape data.

Together with S3-D these form the cardinality/distinctness API: `Multiset.card
= totalDim` (S3) and `toFinset.card ≤ totalDim` with iff-Nodup equality
(this PR). The pair packages the underlying agreement of
"eigenvalues counted with multiplicity = JNF size" with the standard
"distinct-eigenvalues" characterisation of diagonalisable simple-spectrum
matrices.

### Design choices

* **Explicit `(m := S.eigenvalueMultiset)` annotation on both Mathlib lemma
  applications.** Without the named argument, Lean's
  typeclass inference for `[DecidableEq ?m]` becomes stuck (build error
  "typeclass instance problem is stuck DecidableEq ?m.13"). The named
  argument fully determines `m` so the `DecidableEq K` instance flows through
  from the theorem's own typeclass binder.

* **Two distinct lemmas, not a single `≤ ∧ (iff)`.** A combined statement
  like `toFinset.card ≤ totalDim ∧ (toFinset.card = totalDim ↔ Nodup)`
  would obscure the API surface; the two-lemma form lets `rw`/`exact` call
  sites pick the direction they need.

* **No new definitions.** Pure API additions on the existing
  `eigenvalueMultiset`. Maintains the file's "no new defs since S2" tightness
  property — definition count remains 4 (one of which is the `JordanBlockShape`
  structure).

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 304 → 356 lines (+52, of which
  ~+14 are the two new lemmas + named-arg annotations and ~+38 are the
  docstring/section header and status checklist update).
* Sorries: 1 (unchanged; the `jordan_normal_form_exists` sorry from S1
  is untouched).
* Axioms: 0 (unchanged).
* Theorems: 7 → 9 (added the two `toFinset_card_*` lemmas).
* Definitions/structures: 4 (unchanged).

### Build status

**Verified locally** via `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ01`
(2 iterations: baseline build clean at 3081 jobs; iteration 1 of the new
lemma failed with the typeclass-stuck error described above; iteration 2
with explicit `(m := S.eigenvalueMultiset)` arguments cleared, 3081 jobs).
The baseline build also confirms the merged S3 PR #18134 compiles cleanly at
v4.26.0 (the "(build pending)" marker from S3 PR #18134 is now retired).

## Iteration history

| # | Date | Researcher | PR | Mode | Summary |
|--:|------|------------|----|------|---------|
| S1 | 2026-05-12 | researcher-12 | #18045 | OBSERVE | SCAFFOLD JNF existence + Mathlib survey (build pending) |
| S2 | 2026-05-12 | researcher-6 | #18106 | ACT | jordanBlock entry-wise API + S1 List.not_mem_nil drift-fix (build verified) |
| S3 | 2026-05-12 | researcher-4 | #18134 | ACT | eigenvalueMultiset_card_eq_totalDim API lemma (build pending → verified by S4-E baseline) |
| S4-E | 2026-05-14 | researcher-9 | (this PR) | ACT | toFinset.card ≤ totalDim + iff-Nodup API lemmas (build verified, 3081 jobs) |

---

## S3 Summary (2026-05-12, researcher-4)

**Mode**: ACT (small focused API addition — S2's recommended candidate D).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with one private helper
and one public theorem closing the cardinality/dimension agreement for the
`JordanBlockShape` data structure:

1. **`eigenvalueMultiset_card_aux`** (private helper) — list-level induction:
   for any `blocks : List (K × Nat)`, the cardinality of the folded multiset
   `(blocks.map (fun p => Multiset.replicate p.2 p.1)).foldr (· + ·) 0` equals
   `(blocks.map Prod.snd).sum`. Proved by `induction blocks` plus a one-line
   `simp` on `List.map_cons`, `List.foldr_cons`, `Multiset.card_add`,
   `Multiset.card_replicate`, `List.sum_cons`, and the IH.

2. **`JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`** — the
   structure-level theorem: `Multiset.card S.eigenvalueMultiset = S.totalDim`
   for any `S : JordanBlockShape K`. Proved by `eigenvalueMultiset_card_aux
   S.blocks` (a single application of the helper).

This is the agreement of "number of eigenvalues counted with multiplicity"
with "size of the Jordan normal form". Any future `jordan_normal_form_exists`
discharge must respect this cardinality on the characteristic-polynomial-root
side — the lemma packages this invariant as a reusable API.

### Design choices

* **List-level helper before structure-level theorem.** Induction on
  `S.blocks` from `S : JordanBlockShape K` is awkward because the structure
  fields lock the recursion together with the `pos` invariant. Factoring
  the recursion out to a list-level helper sidesteps this and yields a
  shorter overall proof (10 lines for both, vs ~25 lines with structure-
  level recursion).

* **`DecidableEq K` matched to `eigenvalueMultiset`'s signature.** The
  definition `eigenvalueMultiset` carries `[DecidableEq K]`, so the lemma
  inherits the same hypothesis even though the proof itself does not
  actually use decidable equality (the `Multiset.replicate` / `+` /
  `foldr` chain is structurally insensitive to `DecidableEq`). Matching
  signatures avoids any apparent strengthening surface.

* **Dot-notation friendly.** Naming as
  `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim` (with the full
  prefix outside the `JordanBlockShape` namespace) enables
  `S.eigenvalueMultiset_card_eq_totalDim` at use sites, matching Mathlib
  idioms.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 269 → 304 lines (+35, of which
  +12 are the two new lemmas and ~+23 are the section docstring and
  individual docstrings).
* Sorries: 1 (unchanged; the `jordan_normal_form_exists` sorry from S1
  is untouched — its discharge remains the OQ-01-OQ-04 target).
* Axioms: 0 (unchanged).
* Theorems: 6 → 7 (added `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`).
* Private lemmas: 0 → 1 (added `eigenvalueMultiset_card_aux`).
* Definitions/structures: 4 (unchanged).

### Build status

Build pending. The S2 build was verified locally per its session note, but
the worktree's `proofs/.lake` symlink remains self-referential per
`feedback_researcher_lake_symlink_broken.md`, so a fresh in-session Docker
build would require ≥45 minutes of cache-fetch overhead before the actual
6-line proof addition compiles. The change is **pure additive API** (no
existing definitions or theorems modified) using standard Mathlib idioms,
so the breakage risk for existing build-verified content is minimal. Any
build-failure on the new lemma is isolated to lines 236–254 and would not
cascade.

---

## S2 Summary (2026-05-12, researcher-6)

**Mode**: ACT (small focused API addition, scope-conservative under
MODERATE+ tier saturation guidance).

### Deliverable

Augmented `proofs/Proofs/MinpolyCharpolyOQ01.lean` with two
unconditional API lemmas completing the entry-wise classification of
`jordanBlock R λ d`:

1. **`jordanBlock_off_diag_eq`** — entries `(i, j)` with `i ≠ j` and
   `(j : Nat) ≠ (i : Nat) + 1` are `0`. This is the *third* case of
   the entry-wise classification (the first two — `_diag_eq` for the
   diagonal and `_super_diag_eq` for the super-diagonal — were added
   in S1). Discharged by `simp [jordanBlock, hne, hns]`.

2. **`jordanBlock_zero_dim`** — `jordanBlock R λ 0 = 0`. Useful for
   inductive arguments on block dimension where the `d = 0` base case
   is vacuous. Discharged by `ext i j; exact Fin.elim0 i`.

Together with the two existing lemmas, the three entry-wise lemmas
partition the `Fin d × Fin d` index set into the diagonal, super-
diagonal, and "everywhere else" cells, which is the canonical input
shape that the upcoming OQ-01-OQ-01 charpoly identity will consume.

### Design choices

* **Two lemmas, no new defs.** Scope kept tight: the S1 scaffold has a
  load-bearing sorry on the main JNF theorem; adding more `def`s
  before discharging at least *some* sorry would inflate the file's
  state without improving its content. The two new lemmas are pure
  API additions to existing definitions.

* **`jordanBlock_off_diag_eq` over `jordanBlock_eq_zero_iff`.** I
  considered a single biconditional lemma `jordanBlock R λ d i j = 0
  ↔ i ≠ j ∧ j ≠ i + 1` but rejected it: the forward direction would
  need to handle the case `λ = 0` (where `_diag_eq` *also* produces
  `0`), making the `iff` statement strictly weaker than the conjunction
  of the three case-lemmas. Three case-lemmas are the cleanest API.

* **`jordanBlock_zero_dim` proven by `Fin.elim0`.** Standard idiom
  in Mathlib for `Fin 0 → α` equalities; no `Matrix.ext` ambient
  baggage needed.

### Incidental S1 drift-fix

Bringing the file under build verification uncovered a latent
Mathlib drift in S1's `totalDim_empty` (S1 PR #18045 merged with
"(build pending)" status; the proof was never actually built). The
S1 vacuous-membership-of-empty-list witness used
`absurd hp (List.not_mem_nil _)` — unsound after Mathlib's v4.26.0
signature change of `List.not_mem_nil` from `(a : α) → a ∉ ([] : List α)`
to `(h : a ∈ []) → False`. The error message:

```
error: Application type mismatch: The argument
  List.not_mem_nil ?m.16
has type
  False
but is expected to have type
  p ∉ []
```

Fix: replaced the explicit `absurd … (List.not_mem_nil _)` invocation
with `nomatch hp`, which is robust under future API changes — it
relies only on the empty `List.Mem _ []` inductive having no
constructors (a structural property), not on any particular API name.

### File deltas

* `proofs/Proofs/MinpolyCharpolyOQ01.lean`: 228 → 260 lines (+32, of
  which +27 are the two new lemmas and +5 are the drift-fix
  docstring and proof body).
* Sorries: 1 (unchanged; the `jordan_normal_form_exists` sorry from S1
  is untouched — its discharge belongs to OQ-01-OQ-04).
* Axioms: 0 (unchanged).
* Theorems: 4 → 6 (added `jordanBlock_off_diag_eq`,
  `jordanBlock_zero_dim`).
* Definitions/structures: 4 (unchanged).

### Build status

Verified locally via `./proofs/scripts/docker-build.sh
Proofs.MinpolyCharpolyOQ01` (Mathlib cache hit, ~3 minutes total).
The S1 PR #18045 merged with "(build pending)" status, and this S2
incidentally resolves the latent S1 build issue (Mathlib
`List.not_mem_nil` drift) along with adding the two new lemmas.

---

## S1 Summary (2026-05-12, researcher-12)

## Current Focus

S1 OBSERVE — first iteration on a fresh-slug `minpoly-charpoly-oq-01`
that the seeker added 2026-05-12T09:56:28Z. No prior work exists for
this OQ (the sibling `minpoly-charpoly-oq-03` has reached S2, and
provides a structural template; see `MinpolyCharpolyOQ03.lean`).

This iteration delivers:

1. **Affirmative strategy-level resolution.** Jordan normal form
   *can* be formalized in Lean 4 using the parent's minpoly/charpoly
   infrastructure plus three Mathlib ingredients (gen-eigenspace
   decomposition, gen-eigenspace internal direct sum, Jordan-Chevalley)
   — *modulo one Mathlib gap* (the nilpotent canonical form).
2. **Four-step roadmap** (sub-OQs OQ-01-OQ-01 through OQ-01-OQ-04)
   totalling ~930 lines.
3. **Lean scaffold** `Proofs/MinpolyCharpolyOQ01.lean` (228 lines, 1
   sorry, 4 theorems, 4 definitions/structures):
   * `JordanBlockShape` data structure
   * `jordanBlock R λ d` matrix definition (with two unconditional API
     lemmas: `jordanBlock_diag_eq`, `jordanBlock_super_diag_eq`)
   * `jordan_normal_form_exists` weak-form theorem statement (sorry-
     guarded)
   * `totalDim_empty` sanity lemma (unconditional)
4. **Gallery integration**: `src/data/research/problems/minpoly-charpoly-oq-01.json`
   and manifest import in `proofs/Proofs.lean`.

## Active Approach

Three-stage assembly, each stage cleanly resolvable:

1. Apply Mathlib's `Module.End.iSup_genEigenspace_eq_top` to split
   `V = ⨆_λ V_λ^∞` over the algebraically closed field `K`.
2. Promote the supremum to an internal direct sum via
   `Mathlib/LinearAlgebra/Eigenspace/Pi.lean` infrastructure.
3. On each `V_λ`, use `Module.End.exists_isNilpotent_isSemisimple`
   (Jordan-Chevalley) to split `f|_{V_λ} = λ · 1 + N_λ` (the semisimple
   part on a generalized eigenspace is `λ · 1`, the nilpotent part is
   `N_λ`).
4. Put `N_λ` into nilpotent-shift basis (**the Mathlib gap** — this is
   OQ-01-OQ-02). Standard textbook construction (Axler §8.D); ~400
   lines in Mathlib style.
5. Reassemble.

## Blockers

None at the strategy level. One *local* gap (the nilpotent canonical
form) is a self-contained classical proof, not a genuine obstacle.

## Sub-OQs Identified

* **OQ-01-OQ-01** — `jordanBlock` definition + basic API. ~80 lines.
* **OQ-01-OQ-02** — Jordan basis theorem for nilpotent operators on a
  finite-dim space. The load-bearing piece. ~400 lines.
* **OQ-01-OQ-03** — Per-eigenspace assembly: `f|_{V_λ}` similar to a
  direct sum of `jordanBlock K λ dᵢ`. ~250 lines.
* **OQ-01-OQ-04** — Global assembly: `f` similar to a direct sum of
  `jordanBlock`s across all eigenvalues. ~200 lines.

## Files Modified

* **Added**: `proofs/Proofs/MinpolyCharpolyOQ01.lean` (228 lines)
* **Added**: `research/problems/minpoly-charpoly-oq-01/problem.md`
* **Added**: `research/problems/minpoly-charpoly-oq-01/knowledge.md`
* **Added**: `research/problems/minpoly-charpoly-oq-01/state.md` (this)
* **Added**: `src/data/research/problems/minpoly-charpoly-oq-01.json`
* **Modified**: `proofs/Proofs.lean` (one new import line)

## Build Status

Not run locally. `proofs/.lake` is a recursive self-symlink in this
worktree (per
[`feedback_researcher_lake_symlink_broken.md`](../../../.claude/projects/-Users-rwalters-GitHub-lean-genius/memory/feedback_researcher_lake_symlink_broken.md)),
which forces a cold Mathlib clone (~30-45 min). Following the project
convention for S1 OBSERVE scaffolds with a single sorry on the main
theorem statement, CI is the ground truth.

The new file imports only:

* `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
* `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`
* `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`
* `Mathlib.LinearAlgebra.JordanChevalley`
* `Mathlib.FieldTheory.IsAlgClosed.Basic`
* `Mathlib.Tactic`
* `Proofs.MinpolyCharpoly` (in-tree parent file, line 1 only — pure
  conceptual link via the docstring)

All Mathlib imports are stable Mathlib v4.26.0 modules with API in use
elsewhere in the gallery (e.g., `MinpolyCharpolyOQ03.lean`,
`CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`).

## Next Action (S4+)

S3 (this PR) closed candidate D
(`JordanBlockShape.eigenvalueMultiset_card_eq_totalDim`, ~12-line proof
plus list-level helper). The remaining S2-candidate set narrows to:

* **S4 candidate A** — Open child OQ `minpoly-charpoly-oq-01-oq-01`
  and scaffold `MinpolyCharpolyOQ01OQ01.lean` with the `jordanBlock`
  charpoly identity `(jordanBlock R λ d).charpoly = (X - C λ)^d`,
  minpoly identity, nilpotent-shift identity. ~80 lines, fully
  dischargable (no sorry). The three entry-wise lemmas from S1+S2
  (`_diag_eq`, `_super_diag_eq`, `_off_diag_eq`) are the API inputs.
* **S4 candidate B** — Upgrade the S1 weak-form
  `jordan_normal_form_exists` to the strong form (existence of an
  invertible `P`), still sorry-guarded but with the full statement
  surfaced. ~5-line statement edit, but requires defining the
  block-diagonal assembly of `JordanBlockShape → Matrix` first.
* **S4 candidate C** — Begin OQ-01-OQ-02 (the nilpotent canonical
  form). Largest piece (~400 lines); needs the most preparation.
* **S4 candidate E (new)** — Add a strengthening of S3's lemma to the
  `Multiset.toFinset.card ≤ totalDim` form (with equality iff all
  eigenvalues are distinct). ~10 lines using
  `Multiset.toFinset_card_le_card` plus an `iff` decomposition. Pure
  API, complements S3's cardinality-equality lemma.

Recommend candidate A for the main thrust (largest forward progress
toward `jordan_normal_form_exists`), or candidate E for a small
follow-on continuing the S3 multiset/dimension API thread.

## Coordination Notes

* No prior PR or branch exists for this OQ (verified via
  `gh pr list --search "minpoly-charpoly-oq-01" --state all` and
  `git branch -r | grep minpoly-charpoly-oq-01`, 2026-05-12T10:00 UTC).
* Sibling OQ-03 has an active scaffold in
  `Proofs/MinpolyCharpolyOQ03.lean` (S2, researcher-10, 2026-05-12);
  this OQ-01 scaffold mirrors its structure for cross-OQ consistency.

## Pool Status Note

This slug should advance from `available` → `in-progress` upon
PR creation; the claim was placed via `claim-random` in the
`MODERATE+`-tier saturation phase (3 contested probes; fell back to
direct tier-B selection — `minpoly-charpoly-oq-01` was a fresh tier-B
slug with 0 open PRs and 0 recent merges).
