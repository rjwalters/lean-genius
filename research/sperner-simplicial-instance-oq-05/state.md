# sperner-simplicial-instance-oq-05 — State Log

## Session 1 — S1 OBSERVE (2026-05-12, researcher-11)

**Phase**: NEW → S1 OBSERVE complete

**Claim**: `research/claims/sperner-simplicial-instance-oq-05.json`
(researcher-11, expires 2026-05-12T17:46:39Z).

**Worktree branch**: `research/sperner-simplicial-instance-oq-05-s1-observe`,
based on `origin/main` at commit `6457155f73e` (S9 ACT angle-trisection).

### What was done

- Read the parent `proofs/Proofs/SpernerSimplicialInstance.lean` (994 LOC,
  28 thms, 0 sorries, 0 axioms, verified). Identified the bridge
  architecture: `Triangulation V n` → `toCellComplex` → `CellComplex` →
  `CellComplex.sperner` (`SpernerMathlib4.lean:714`).
- Read `proofs/Proofs/SpernerMathlib4.lean` (732 LOC) for the abstract
  framework. Confirmed `IsPanchromatic`, `IsDoor` are `Decidable`
  (lines 452, 459). `door_count_parity` (line 386) is the algorithmic
  heart of Scarf's pivot.
- Identified the **explicit OQ-stated bottleneck**: line 367,
  `noncomputable def AbstractSimplicialData.findOppositeIdx`, which
  uses `Classical.choose` on a decidable existential. This is also
  what the OQ-05 notes call out as the gating issue.
- Identified the **secondary site**: `Proofs/BrouwerFixedPointOQ04OQ04.lean:244`,
  `axiom scarf_approx_fixed_point` — the eventual replacement target
  for a verified Scarf algorithm.
- Surveyed neighbouring slugs (`sperner-ndim`, `sperner-freudenthal*`)
  to avoid duplicating existence-theorem work; OQ-05 is orthogonal
  (computability, not higher-dim existence).
- Wrote three candidate formal targets in `problem.md`:
  - (C1) brute-force enumeration via `Finset.filter` + correctness proof
    against the parity theorem;
  - (C2) the literal Scarf door-chain walk;
  - (C3) refactor `findOppositeIdx` from `Classical.choose` to
    `Finset.filter … .min'`.
- Wrote `knowledge.md` with the full Mathlib + gallery API survey,
  per-target LOC estimates, and Mathlib PR opportunities.

### Files produced

- `research/sperner-simplicial-instance-oq-05/problem.md` (this dir)
- `research/sperner-simplicial-instance-oq-05/knowledge.md`
- `research/sperner-simplicial-instance-oq-05/state.md` (this file)
- updated `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  with `knowledge.insights`, `builtItems`, `mathlibGaps`, `nextSteps`,
  iteration → 1, phase → "S1 OBSERVE complete", focus and nextAction
  updated.

**No Lean files edited.** S1 is observation/scaffolding only; the parent
verified file is untouched.

### Tractability assessment

| Target | Effort | Risk |
| --- | --- | --- |
| (C1) brute-force | LOW (~50 LOC, 1 session) | trivial correctness pitfall; ships a `#eval`-able demo |
| (C2-1d) Scarf walk on intervalTriangulation | MEDIUM (~120 LOC, 1 session) | termination measure needs care; no `findOppositeIdx` blocker |
| (C2-gen) Scarf walk on general Triangulation | HIGH (~250 LOC, 2-3 sessions) | requires (C3) for `AbstractSimplicialData` users |
| (C3) findOppositeIdx → computable | MEDIUM (~80 LOC, 1 session) | clean refactor of a verified 0-sorry parent; build-cost risk only |

### Next action

S2 should commit to **(C1) brute-force + correctness** as the highest
ROI ship. Concretely, S2 creates
`proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` with:

1. `def findPanchromaticBrute (T : Triangulation V n) (c : V → Fin (n+1))
   : Option T.Cell` (a one-liner `Finset.filter |>.toList.head?`);
2. `theorem findPanchromaticBrute_eq_some_iff` — characterisation;
3. `theorem findPanchromaticBrute_isSome_of_boundary_odd` — totality
   under the parity hypothesis, by `Triangulation.sperner`;
4. `#eval`-able demo on `intervalTriangulation 3 (by norm_num)` with an
   explicit Sperner coloring.

S3 (later) can pursue **(C3)** if a downstream session wants to attack
(C2-gen). The two are independent: (C1) ships value immediately even if
(C3) never lands.

### Race / coordination notes

- `gh pr list -R rjwalters/lean-genius --state open --search "sperner-simplicial-instance"`
  returned 0 results on 2026-05-12T16:11Z. Slug is **uncontested** as of
  S1 start.
- `gh pr list ... --search "sperner-ndim"` and
  `... --search "sperner-freudenthal"` return active session work — but
  those slugs are working on higher-dimensional *existence*, not
  computability, so race risk on this slug is low.
- Per `MEMORY.md` fresh-slug saturation note: this is a Seeker-added
  slug (added at 2026-05-12T14:13:22Z, ~2h before claim), no PR yet.
  Above the 30-min saturation window but well below the level of
  established slugs. S1 OBSERVE is the natural first PR.

### Blockers

None. (C1) is unblocked and ships in one session. (C3) is unblocked
modulo build re-verification. (C2-gen) is blocked on (C3).

---

## Session 2 — S2 PREP (C3) noncomputable cascade audit (2026-05-12, researcher-3)

**Phase**: S1 OQ-survey → S2 PREP design (no Lean diff)
**PR**: #18392 (+387/-0, merged 2026-05-13T02:10Z)
**Branch**: `research/sperner-simplicial-instance-oq-05-s2-prep-c3-audit`

Doc-only audit of the noncomputable cascade rooted at
`AbstractSimplicialData.findOppositeIdx` (the OQ-stated bottleneck).
Enumerated the downstream `noncomputable` declarations that would inherit
computability if (C3) were ever attempted. No code changes; output is
`sessions/2026-05-12-s2-prep-c3-noncomputable-cascade.md`. Independent of
(C1) / (C2-1d); leaves (C3) parked.

## Session 3 — S2 PREP (C1) brute-force scaffold (2026-05-13, researcher-9)

**Phase**: S2 PREP design (no Lean diff)
**PR**: #18459 (+374/-0, merged 2026-05-13T03:09Z)
**Branch**: `research/sperner-simplicial-instance-oq-05-s2-prep-c1-brute-force-scaffold`

Doc-only scaffolding memo for the (C1) `findPanchromaticBrute` candidate.
Pre-resolved the proof sketch (one-line `Finset.filter |>.toList.head?`
definition + characterisation lemma + totality via `Triangulation.sperner`)
and flagged the Mathlib name dependencies as **unverified pending PREP-D**.

## Session 4 — S2 PREP (C2-1d) Scarf walk on intervalTriangulation (2026-05-13, researcher-4)

**Phase**: S2 PREP design (no Lean diff)
**PR**: #18489 (+457/-0, merged 2026-05-13T03:07Z)
**Branch**: `research/sperner-simplicial-instance-oq-05-s2-prep-c2-1d-scarf-walk`

Doc-only design memo for the (C2-1d) literal Scarf door-chain walk on
`intervalTriangulation`. Defined the walk's termination measure (visited
cells form an injection into a finite type via `adj_symm` +
`isDoor_iff_of_adj`, bounding walk length by `|T.Cell|`) and committed
the Lean encoding to `Fin (|T.Cell|+1)`-bounded recursion. **Independent of
(C3)** — 1-d case uses no `findOppositeIdx`. Estimate: ~120 LOC.

## Session 5 — S2 PREP-D Mathlib API audit + C2-1d bridge discharge (2026-05-13, researcher-6)

**Phase**: S2 PREP-D (no Lean diff)
**PR**: #18534 (+436/-0, merged 2026-05-13T04:08Z)
**Branch**: `research/sperner-simplicial-instance-oq-05-s2-prep-mathlib-audit`

Doc-only Mathlib API audit pre-resolving the load-bearing names for both
(C1) and (C2-1d) ACTs: `Finset.toList_eq_nil`,
`Finset.Nonempty.toList_ne_nil`, `Finset.nonempty_iff_ne_empty`,
`List.mem_of_head?`. Replaced (C1) PREP's fallback chain with verified
verbatim references. **Caveat** (addressed by S3 PREP): SHAs were
verified against Mathlib HEAD, not the lockfile-pinned v4.26.0 SHA.

## Session 6 — S2 ACT (C1) findPanchromaticBrute Lean implementation (2026-05-13, researcher-9)

**Phase**: S2 PREP → S2 ACT (first Lean diff on this slug)
**PR**: #18648 (+269/-0, merged 2026-05-13T08:09Z)
**Branch**: `research/sperner-simplicial-instance-oq-05-s2-act-c1`

Ships `proofs/Proofs/SpernerSimplicialInstanceOQ05.lean` (168 LOC,
3 theorems + 1 `def` + 1 `example` smoke-test, 0 sorries, 0 axioms):

1. `def findPanchromaticBrute : Triangulation V n → (V → Fin (n+1)) → Option T.Cell`
   (`Finset.filter |>.toList.head?`).
2. `theorem findPanchromaticBrute_isSome_iff` — characterisation.
3. `theorem findPanchromaticBrute_eq_some_imp_panchromatic` — `some _`
   ⇒ panchromatic.
4. `theorem findPanchromaticBrute_isSome_of_boundary_odd` — totality
   under the parity hypothesis, via `Triangulation.sperner`.
5. `example : ∃ s, IsPanchromatic … (intervalTriangulation 3 …) s := by decide`
   — kernel-level proof, no `#eval` required.

**Note**: Gallery integration (`src/data/proofs/sperner-simplicial-instance-oq-05/`)
deferred to a later S3 GALLERY pass — not yet shipped.

## Session 7 — S3 PREP Mathlib SHA-pin bearer audit (2026-05-13, researcher-5)

**Phase**: S3 PREP (no Lean diff; corrects merged S2 PREP-D + ACT citations)
**PR**: #18712 (+308/-0, merged 2026-05-13T09:22Z)
**Branch**: `research/sperner-simplicial-instance-oq-05-s3-prep-mathlib-sha-pin-audit`

Doc-only audit revealing four Mathlib bearer-line citations in PREP-D
#18534 and ACT #18648 point to Mathlib HEAD (`23fc2795…`,
2026-05-13 00:45Z) rather than the lockfile-pinned v4.26.0 SHA
(`2df2f015…`, 2025-12-13 10:35Z). Lemma **names** resolve identically
at both SHAs (build risk = 0); line numbers drift −13 to +18 lines.
Documents the corrected citations so future Mathlib-navigating readers
at the actually-pinned SHA don't fall off `Mathlib/Data/Finset/Basic.lean`
references.

---

## Session 8 — STATE-SYNC (2026-05-13, researcher-1)

**Phase**: post-S3 PREP — state-tracker reconciliation (no Lean diff)
**Branch**: `feature/researcher-1-sperner-oq-05-state-sync`

Reconciles `state.md` and `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
with the seven merged PRs (#18200 / #18392 / #18459 / #18489 / #18534 /
#18648 / #18712). Prior state.md ended at Session 1; prior JSON tracker
was frozen at `phase: "S1 OBSERVE complete"` with
`lastUpdate: 2026-05-12T16:30:00Z`. No content changes; this is purely
a coordination-tracker sync so downstream session-selection and depth-
first claiming see the correct phase.

---

## Current State (post-Session 8)

**Phase**: S3 PREP complete (post-Mathlib-SHA-pin audit). Awaiting one of:

| Candidate | Lean status | LOC | Risk | Blocker |
|---|---|---|---|---|
| (C1) `findPanchromaticBrute` brute-force | **SHIPPED** (S2 ACT #18648, 168 LOC, 0/0) | — | — | none |
| (C2-1d) Scarf walk on `intervalTriangulation` | PREP designed (#18489), **ACT pending** | ~120 | MEDIUM (termination measure) | none |
| (C2-gen) Scarf walk on general `Triangulation` | DEFERRED | ~250 | HIGH | (C3) must land first |
| (C3) `findOppositeIdx` Classical.choose → computable | PREP audited (#18392), **ACT pending** | ~80 | MEDIUM (verified-parent re-build) | none |
| S3 ACT — apply S3 PREP SHA-pin corrections to OQ05 Lean | **Optional cosmetic** (build is correct at lockfile SHA, citations only) | <20 | LOW | none |
| S3 GALLERY — `src/data/proofs/sperner-simplicial-instance-oq-05/` | Not yet shipped | ~10 files | LOW | none |

**Next reasonable ACT**: (C2-1d) Scarf walk has the highest mathematical
value (it's the literal algorithmic content of OQ-05) and is unblocked.
S3 GALLERY is the next "easy ship" that converts the existing C1 work
into a public gallery entry. (C3) and (C2-gen) are the long-tail path
to discharging `axiom scarf_approx_fixed_point` in
`BrouwerFixedPointOQ04OQ04.lean:244`.

**Open PRs on slug**: none (verified 2026-05-13T22:30Z).

**Aggregate Lean delta**: 168 LOC, 5 declarations (1 `def`, 3 theorems,
1 example), 0 sorries, 0 axioms.

**Aggregate doc delta**: 7 session memos + this state log + problem.md
+ knowledge.md, totalling ~2,300 lines across 10 files.

