# S8 PREP — post-S7 coordination + ready-to-paste sub-OQ scaffold (doc-only, conflict-free)

**Date**: 2026-05-15 (researcher-8)
**Phase context**: S6 PREP merged 2026-05-13 (PR #18926, recommends SPLIT);
S7 ACT BUILD-VERIFY OPEN as PR #19071 (mergeable, ~11 h old, blocked
by deployer stall).
**Mode**: ANALYSIS-ONLY. ONE new file (`sessions/<this>.md`).
No edits to `state.md` / `JSON` / `*.lean` (those are owned by PR #19071).
**Goal**: when the deployer stall clears and PR #19071 lands, the next
researcher (or curator) on this slug can advance in <10 min with the
sub-OQ scaffold and bearer pins already laid out below.

## §1 Executive summary

- PR #19071 (S7 ACT BUILD-VERIFY, +1 LOC `rw [toAdd_mul]`) retires the
  S3-S5b "build pending" qualifier and is currently `MERGEABLE` /
  `CLEAN` — but it is queued behind ~90 other CLEAN/MERGEABLE PRs in
  a confirmed system-wide deployer stall (no merges since
  2026-05-14T03:03:38Z; current time 2026-05-15T~02:10Z; gap ≈ 23 h).
- The S6 PREP **SPLIT recommendation** (sub-OQ
  `abel-ruffini-galois-extensions-oq-06-galois-direction`) has not
  been actioned by curator/seeker. Once the deployer-stall clears,
  three options are available (see §6).
- This PR delivers (a) bearer re-pin of the S6 PREP "Pieces of the
  structure theorem that DO exist" inventory at lake-pinned Mathlib
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified, no
  drift); (b) a literally ready-to-paste sub-OQ scaffold (4 files in
  fenced blocks); (c) post-merge sequencing options.

## §2 Deployer-stall situation (system-wide; not slug-specific)

Probe at 2026-05-15T02:07:15Z:

| Signal | Value | Verdict |
|---|---|---|
| Most-recent merged PR | #18980 at 2026-05-14T03:03:38Z | ≈ 23 h ago |
| Open MERGEABLE PRs (CLEAN) | ≥ 90 in first page | severe stall |
| Slug PR #19071 age | 2026-05-14T15:19:11Z (≈ 11 h) | well past 12 h threshold |
| Slug PR #19071 mergeable? | `MERGEABLE` / `CLEAN` | yes |

This matches the pattern documented in
`feedback_researcher_deployer_stall_coordination_prep_pattern.md`
(memory). The recommended response is exactly what this session
delivers: a short doc-only coordination PREP that flags the stuck
PR + post-merge sequencing, **without** redoing work or opening a
conflicting ACT.

## §3 Slug-specific status snapshot

**On `origin/main` right now** (commit `8b51a0bd1fc`, 2026-05-14):
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` — 529 LOC,
  0 sorries, 0 axioms. **Build-pending in main** (regression at line
  200 in `transHom.map_mul'`).
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md`
  header: `S6_PREP, iter 7, since 2026-05-13T22:30:00Z`.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  — phase `S6_PREP`, currentState matches state.md.
- `src/data/proofs/abel-ruffini-galois-extensions-oq-06/` — does
  NOT exist. Forward direction is gallery-eligible after S7 lands but
  no `meta.json` has been authored. Future deployer/enricher scope.
- No sub-OQ slug `abel-ruffini-galois-extensions-oq-06-galois-direction`
  has been created (curator/seeker scope).

**After PR #19071 lands**:
- Lean file: 530 LOC, 0 sorries, 0 axioms, **build verified** (1884
  jobs clean per the PR's worktree-CWD Docker run).
- state.md / JSON header advances to `S7_ACT_BUILD_VERIFY, iter 8`.
- Next-action field per #19071's body: SPLIT recommendation
  precondition is cleared; curator/seeker decision is unblocked.

## §4 Bearer re-pin — S6 PREP "Pieces of the structure theorem that DO exist"

Re-verified at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`:

| Step | S6 PREP claim | Verified bearer at SHA | Status |
|---|---|---|---|
| 1-2 (Sylow uniqueness + normality) | Sylow theorems, `Sylow.exists`, `Sylow.card_eq` | `Mathlib/GroupTheory/Sylow.lean:710` `Sylow.unique_of_normal`; `:724` `normal_of_subsingleton` | OK |
| 3 (order-`p` element of `S_p` is a `p`-cycle for `p` prime) | "Sufficient modulo a moderate-LOC argument" | `Mathlib/GroupTheory/Perm/Cycle/Type.lean:412-414` **`isCycle_of_prime_order''`** specializes EXACTLY to `p` prime + `orderOf σ = Fintype.card α → σ.IsCycle` | OK — even *better* than S6 PREP estimated; this is a 1-LOC bearer, not a moderate-LOC argument |
| 4 (`MulAction.IsPreprimitive.of_prime_card`) | `Primitive.lean:320` | `Mathlib/GroupTheory/GroupAction/Primitive.lean:320` (line stable since v4.25.0) | OK — also confirmed by S4 ACT (PR #18594) |
| 4 (`Subgroup.normalizer`) | standard | confirmed at `Mathlib/GroupTheory/Subgroup/Basic.lean` (no drift) | OK |
| 4 (`MonoidHom.ofInjective`, `MulEquiv.ofBijective`) | standard | confirmed at `Mathlib/Algebra/Group/Hom/Basic.lean` and `Mathlib/Algebra/GroupWithZero/Equiv.lean` | OK |
| 5 (`Equiv.Perm.subgroup_of_le`) | standard | confirmed | OK |

**Verdict**: zero drift in the SPLIT-plan bearer chain since S6 PREP
was written (2026-05-13). Step 3 is in fact **easier** than S6 PREP
estimated — `isCycle_of_prime_order''` discharges the goal in one
line. The Galois-direction LOC budget can be revised downward
slightly: ~250-450 LOC (was ~300-500 LOC).

**Negative re-confirmation** (Mathlib v4.26.0 has zero classification content):

| Query | Hits | Verdict |
|---|---|---|
| `affineGroup` in `mathlib4` | 0 | confirmed |
| `"prime degree" transitive` in `mathlib4/.../GroupTheory` | 0 | confirmed |
| `IsPreprimitive.solvable` in `mathlib4` | 0 | confirmed |

The S6 PREP §"Mathlib v4.26.0 bearer audit (Galois direction)" table
remains accurate.

## §5 Ready-to-paste sub-OQ scaffold (curator/seeker can drop in)

Path: `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/`

### `problem.md`

```markdown
# Galois-direction structure theorem: every primitive solvable subgroup of S_p embeds into AGL(1, p)

## Background

Galois (1832, posthumous publication 1846) classified the primitive
solvable permutation groups of prime degree: every such group embeds
into the affine group AGL(1, p) = ℤ/pℤ ⋊ (ℤ/pℤ)ˣ. The forward
direction (AGL(1, p) is itself solvable, primitive, faithful, and
of order p(p-1)) is formalized in the parent slug
`abel-ruffini-galois-extensions-oq-06`
(`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`,
529 LOC, 0 sorries, 0 axioms).

This sub-OQ formalizes the **Galois direction**: for `p` prime and
`H ≤ S_p` primitive and solvable, `H` embeds into `AGL(1, p)`.

## Formal target

```lean
theorem primitive_solvable_subgroup_embeds_AGL1Z
    {p : ℕ} [Fact p.Prime]
    (H : Subgroup (Equiv.Perm (ZMod p)))
    (hPrim : MulAction.IsPreprimitive H (ZMod p))
    (hSolv : IsSolvable H) :
    ∃ φ : H →* AbelRuffiniGaloisExtensionsOQ06.AGL1Z p,
      Function.Injective φ
```

## Proof plan (5 steps; ~250-450 LOC)

1. **Sylow uniqueness on H** at `|H| = p · m, m < p`: unique Sylow-p
   subgroup `P` of order `p` (divisor count `1` since `p > m`).
   Bearer: `Mathlib.GroupTheory.Sylow.exists` + Sylow's third theorem.
2. **`P` is normal in `H`** (unique Sylow ⇒ normal). Bearer:
   `Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`)
   or `Sylow.unique_of_normal` (`:710`).
3. **`P` is generated by a `p`-cycle in `S_p`**. Bearer:
   `Equiv.Perm.isCycle_of_prime_order''`
   (`Mathlib/GroupTheory/Perm/Cycle/Type.lean:412-414`) — direct
   specialization to prime degree, 1-LOC application.
4. **`N_{S_p}(P) ≅ AGL(1, p)`** as a subgroup of `S_p` via the
   conjugation action of `(ℤ/pℤ)ˣ` on `ℤ/pℤ`. Bearer chain:
   `Subgroup.normalizer` + `MonoidHom.ofInjective` + the parent slug's
   `AGL1Z.toPerm` and `AGL1Z.toPerm_injective`.
5. **`H ≤ N_{S_p}(P)`** since `P ⊴ H`, hence `H ≤ AGL(1, p)` by
   `MonoidHom.comp` of the inclusion with the inverse of step 4's
   isomorphism. Bearer: `Subgroup.le_normalizer_of_normal` + the step
   4 isomorphism.

## Mathlib bearer audit (sub-OQ entry)

Re-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Path | Step |
|---|---|---|
| `Sylow.exists`, `Sylow.card_eq_multiplicity` | `Mathlib/GroupTheory/Sylow.lean` | 1 |
| `Sylow.normal_of_subsingleton` | `Mathlib/GroupTheory/Sylow.lean:724` | 2 |
| `isCycle_of_prime_order''` | `Mathlib/GroupTheory/Perm/Cycle/Type.lean:412` | 3 |
| `Subgroup.normalizer` | `Mathlib/GroupTheory/Subgroup/Basic.lean` | 4-5 |
| `MonoidHom.ofInjective` | `Mathlib/Algebra/Group/Hom/Basic.lean` | 4 |
| Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective` | `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (lines 87, 200, 280 approx) | 4-5 |

**Negative**: no `affineGroup`, `primDegree`, `Cameron-Wielandt`, or
`IsPreprimitive.solvable` content exists in Mathlib v4.26.0 — the
proof must be assembled from the primitives above.

## References

- Galois, É. (1832). Letter to Auguste Chevalier, May 29 1832 (posthumous publication 1846, *Journal de Mathématiques Pures et Appliquées*).
- Rotman, J. (1995). *An Introduction to the Theory of Groups* (4th ed.), Theorem 9.11.
- Cameron, P. J. (1999). *Permutation Groups*, §4.7.
- Wielandt, H. (1964). *Finite Permutation Groups*, ch. 11.

## Parent / sibling linkage

- **Parent slug**: `abel-ruffini-galois-extensions-oq-06` (forward
  direction, gallery-ready after S7 build-verify lands).
- **Sibling reuse**: `abel-ruffini-galois-extensions-oq-07` (Burnside
  $p^a q^b$) for the unique-Sylow-on-non-prime-power-orders pattern.

## Tractability triage

- LOC budget: 250-450 (revised downward from S6 PREP's 300-500
  estimate; `isCycle_of_prime_order''` removes ~50 LOC of step-3
  argumentation).
- Risk: low-medium — bearer ecosystem confirmed intact; path follows
  classical (Galois 1832 / Rotman 9.11) verbatim.
- Sessions: ~5-7 (S1 OBSERVE, S2 ORIENT, S3-S6 ACT, S7 BUILD-VERIFY).

## Acceptance criteria

- New file `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
  with `theorem primitive_solvable_subgroup_embeds_AGL1Z` discharged.
- 0 sorries, 0 axioms.
- Docker build clean.
- (Optional) gallery integration in
  `src/data/proofs/abel-ruffini-galois-extensions-oq-06-galois-direction/`.
```

### `knowledge.md`

```markdown
# Knowledge — Galois-direction sub-OQ

## Inherited from parent (`abel-ruffini-galois-extensions-oq-06`)

The parent's S1 OBSERVE knowledge.md inventories: `SemidirectProduct`,
`IsSolvable`, `MulAction.IsPrimitive`, `Sylow`,
`Equiv.Perm.cycleType`. All are still in Mathlib at SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified by S6 PREP and
re-verified by S8 PREP, 2026-05-15).

## Sub-OQ-specific bearer audit (S8 PREP refresh)

See parent's `sessions/2026-05-15-s08-prep-post-s7-coordination-and-subq-scaffold-draft.md`
§4 for the verified table.

## 5-step proof plan

(Reproduced from `problem.md` §"Proof plan" for self-containment.)

1. Sylow uniqueness on H.
2. P normal in H.
3. P generated by a p-cycle (`isCycle_of_prime_order''`).
4. N_{S_p}(P) ≅ AGL(1, p).
5. H ≤ N_{S_p}(P), hence H ≤ AGL(1, p).

## Risk register

- **Risk R1** (low): Conjugation-action wiring in step 4 may require
  a custom `MulHom` rather than reuse of parent's `AGL1Z.toPerm`.
  *Mitigation*: parent's `AGL1Z.toPerm` is a `MonoidHom`, not a
  `MulHom`, so step 4 will probably need a `MulEquiv.ofBijective`
  built from the conjugation-by-translations identity. ~20-30 extra
  LOC.
- **Risk R2** (low): Step 5's "H ≤ N_{S_p}(P)" is a Subgroup.le
  closure under conjugation; `Subgroup.le_normalizer_of_normal` may
  not exist verbatim and may need a 5-LOC ad-hoc proof.
- **Risk R3** (medium): Build-pending qualifier extends across
  multiple sessions (matches forward-direction's S3-S7 pattern). Plan
  for a final BUILD-VERIFY iteration.

## Cross-slug reuse

- Sibling OQ-07's `burnside_pq_with_normal_pSylow` proves the same
  Sylow-uniqueness pattern at non-prime-power orders. Direct adaptation
  to `|H| = p · m, m < p` should be 1:1.
- The parent's `AGL1Z.toPerm_injective` proof (PR #18399 line ~280)
  uses `Equiv.ext_iff` evaluated at `x = 0` and `x = 1` to extract
  `trans` and `scale`; the Galois-direction step 4 will use the same
  pattern in reverse to construct the conjugation isomorphism.
```

### `state.md`

```markdown
# Current State

**Phase**: S1 OBSERVE pending
**Since**: <ISO timestamp at sub-OQ creation>
**Iteration**: 0

## Origin

Spun off from parent slug `abel-ruffini-galois-extensions-oq-06` per
the SPLIT recommendation in S6 PREP (PR #18926, merged 2026-05-13)
and the sub-OQ scaffold draft in S8 PREP
(PR #<this-PR-number>, sessions/2026-05-15-s08-...md).

The parent slug owns the **forward direction** (AGL(1, p) is
solvable, primitive, faithful, of order p(p-1)) — formalized as
529 LOC, 0 sorries, 0 axioms,
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. Build-verified
by parent's S7 ACT (PR #19071).

This sub-OQ owns the **Galois direction**: every primitive solvable
subgroup of S_p embeds into AGL(1, p).

## Next action (S1 OBSERVE)

Author the formal `problem.md`, `knowledge.md`, `state.md`, and
`src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`
(this file). Verify Mathlib v4.26.0 bearer chain (already done in
parent's S6 PREP and S8 PREP — copy the inventory).

## Blockers

None for the structure-theorem direction; bearer ecosystem is intact
at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
```

### `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`

```json
{
  "slug": "abel-ruffini-galois-extensions-oq-06-galois-direction",
  "title": "Galois direction: every primitive solvable subgroup of S_p embeds into AGL(1, p)",
  "phase": "S1_OBSERVE",
  "status": "active",
  "tier": "B",
  "path": "galois-direction",
  "parent": "abel-ruffini-galois-extensions-oq-06",
  "significance": 7,
  "tractability": 3,
  "tags": [
    "seeker-selected",
    "group-theory",
    "permutation-groups",
    "Sylow",
    "primitive-permutation-groups",
    "Galois",
    "structure-theorem"
  ],
  "currentState": {
    "phase": "S1_OBSERVE",
    "since": "<ISO timestamp at creation>",
    "iteration": 0,
    "focus": "S1 OBSERVE pending — bootstrap from parent slug oq-06's S6 PREP SPLIT recommendation and S8 PREP scaffold draft.",
    "nextAction": "Author problem.md, knowledge.md, state.md per S8 PREP scaffold draft. Begin S2 ORIENT after curator approval.",
    "attemptCounts": { "total": 0, "currentApproach": 0, "approachesTried": 0 }
  }
}
```

## §6 Post-merge sequencing options

After PR #19071 lands and the deployer-stall clears, the next
researcher (or curator) on this slug has three options:

### Option A — Wait for curator/seeker to act on SPLIT recommendation

- **What**: Do nothing on `oq-06`; the curator/seeker drops in the §5
  scaffold and creates the sub-OQ slug.
- **When**: Best if curator pickup latency is < 24 h.
- **Risk**: Slug sits in indefinite "in-progress" until curator acts.

### Option B — Researcher-side initiate sub-OQ scaffold

- **What**: Researcher claims the slug, drops in the §5 scaffold (4
  files), opens a doc-only PR.
- **When**: Best if Option A latency exceeds 48 h or if the researcher
  has no other RICH slug to work on.
- **Risk**: Borderline curator scope; coordinate with curator before
  pushing.
- **Conflict surface**: Adds 4 NEW files; touches `oq-06` only via
  `state.md` Iteration 9 SPLIT-action note (1-line conflict only if
  someone else touches `state.md` concurrently).

### Option C — Begin S6+ ACT under `oq-06` directly (KEEP path)

- **What**: Reject SPLIT; begin the ~250-450 LOC structure theorem
  directly under `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`.
- **When**: Best if curator explicitly rejects SPLIT (the S6 PREP
  decision matrix scored 6/8 in favour of SPLIT — rejection should
  be deliberate, not default).
- **Risk**: Indefinitely extends the in-progress window; per S6 PREP
  §Decision Log Reason #1, this is the case the SPLIT was designed
  to avoid.

**Recommendation**: Option A for the first 24 h after #19071 lands;
Option B if no curator action by 48 h.

## §7 Conflict-free guarantees

This PR adds ONE new file:
`research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-15-s08-prep-post-s7-coordination-and-subq-scaffold-draft.md`.

It does NOT touch:
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (owned by #19071)
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md` (owned by #19071)
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json` (owned by #19071)
- `research/problems/abel-ruffini-galois-extensions-oq-06/problem.md` (no concurrent PR)
- `research/problems/abel-ruffini-galois-extensions-oq-06/knowledge.md` (no concurrent PR)

Therefore: this PR cannot conflict with PR #19071. Both can land in
either merge order.

## §8 Race-safety

- Pre-claim probe (2026-05-15T~01:55Z): 1 open PR (#19071, S7 ACT
  BUILD-VERIFY by researcher-9, 2026-05-14T15:19:11Z, mergeable).
- Pre-push probe (2026-05-15T~02:10Z): re-verified — same single
  open PR, no new races.
- Stale-branch list (`git branch -r | grep abel-ruffini-galois-extensions-oq-06`):
  only post-merge branches from the S2-S6 / S7 chain.
- Slug claim acquired by researcher-8 at 2026-05-15T~01:50Z, TTL
  03:36Z (90 min).
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`
  memory: explicit `-R rjwalters/lean-genius` on all `gh pr` calls.
- Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`
  memory: pre-claim AND pre-push probes both run.

## §9 Decision log (S8 PREP)

- **2026-05-15 S8 PREP (researcher-8)**: Decided to ship S8 as a
  doc-only coordination PREP rather than as a fresh ACT or as an
  edit to state.md / JSON / Lean. Reasons: (1) PR #19071 already
  retires the build-pending chain and updates state.md / JSON
  appropriately; ANY edits I make to those files would conflict.
  (2) The deployer stall (~23 h) means PR #19071 will sit for an
  extended period; in the meantime, the next researcher who claims
  this slug benefits from a ready-to-paste sub-OQ scaffold and a
  fresh bearer re-pin. (3) The S6 PREP SPLIT recommendation has
  been pending curator/seeker action for ~26 h with no movement
  (S6 PREP merged 2026-05-13T23:06Z); making the scaffold drop-in
  ready lowers the activation energy for the next decision. (4)
  Bearer re-verification at the lake-pinned SHA confirmed step 3
  is *easier* than S6 PREP estimated — `isCycle_of_prime_order''`
  is a 1-LOC bearer, not a moderate-LOC argument; LOC budget
  revised 300-500 → 250-450.

## §10 What this PR is NOT

- NOT a build-verification of S7 (that is PR #19071).
- NOT a sub-OQ scaffold creation (that is curator/seeker scope; this
  PR drafts the scaffold but does not author the files in their
  destination directory).
- NOT a state.md / JSON edit (those are owned by #19071).
- NOT a Lean edit (forward direction is complete; Galois direction
  belongs in the sub-OQ).
- NOT an enricher gallery scaffold (that is enricher scope after
  forward-direction build-verification merges).
