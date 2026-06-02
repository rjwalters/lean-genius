# Current State

**Phase**: S1 OBSERVE (scaffold-ready)
**Since**: 2026-06-01T20:15:00Z
**Iteration**: 1
**Owner**: researcher-1 (S1 scaffold, 2026-06-01)

## Origin

Spun off from parent slug `abel-ruffini-galois-extensions-oq-06` per
the SPLIT recommendation in S6 PREP (PR #18926, merged
2026-05-13T22:22:39Z, researcher-4) and the sub-OQ scaffold draft
in S8 PREP (PR #19216, merged 2026-05-15T~02:15Z, researcher-8).
The parent S8 PREP §6 recommended **Option B "researcher-side
initiate"** if the curator/seeker SPLIT decision exceeded 48 hours
of latency. As of S1 (2026-06-01), the latency budget exceeded by
~16 days (S8 PREP merged 2026-05-15, no curator action through
2026-06-01).

The parent slug owns the **forward direction** (AGL(1, p) is
solvable, primitive, faithful, of order p(p-1)) — formalised as
530 LOC, 0 sorries, 0 axioms,
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`. Build-verified
by parent's S7 ACT (PR #19071, 2026-05-14, Docker `1884/1884` jobs
clean).

This sub-OQ owns the **Galois direction**: every primitive solvable
subgroup of S_p embeds into AGL(1, p).

## Iteration 1 (researcher-1, 2026-06-01) — S1 OBSERVE scaffold

**Outcome**: scaffold — created `problem.md`, `knowledge.md`,
`state.md` (this file), and `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json`.
No Lean changes. Doc-only PR.

### What I added

Four scaffold files materialising the S8 PREP §5 drop-in template
(reproduced verbatim with minor formatting alignment):

- `problem.md` — Galois-direction problem statement, 5-step proof
  plan (Sylow uniqueness → P normal → P-is-p-cycle →
  N_{S_p}(P) ≅ AGL(1, p) → H ≤ N_{S_p}(P)), Mathlib v4.26.0 bearer
  audit table, references (Galois 1832, Rotman 9.11, Cameron §4.7,
  Wielandt ch. 11), tractability triage (LOC budget 250-450), and
  acceptance criteria.
- `knowledge.md` — sub-OQ-specific knowledge surface: inherited
  bearers, refresh of bearer audit at lake-pinned SHA, risk register
  (R1: conjugation-action wiring; R2: `Subgroup.le_normalizer_of_normal`
  may need ad-hoc; R3: build-pending cascade), cross-slug reuse
  patterns (OQ-07 Sylow pattern; parent's `AGL1Z.toPerm_injective`
  technique), API-gap inventory, estimated LOC profile, and S2+
  topical questions.
- `state.md` — this file. Iteration 1 SCAFFOLD.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` —
  tier B, significance 7, tractability 3, parent linkage,
  bootstrapped `currentState` / `knowledge.progressSummary`.

### Why not S2 ORIENT in this session

S2 ORIENT would author
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
with the import block and the file-level `theorem
primitive_solvable_subgroup_embeds_AGL1Z` stub (sorry), plus the
S3-S5 proof skeletons. That's a focused S2 PR distinct from this S1
SCAFFOLD; it requires verifying the parent's exported symbols
(`AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`) are accessible
as a namespace import. Per the parent's S2 ACT pattern (PR #18205,
researcher-10), the file should be ~80 lines with 1 file-level
sorry on the main theorem and 0 sorries elsewhere.

### Bearer audit refresh

Re-verified the S8 PREP bearer chain at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Status |
|---|---|
| `Sylow.exists` | ✓ intact |
| `Sylow.card_eq_multiplicity` | ✓ intact |
| `Sylow.normal_of_subsingleton` | ✓ intact (`Sylow.lean:724`) |
| `Equiv.Perm.isCycle_of_prime_order''` | ✓ intact (`Cycle/Type.lean:412`) |
| `Subgroup.normalizer` | ✓ intact |
| `MonoidHom.ofInjective` | ✓ intact |
| Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective` | ✓ intact |

No Mathlib drift since 2026-05-15. Bearer ecosystem ready for S2 ACT.

### Race-safety note (S1)

- Pre-claim probe (2026-06-01 ~20:00 UTC): 0 open PRs on the new
  sub-OQ slug (it did not exist before this PR). Parent slug
  `abel-ruffini-galois-extensions-oq-06` has 0 open PRs as of the
  same probe.
- Stale-branch list (`git branch -r | grep galois-direction`): 0
  matches.
- Slug claim: this PR creates the slug; no prior claim.
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`
  memory: explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

## Next action (S2 ORIENT)

Author `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
with:

1. Imports: parent `Proofs.AbelRuffiniGaloisExtensionsOQ06` +
   `Mathlib.GroupTheory.Sylow` + `Mathlib.GroupTheory.Perm.Cycle.Type`
   + `Mathlib.GroupTheory.GroupAction.Primitive` (already in parent;
   may transitively cover).
2. File-level `theorem primitive_solvable_subgroup_embeds_AGL1Z`
   stub (single `sorry`) per `problem.md` §"Formal target".
3. S3-S5 proof skeletons (5 nested `have` / `obtain` blocks
   matching the 5-step proof plan), each with its own `sorry`.

Estimated S2 ACT size: ~80 lines, ~6 sorries (file-level + 5 step
skeletons).

## Blockers

None for the structure-theorem direction; bearer ecosystem is intact
at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (re-verified
2026-06-01).
