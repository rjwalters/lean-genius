# Current State

**Phase**: S2 ORIENT (Lean stub authored; 5-step skeleton + main theorem stub; 7 sorries; 119 LOC; **Docker-build path clarified — G9 RECLASSIFIED via S3 STATE-SYNC 2026-06-10**)
**Since**: 2026-06-10 (S3 STATE-SYNC clarifies G9; was 2026-06-04T17:00:00Z S2 ORIENT)
**Iteration**: 3 (S1 scaffold merged via #22031 on 2026-06-02; S2 ORIENT 2026-06-04; S3 STATE-SYNC this iteration)
**Owner**: researcher-1 (S1 scaffold, 2026-06-01; S2 ORIENT, 2026-06-04; S3 STATE-SYNC, 2026-06-10)

## Iteration 3 (researcher-1, 2026-06-10) — S3 STATE-SYNC: G9 reclassification

**Outcome**: knowledge — clarification that the "G9 lake self-loop" blocker
flagged in S2 ORIENT is a **researcher-side grep-convenience issue**, NOT
a Docker-build blocker. The next ACT picker should not defer Docker on
G9 grounds.

### Evidence: Docker works on this worktree at HEAD `98d1689ec26`

Verified this session by researcher-1 in `.loom/worktrees/researcher-1/`:
- Ran `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG6`
  on a sibling file (new file under the same project root) on 2026-06-10.
- Result: **7743 jobs clean**, ~158 s for the new module, total ~5–6 min
  including Mathlib cache fetch. (Shipped as PR #22751 / S21 ACT on
  slug `lagrange-four-squares-waring-g2-oq-01`.)
- Host disk: 77 Gi free (`df -h /System/Volumes/Data` reports 92% used).
- Docker daemon: healthy.

The host-side `proofs/.lake` symlink in this worktree is indeed
self-referencing (`ls proofs/.lake/packages/` errors with "Too many
levels of symbolic links"). This means a researcher cannot
`grep -r '<symbol>' proofs/.lake/packages/mathlib/` from the host
shell to audit Mathlib bearer signatures. However, Docker uses **its
own .lake** inside the container; the host symlink does not enter the
container, so `docker-build.sh` is unaffected.

### Implications for S3 ACT picker

- **Docker build is fully available**. The S2 ORIENT framing
  "build pending — G9 lake self-loop" should not be read as
  "Docker is blocked"; it's "I can't grep Mathlib locally from the
  host." The S3 ACT picker can attempt the full 119-LOC file build
  immediately.
- **Bearer audits should use `gh api`** instead of host-side grep.
  Demonstrated this session on the laws-of-large-numbers-oq-01-oq-02
  S4 PREP (PR #22753): `gh api search/code` + `gh api repos/.../contents/...`
  reaches Mathlib v4.26.0 surface without local `.lake` access.
  Bearer pin (`2df2f015…`) is the same one the S2 ORIENT bearer
  pre-flight verified; no re-pin needed.
- **The 7 sorries are the real blocker**, not infrastructure. S3 ACT
  should plan a focused per-sorry discharge cycle. Step 2 (`sylow_p_normal`)
  is the cheapest (any unique Sylow is normal via
  `Sylow.normal_of_subsingleton`) — make it the warm-up.

### What this STATE-SYNC does NOT do

- Does not modify
  `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`.
  The 7 sorries are intact.
- Does not run a Docker build verification. The S21 ACT verification
  on a sibling file is sufficient evidence for Docker availability;
  re-running just to "prove the obvious" wastes ~5 min for no signal.
- Does not discharge any of the 7 sorries. Real S3 ACT work is
  reserved for a dedicated session — the Galois 1832 / Rotman 9.11
  proof recipe needs sustained engagement, not a 25-minute tail.

### Files touched (2 total)

- `research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction/state.md` — this block + phase line refreshed.
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06-galois-direction.json` — `currentState.{phase, since, iteration, focus, nextAction}`, `lastUpdate`.

### Honesty

This STATE-SYNC is doc-only:
- 0 Lean files touched, 0 sorry / axiom changes
- 0 new bearer verifications (S2 ORIENT bearer pre-flight inherited)
- 0 Docker build attempts (S21 ACT sibling-file verification reused)

The contribution is a single-paragraph reclassification of an
inherited blocker label, removing an unjustified deferral excuse from
the next picker's path.

---

## Iteration 2 (researcher-1, 2026-06-04) — S2 ORIENT Lean stub

**Outcome**: scaffold — created
`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`
(119 LOC, 7 sorries, 0 axioms, 6 theorems) plus the auto-generated
`proofs/Proofs.lean` import refresh (`+1 line` after running
`./.lean/scripts/generate-proofs-imports.sh`).

### What I added

- **`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06GaloisDirection.lean`**
  (NEW, 119 LOC, 7 sorries):
  - imports `Proofs.AbelRuffiniGaloisExtensionsOQ06`,
    `Mathlib.GroupTheory.Sylow`,
    `Mathlib.GroupTheory.Perm.Cycle.Type`
  - opens parent namespace `AbelRuffiniGaloisExtensionsOQ06`
  - 5 step-lemma stubs (one per S1 OBSERVE step):
    - `sylow_p_unique` — `Subsingleton (Sylow p H)` for primitive
      solvable `H ≤ S_p`
    - `sylow_p_normal` — `(P : Subgroup H).Normal` for the unique
      Sylow-p
    - `sylow_p_is_pcycle` — existence of a `p`-cycle `σ ∈ S_p` with
      `P ≤ ⟨σ⟩`
    - `normalizer_iso_AGL1Z` — `(zpowers σ).normalizer ≅ AGL1Z p` via
      conjugation
    - `H_le_normalizer` — `H ≤ (zpowers σ).normalizer` since `P ⊴ H`
  - file-level main stub
    `primitive_solvable_subgroup_embeds_AGL1Z` returning
    `∃ φ : H →* AGL1Z p, Function.Injective φ`
  - 7 sorries total (one per step + main)
- **`proofs/Proofs.lean`** auto-regenerated via
  `./.lean/scripts/generate-proofs-imports.sh` to add the new import
  line at the correct alphabetic insertion point.

### What I did NOT do (deferred to S3+)

- Discharge any of the 7 sorries.
- Run Docker build (G9 lake self-loop blocker; consistent with sibling
  build-pending PRs #21477 #21475 #21506 #22088).
- Author gallery files (`src/data/proofs/.../{meta.json, index.ts,
  annotations.json}`) — deferred until at least one sorry is discharged
  (S5+) so that gallery `status` can claim `formalized` or `verified`
  honestly per Axiom Integrity Policy.

### Bearer pre-flight (re-verified at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Sylow.exists`: ✓ intact
- `Sylow.normal_of_subsingleton` (`Mathlib/GroupTheory/Sylow.lean:724`): ✓ intact
- `Equiv.Perm.isCycle_of_prime_order''`
  (`Mathlib/GroupTheory/Perm/Cycle/Type.lean:412`): ✓ intact
- `Subgroup.normalizer`: ✓ intact
- `Subgroup.zpowers`: ✓ intact
- Parent `AGL1Z`, `AGL1Z.toPerm`, `AGL1Z.toPerm_injective`
  (`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`): ✓ intact

No Mathlib drift since S1 OBSERVE (2026-06-01, 3 days elapsed; SHA unchanged).

### Race-safety note (S2)

- Pre-claim probe (2026-06-04 ~17:00 UTC): 0 open PRs on the sub-OQ
  slug since S1 merge (#22031, 2026-06-02). Branch
  `research/abel-ruffini-galois-extensions-oq-06-galois-direction-s2-orient`
  is new (per `git branch -r | grep galois-direction` → 0 matches).
- Per `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`:
  explicit `-R rjwalters/lean-genius` on all `gh pr` calls.

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

## Iteration 1 (researcher-1, 2026-06-01) — S1 OBSERVE scaffold (merged via #22031, 2026-06-02)

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

## Next action (S3 ACT — discharge Step 1 `sylow_p_unique`)

The S2 ORIENT scaffold this iteration exposes 7 sorries. S3 ACT should
discharge **Step 1 (`sylow_p_unique`)** first because:

1. It has the cleanest bearer surface: `Sylow.exists` + `Sylow`
   API + `Nat.card H` divisibility arithmetic, all in
   `Mathlib.GroupTheory.Sylow`.
2. It is a prerequisite for Step 2 (`sylow_p_normal` needs a unique
   Sylow to extract `Sylow.normal_of_subsingleton`).
3. The argument follows Galois 1832 / Rotman 9.11 verbatim:
   - `|H| = p · m` where `m < p` (from primitivity + solvability +
     the fact that `H ≤ S_p`; this needs the parent's
     `IsPreprimitive.transitive` + a divisor-count argument).
   - Number of Sylow-p subgroups `s_p ∣ m, s_p ≡ 1 (mod p)`, so
     `s_p = 1` (since `m < p`).

Estimated S3 ACT size: ~40-60 LOC additional content (one theorem
fully discharged; 6 sorries remaining).

Subsequent iterations:

- S4 ACT — Step 2 (`sylow_p_normal`) via `Sylow.normal_of_subsingleton`,
  ~5-10 LOC.
- S5 ACT — Step 3 (`sylow_p_is_pcycle`) via `isCycle_of_prime_order''`,
  ~20-30 LOC.
- S6 ACT — Step 4 (`normalizer_iso_AGL1Z`), the hardest step;
  ~80-150 LOC.
- S7 ACT — Step 5 (`H_le_normalizer`) + main theorem composition,
  ~30 LOC.
- S8 BUILD-VERIFY — Docker build verification once G9 clears.
- S∞ — gallery integration.

## Blockers

None for the structure-theorem direction; bearer ecosystem is intact
at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (re-verified
2026-06-01).
