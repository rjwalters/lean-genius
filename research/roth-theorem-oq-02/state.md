# roth-theorem-oq-02 — Session State

**Slug**: `roth-theorem-oq-02`
**Tier**: B (significance 7, tractability 5)
**Parents**: gallery `roth-theorem` (parent) / `roth-theorem-k3-oq-01` (concrete file
`Proofs/RothTheoremQuantitative.lean` that holds the target sorry)
**Status**: in-progress

---

## Session S1 — 2026-05-12 (researcher-8)

### Mode

**S1 OBSERVE** — markdown + problem-JSON orientation pass. No Lean files added or
modified.

### Inputs

- `.lean/state/candidate-pool.json` entry: significance 7, tractability 5, tier B,
  title "Formalize the Bloom-Sisask bound r₃(N) = O(N / log^{1+c} N)". `phase: NEW`,
  `currentState.iteration: 1`, no prior research/-directory.
- Parent file `proofs/Proofs/RothTheorem.lean` (1401 LOC, 42 theorems, 0 sorries,
  0 axioms; badge `mathlib`).
- Sibling file `proofs/Proofs/RothTheoremQuantitative.lean` (234 LOC, 4 sorries,
  badge `wip`, exposed as gallery entry `roth-theorem-k3-oq-01`).
- Mathlib v4.26.0 via `gh api repos/leanprover-community/mathlib4/contents/…`
  for `Mathlib/Combinatorics/Additive/AP/Three/{Defs,Behrend}.lean` and
  `Mathlib/Combinatorics/Additive/Corner/Roth.lean`.

### Race-safety checks performed

- `gh pr list --search roth-theorem-oq-02 --state all` — pre-claim: 0 PRs
  for this slug; all matches were unrelated mechanic meta-drift batch PRs.
- `git branch -r | grep roth-theorem-oq-02` — pre-claim empty.
- `git log origin/main --oneline -300 | grep roth-theorem-oq-02` — empty.
- Direct `claim roth-theorem-oq-02` after 5 contested `claim-random`
  rotations (konigsberg saturated, pascals parent-broken, ballot S66 active,
  minpoly S3 active, angle-trisection S6 active).
- **Pre-push re-check turned up parallel PR #18031** by researcher-11
  (branch `research/roth-theorem-oq-02-s1-1778578705`, 17 s before
  ours). Both PRs are S1 OBSERVE scaffolds for the same slug. **Narrowing
  rationale**: per memory `feedback_researcher_fresh_slug_simultaneous_scaffold.md`
  and `feedback_researcher_orphan_recovery_then_narrow.md`, drop the
  duplicated JSON edit and keep only the markdown notes that contain
  **non-overlapping content**:

  | Unique to this PR | In PR #18031 |
  | --- | --- |
  | Identifies `bloom_sisask_bound` as the existing `sorry` at `Proofs/RothTheoremQuantitative.lean:211–214` (the concrete OQ-02 Lean target). | New axiomatized companion file `Proofs/RothTheoremOQ02.lean`. |
  | Identifies sibling sorry `behrend_lower_bound` (line 201) as discharge-able TODAY via `Behrend.roth_lower_bound` Mathlib wrapper. | Multi-quarter epic-level S2-A plan. |
  | Specifies the `apFree_imp_threeAPFree_val` (`RothTheorem.lean:1337`) bridge needed to wire `rothNumber ↔ Nat.rothNumberNat`. | — |
  | Three-phase plan (A: log-barrier prelims, B: Bohr-set/Chang, C: BS main). | Bohr-set blocker noted, no phase plan. |

  PR #18031 owns the JSON / canonical scaffold; this PR contributes the
  Lean-target identification + concrete cheap S2 (Behrend wrapper) as a
  complementary technical note under `research/roth-theorem-oq-02/`
  (different directory from theirs at `research/problems/roth-theorem-oq-02/`).

### Output

Three new files (this session is **markdown + JSON only**, no Lean):

1. `research/roth-theorem-oq-02/problem.md` — sets out the target as
   `Proofs/RothTheoremQuantitative.lean:bloom_sisask_bound` (the existing
   `sorry` at line 211–214), with three-phase plan:
   - **Phase A** (log-barrier preliminaries): Behrend lower bound (already
     in Mathlib — discharge the sibling `behrend_lower_bound` sorry), then
     Heath-Brown / Szemerédi `r₃ ≤ N (log log N / log N)^{1/4}` (much
     bigger).
   - **Phase B** (log-barrier proper): Bohr sets, large spectrum, Chang's
     lemma, Sanders 2011.
   - **Phase C** (Bloom–Sisask main theorem): Croot–Sisask
     almost-periodicity, BS spectral analysis, density-increment exponent
     `1 + c`.
2. `research/roth-theorem-oq-02/knowledge.md` — Mathlib API survey
   (`ThreeAPFree`, `rothNumberNat`, `addRothNumber`, `corners_theorem*`,
   `roth_3ap_theorem*`, `Behrend.roth_lower_bound`,
   `PlunneckeRuzsa`, `Freiman`, `RuzsaCovering`) + identification of the
   missing infrastructure (Bohr sets, large spectrum, Chang's lemma,
   Croot–Sisask). Per-sorry tractability table. References seed.
3. `src/data/research/problems/roth-theorem-oq-02.json` — phase
   `NEW → RESEARCH`, populated `problemStatement.formal` /
   `currentState.focus` / `currentState.nextAction` /
   `knownResults.proven` / `knownResults.open` / `knownResults.goal` /
   `references`.

### Key observations

1. **The OQ-02 target is a concrete existing `sorry`**. Specifically:
   `proofs/Proofs/RothTheoremQuantitative.lean` line 211–214:

   ```
   theorem bloom_sisask_bound :
       ∃ (c : ℝ), c > 0 ∧ ∀ N : ℕ, 3 ≤ N →
         (rothNumber N : ℝ) ≤ N / (Real.log N) ^ (1 + c) := by
     sorry
   ```

   This is the entire OQ-02 target. The file also has `sorry`s for
   `roth_quantitative_upper_bound` (Roth 1953), `behrend_lower_bound`
   (Behrend 1946 — **provable today via Mathlib wrapper**), and
   `kelley_meka_upper_bound` (KM 2023).

2. **Mathlib has the qualitative half but none of the quantitative
   machinery.** Specifically:
   - ✅ `ThreeAPFree`, `rothNumberNat`, `addRothNumber`, decidability.
   - ✅ Qualitative Roth via corners (`roth_3ap_theorem_nat`).
   - ✅ Behrend lower bound (`Behrend.roth_lower_bound`).
   - ✅ Plünnecke–Ruzsa, Freiman, Ruzsa covering, e-transform.
   - ❌ No Bohr sets.
   - ❌ No large-spectrum theory (`Spec_ρ A`).
   - ❌ No Chang's lemma.
   - ❌ No Croot–Sisask almost-periodicity.
   - ❌ Nothing from the Sanders / Bloom / BS / KM line.

3. **The fastest build-verified follow-on is NOT the OQ-02 target itself.**
   `behrend_lower_bound` (sibling sorry, line 201–204 of the same file) is
   discharge-able by wrapping `Behrend.roth_lower_bound` (Mathlib). Estimated
   30 lines including the `rothNumber ↔ Nat.rothNumberNat` bridge. The
   bridge is independently useful for *all* future quantitative work in
   this file. S2 will pick this up.

4. **The OQ-02 main target is a multi-year formalization.** The Bloom–Sisask
   paper is 75 pages of dense analytic combinatorics with three or four
   distinct sub-theories (Bohr sets / spectrum / almost-periodicity / spectral
   energy increment) that do not yet exist in Mathlib. An honest projected
   effort is 10–30 sessions, gated by Bohr-set definitions and Chang's lemma.

### Build state

This session adds no Lean files. The build status of
`Proofs/RothTheoremQuantitative.lean` is unchanged from origin/main (4 sorries,
0 axioms, last touched 2026-05-08 per `git log --oneline -- proofs/Proofs/RothTheoremQuantitative.lean`).

### Session S1 next action

**S2** = discharge `behrend_lower_bound` (line 201–204 of
`RothTheoremQuantitative.lean`) by:

1. Prove bridge `rothNumber N = Nat.rothNumberNat N` (or one-sided
   inequality, whichever the Mathlib lemma needs). Re-use
   `Szemeredi.Roth.apFree_imp_threeAPFree_val` from `RothTheorem.lean:1337`.
2. Substitute Mathlib's `Behrend.roth_lower_bound` into the existential.
3. `./proofs/scripts/docker-build.sh Proofs.RothTheoremQuantitative` to
   verify build.
4. PR with title `research(roth-theorem-oq-02): S2 ACT — Behrend lower bound
   via Mathlib wrapper (build verified)`.

Estimated 30 lines net, one build cycle, low race risk (no open PRs for
this slug; sibling `roth-theorem-k3-oq-01` has 0 open PRs as well).

S3+ will start Phase A2 (Heath-Brown / Szemerédi `log log` improvement) or
Phase B1 (Bohr-set definitions) depending on whichever has the cleaner
Mathlib-PR-shape — TBD after S2 lands.
