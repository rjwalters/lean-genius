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

---

## Session S2 — 2026-06-05 (researcher-1, STATE-SYNC + scope decision)

### Mode

**S2 STATE-SYNC** — re-verify file state since S1 (2026-05-12), confirm the four
sorries are still present at the same shape, then deliberately defer the
Behrend Mathlib wrapper attempt rather than land a half-built bridge.

### State re-verified at HEAD origin/main (2026-06-05)

`proofs/Proofs/RothTheoremQuantitative.lean` still carries 4 sorries, all
at the same theorem statements documented in S1 (line numbers shifted slightly
due to nearby refactors but the bodies match):

| Theorem | Old line (S1) | Current line | Statement shape |
| --- | --- | --- | --- |
| `roth_quantitative_upper_bound` | 187–190 | 239–242 | `∃ C > 0, ∀ N ≥ 3, (rothNumber N : ℝ) ≤ C·N / log(log N)` |
| `behrend_lower_bound` | 201–204 | 253–256 | `∃ c > 0, ∀ N ≥ 3, (rothNumber N : ℝ) ≥ N · exp(-c · √(log N))` |
| `bloom_sisask_bound` | 211–214 | 263–266 | `∃ c > 0, ∀ N ≥ 3, (rothNumber N : ℝ) ≤ N / (log N)^(1+c)` |
| `kelley_meka_upper_bound` | 223–226 | 275–278 | `∃ c > 0, ∀ N ≥ 3, (rothNumber N : ℝ) ≤ N · exp(-c · (log N)^(1/12))` |

The bridge candidate `apFree_imp_threeAPFree_val` is still at
`RothTheorem.lean:1337`, providing `APFree A → ThreeAPFree (image ZMod.val A : Set ℕ)`
— useful for the *upper*-bound direction `rothNumber N ≤ Nat.rothNumberNat N`.
The Behrend wrapper actually needs the *opposite* direction
`Nat.rothNumberNat N ≤ rothNumber N` (lifting a ℕ-side AP-free set to a
ZMod-side `APFree` set), which is a separate construction.

### Why S2 deferred the Behrend wrapper

1. **Bridge direction mismatch.** S1 assumed the existing
   `apFree_imp_threeAPFree_val` lemma was a direct enabler. On closer reading it
   is the *upper*-bound bridge (ZMod → ℕ); the Behrend wrapper needs the
   *lower*-bound bridge (ℕ → ZMod). That second bridge is provable but is
   genuinely new code — `Fin N → ZMod N` via `(i : ℕ) ↦ (i : ZMod N)`, plus a
   proof that `Function.Injective` on the image preserves `APFree`. It's likely
   another ~30 lines on top of the wrapper itself, raising the original S1
   estimate from "30 lines total" to ~60 lines spanning two artifacts.

2. **Mathlib signature unverified in this session.** This researcher worktree's
   `proofs/.lake/packages` resolves to a broken self-loop symlink, so direct
   `Read` of `Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean` is not
   available; the Docker cache lives only inside the build container. Without
   confirming the exact statement of `Behrend.roth_lower_bound` (constant
   placement, N-threshold, ℕ vs ℝ side of the inequality, presence of an
   `∃ c`, etc.), the wrapper cannot be written as a single
   informed pass — it would need open-ended iterative Docker probing.

3. **Cycle budget.** This is researcher-1's fifth iteration within the current
   90-minute TTL. The previous four landed clean structural-lemma PRs in
   ≤2 Docker cycles each; the Roth Behrend attempt is much higher-variance
   (the bridge code is new, the Mathlib signature is unknown). Deferring to a
   future session that starts with the Mathlib source in-hand is strictly
   better expected value than burning the remaining window on a probe loop.

### Output

This session adds no Lean files. Only this S2 STATE-SYNC note. No JSON edits.

### Concrete S3 plan (in priority order)

1. **S3a — make Mathlib readable from the worktree.** Either rebuild the
   worktree from a fresh `git worktree add` so `.lake/packages` resolves to
   a real directory, or have the launcher copy
   `Mathlib/Combinatorics/Additive/AP/Three/{Behrend,Defs}.lean` into
   `research/roth-theorem-oq-02/mathlib-snapshot/` before the researcher
   starts. Until this is fixed, every Mathlib-wrapper task on this slug
   pays the same probe-loop tax that S2 just declined.

2. **S3b — Behrend wrapper, informed pass.** Concrete ~60-line patch:
   - Prove `nat_rothNumberNat_le_rothNumber : ∀ N, Nat.rothNumberNat N ≤ rothNumber N`
     by mapping `Finset (Fin N) → Finset (ZMod N)` via the natural inclusion,
     using injectivity of `(· : ℕ) → ZMod N` for `· < N` to lift `ThreeAPFree`
     to `APFree`.
   - In `behrend_lower_bound`, instantiate `c` from `Behrend.roth_lower_bound`,
     chain through `nat_rothNumberNat_le_rothNumber`, close with `linarith` /
     `gcongr`.

3. **S4+** — Phase A2 (Heath-Brown / Szemerédi `log log`) or Phase B1
   (Bohr-set definitions) per the S1 phase plan.

### Race-safety re-check at S2 start

- `gh pr list --search roth-theorem-oq-02 --state open` — 0 open PRs.
- `git branch -r | grep roth-theorem-oq-02` — only the S1 scaffold branch
  history; no parallel in-flight researchers.
- This slug remains in `in-progress` status; the claim TTL refreshes after
  this S2 PR lands.
