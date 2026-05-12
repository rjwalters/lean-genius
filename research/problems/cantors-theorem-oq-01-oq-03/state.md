# Current State

**Phase**: OBSERVE
**Since**: 2026-05-11 (S1 by researcher-1)
**Iteration**: 1

## Current Focus

S1 (researcher-1, 2026-05-11) — **OBSERVE survey** of König's
constraint on `|𝒫(ℝ)|`. Survey-only iteration: no Lean changes,
just the research/JSON scaffolding so the next iteration has a
clear API target list and decomposition.

### S1 deliverables (this PR)

* `research/problems/cantors-theorem-oq-01-oq-03/problem.md` —
  problem statement + the four target Lean theorems.
* `research/problems/cantors-theorem-oq-01-oq-03/knowledge.md` —
  full survey: König's classical statement, Mathlib API candidates,
  axiom-cleanliness check, S2+ decomposition.
* `research/problems/cantors-theorem-oq-01-oq-03/state.md` — this
  file.
* `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` —
  research-state JSON (knowledge score `0 → 14`).

### S1 findings (one-line summary)

* Parent file has an explicitly empty Part 7 ("König's Constraint
  on |𝒫(ℝ)|", lines 214–222). The whole problem is to fill it.
* Sibling `cantors-theorem-oq-01-oq-02` (line 131 of its
  `meta.json`) names the candidate Mathlib API as
  `Cardinal.lt_cof_power` — a cross-reference, not a verified
  invocation; S2 must confirm.
* König's classical statement decomposes into three Lean theorems
  of strictly increasing generality: cofinality bound on `2^𝔠`,
  ℵ_ω exclusion, general small-cofinality exclusion.
* The axiom-cleanliness question reduces entirely to whether the
  Mathlib König chain transitively imports any `axiom` declaration
  or relies on `Classical.choice` *that is itself classified as an
  axiom*. Mathlib treats `Classical.choice` as standard, so by
  Mathlib's accounting the chain is "axiom-free"; this should be
  documented in the eventual gallery `meta.json`.

## Active Approach

**OBSERVE → ORIENT → ACT** sequence:

* **S1 (this iteration, complete)** — OBSERVE.
* **S2 (next)** — ORIENT: verify Mathlib API names by quick
  successive Docker builds with `#check Cardinal.lt_cof_power` /
  `#check Cardinal.cof_aleph_omega0` / `#check Cardinal.sum_lt_prod`
  test files. (Each is < 30 lines and avoids the full module's
  build cost.) Report which names exist and their exact signatures.
* **S3** — ACT: write `proofs/Proofs/CantorsTheoremOQ01OQ03.lean`
  with the four target theorems, gallery `meta.json`, and gallery
  `index.ts`/`annotations.json`.
* **S4** — POLISH: cross-reference into the parent's Part 7
  (replace its empty comment with `import` + `#check`), and
  populate `cantors-theorem-oq-01`'s `conclusion.openQuestions[1]`
  with `[RESOLVED in oq-01-oq-03 (theorem konig_cof_powerSet_real)]`.

## Blockers

None. S2 is unblocked once an agent picks up this slug — only
needs Docker build access.

### Risks

* `Cardinal.lt_cof_power` may have been renamed in a recent Mathlib
  bump. If so, S2 reports the new name and S3 uses it. The fallback
  is to derive the cofinality bound from `Cardinal.sum_lt_prod`
  (König's general inequality) directly — the proof is < 20 lines
  and is a textbook exercise.
* The `Cardinal.aleph` index in current Mathlib uses
  `Ordinal.aleph` or sometimes a newer `aleph'` API; S2 verifies
  which is current.

## Next Action

**S2 (any researcher)** — verify the three API candidates from
`knowledge.md` §"Mathlib API verification". Commit a 3-line stub
file `proofs/Proofs/CantorsTheoremOQ01OQ03Probe.lean` containing
just

```lean
import Mathlib
#check @Cardinal.lt_cof_power
#check @Cardinal.sum_lt_prod
#check @Cardinal.cof_aleph_omega0
```

run `./proofs/scripts/docker-build.sh Proofs.CantorsTheoremOQ01OQ03Probe`,
report which `#check`s succeed, then delete the probe file and
proceed to S3 with the verified names. Estimate: 60 min wall
clock (45 min Mathlib refetch + 10 min cache fetch + 5 min compile).

## Attempt Counts

- Total attempts: 0 (S1 is documentation-only)
- Current approach attempts: 0
- Approaches tried: 0
