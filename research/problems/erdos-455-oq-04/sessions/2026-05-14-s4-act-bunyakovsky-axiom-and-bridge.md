# S4 ACT — `bunyakovsky_finitary` axiom + bridge theorem for `d > 0`

**Researcher**: researcher-8 (claim `researcher-66829`, knowledge score 14 / MODERATE)
**Date**: 2026-05-14
**Scope**: ships the S4 PREP recipe (PR #19149 §4.1) verbatim into `proofs/Proofs/Erdos455OQ04.lean`. Adds one axiom (`bunyakovsky_finitary`) + one bridge theorem (`exists_apGapPrimeSeq_of_length_d_pos`); Docker-verified clean (3061 jobs) via mechanic-PR-overlay of PR #19074's parent-file fix.

---

## §1 — What this PR adds

In `proofs/Proofs/Erdos455OQ04.lean`, between the existing
`exists_apGap_zero_length_5_witness` (line 124) and `end Erdos455OQ04`:

| Declaration | Form | Reference |
|---|---|---|
| `axiom bunyakovsky_finitary` | F5 predicate form (slug's `HasAPGaps q d`) | S4 PREP §3.2 (PR #19149) |
| `theorem exists_apGapPrimeSeq_of_length_d_pos` | One-line restatement of the axiom | S4 PREP §4.1 (PR #19149) |

**Axiom signature** (verbatim from S4 PREP §3.2):

```lean
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d
```

**Bridge theorem** (one-liner; no `obtain` unpacking because F5 axiom directly
produces the tuple shape):

```lean
theorem exists_apGapPrimeSeq_of_length_d_pos
    (k : ℕ) (d : ℤ) (hd : 0 < d) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d :=
  bunyakovsky_finitary k d hd
```

The deliberate asymmetry with `exists_apGap_zero_of_length` (the `d = 0`
bridge that DOES use `obtain` + `push_cast; ring`) is documented inline:
the F5 form sidesteps the `ℤ`-cast bookkeeping that an F1 (raw-triple)
form would require for the quadratic `q n = q₀ + n*g₀ + (n.choose 2)*d.toNat`.

---

## §2 — Build verification (Docker)

Used the **mechanic-PR-overlay pattern**
(`feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`) to
verify the build despite the open parent-file unblocker PR #19074:

1. `git apply /tmp/pr19074.patch` — overlay PR #19074's 3-docstring fix
   (`/--` → `/-!` on 3 orphan blocks in `Erdos455Problem.lean` lines 54-67,
   79-82, 89-94).
2. `git checkout origin/main -- research/problems/erdos-455-oq-04/state.md
   src/data/research/problems/erdos-455-oq-04.json` — discard PR #19074's
   state.md + JSON edits (these would conflict with merging PR #19074).
3. `./proofs/scripts/docker-build.sh Proofs.Erdos455OQ04` — full Docker
   build from worktree CWD.
4. `git checkout origin/main -- proofs/Proofs/Erdos455Problem.lean` —
   revert the overlay parent fix after build success.

**Result**:

```
⚠ [3060/3061] Replayed Proofs.Erdos455Problem
warning: Proofs/Erdos455Problem.lean:129:36: unused variable `hq`
✔ [3061/3061] Built Proofs.Erdos455OQ04 (3.8s)
Build completed successfully (3061 jobs).
```

Only warning is pre-existing `unused variable hq` in parent (out of scope,
flagged in PR #19074's "Residual" section).

---

## §3 — Counts post-S4 ACT

| Metric | Pre-S4 (= post-S3) | Post-S4 (this PR) | Delta |
|---|---|---|---|
| `lineCount` | 126 | 166 | +40 |
| `theoremCount` | 4 | 5 | +1 (`exists_apGapPrimeSeq_of_length_d_pos`) |
| `defCount` (incl. structure) | 2 defs + 1 structure | unchanged | 0 |
| `sorryCount` | 0 | 0 | 0 |
| `axiomCount` | 1 (`greenTao_finitary`) | 2 (+ `bunyakovsky_finitary`) | +1 |

LOC delta is +40, slightly above the S4 PREP §4.2 estimate of +29. The
extra +11 comes from a richer docstring on the new axiom (epistemic
distinction from Green-Tao + Bateman-Horn reference) and a 6-line
asymmetry note on the bridge.

---

## §4 — Orthogonality to in-flight PRs

| PR | Status | Files touched | Conflicts with this PR? |
|---|---|---|---|
| #19074 (S3 ACT BUILD-VERIFY) | OPEN, MERGEABLE/CLEAN, 10h | `Erdos455Problem.lean` (parent), `state.md`, `JSON` | NO — disjoint Lean file; this PR does not touch state.md/JSON |
| #19149 (S4 PREP) | OPEN, MERGEABLE/CLEAN, 3h | new `sessions/2026-05-14-s4-prep-*.md` only | NO — different new session file (this PR's is `s4-act-*`) |

**This PR strictly modifies** `proofs/Proofs/Erdos455OQ04.lean` (+40 LOC)
and adds **one new session file** (`sessions/2026-05-14-s4-act-*.md`).

**This PR does NOT touch** `state.md`, `src/data/research/problems/erdos-455-oq-04.json`,
or `proofs/Proofs/Erdos455Problem.lean` — so it is safely orthogonal to
PR #19074 (which modifies state.md/JSON/parent) and PR #19149 (which adds
a different new sessions file).

Merge order is flexible: any sequence of #19074 → #19149 → this, or any
permutation, will land cleanly. The S4 ACT is logically downstream of
S4 PREP (#19149), but git-wise there is no overlap.

---

## §5 — Honesty / scope guarantee

This PR is a **strict implementation of PR #19149's §4.1 recipe**:

- **Axiom signature**: F5 predicate form — verbatim from PR #19149 §0.2 and §3.2.
- **Bridge theorem**: one-line restatement — verbatim from PR #19149 §0.3 and §4.1.
- **Docstring**: paraphrased from PR #19149 §4.1, with the additional
  inline note about why the bridge is a one-liner (F5 vs F1 asymmetry).
- **Build verification**: Docker clean, 3061 jobs, single pass.

The PR adds **no new mathematical content beyond what S4 PREP §4 already
designed**. The S4 PREP was the design memo; this is the implementation.

**Anti-overclaiming**:

- This PR does **not** claim that Bunyakovsky's conjecture is true — it
  introduces it as an axiom, on the same epistemic footing as
  `greenTao_finitary` (both honest gallery-integrity axioms).
- This PR does **not** ship any concrete `d > 0` small-witness — that
  is S6 ACT scope per S4 PREP §4.4.
- This PR does **not** update state.md or the research JSON — those
  edits are deferred to a future STATE-SYNC, post-merge of #19074 + #19149.

---

## §6 — Cross-references

- **S4 PREP** (PR #19149, OPEN): axiom signature design memo. This PR
  implements the §4.1 recipe.
- **PR #19074** (OPEN): parent-file 3-docstring v4.26.0 unblocker.
  Required for build; applied transiently via mechanic-PR-overlay.
- **S3 ACT** (PR #18851, MERGED): `greenTao_finitary` precedent for d=0.
- **S2 ACT** (PR #18590, MERGED): `eulerPoly` + `HasAPGaps` predicate +
  `APGapPrimeSeq d` structure.

### Memory references

- `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md` —
  applied here for transient parent-file fix to enable Docker-verify.
- `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md` —
  applied: pre-claim probe at session start + pre-push probe immediately
  before `git push` to detect race-window conflicts on the slug.

### Mathlib pin

`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0; same pin as
S4 PREP §6.1).
