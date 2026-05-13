# State: sqrt2-plus-sqrt3-irrational-oq-01

**Phase**: COMPLETED (S2 ACT build-verified, S3 GALLERY shipped, S4 PREP sibling-slug seeded)
**Iteration**: 4 (S1 OBSERVE, S2 PREP, S2 ACT, S3 GALLERY, S4 PREP)
**Last session**: S4 PREP (2026-05-13) — Besicovitch sibling-slug design memo
**Tier**: B
**Tractability**: 7 / Significance: 6

## Completion summary (STATE-SYNC, 2026-05-13)

OQ-01 ("Is `√2 + √3 + √5` irrational?") is **answered affirmatively
and formalized** in Mathlib v4.26.0 via the "isolate `√30` by squaring
twice" tactic. The full deliverable chain is on `main`:

| Stage | PR | Merge (UTC) | Artifact |
|---|---|---|---|
| S1 OBSERVE | [#18222](https://github.com/rjwalters/lean-genius/pull/18222) | 2026-05-12T22:20:41Z | scaffold (problem.md, knowledge.md, state.md, JSON) |
| S2 PREP | [#18353](https://github.com/rjwalters/lean-genius/pull/18353) | 2026-05-12T23:17:45Z | annotated Lean draft + quartic-identity tactic chain |
| S2 ACT | [#18369](https://github.com/rjwalters/lean-genius/pull/18369) | 2026-05-13T02:11:30Z | `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (144 LOC, 5 theorems, 0 sorries, 0 axioms; build verified) |
| S3 GALLERY | [#18538](https://github.com/rjwalters/lean-genius/pull/18538) | 2026-05-13T04:08:24Z | `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/{meta,annotations,index}` (status verified, 5 theorems, 0 axioms) |
| S4 PREP | [#18402](https://github.com/rjwalters/lean-genius/pull/18402) | 2026-05-13T02:09:38Z | Besicovitch (1940) sibling-slug design memo (seeds `sqrt2-plus-sqrt3-irrational-oq-02`) |

The originally proposed S3 GALLERY under `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/`
landed under the **theorem-named sibling slug** (not under
`sqrt2-plus-sqrt3-irrational-oq-01/`), which is consistent with the
gallery convention of naming entries by their main theorem rather than
the parent OQ. Cross-references in that gallery entry point back to
this OQ slug.

Besicovitch (1940) general-k formalisation is **out of scope** for this
slug going forward — the seeded successor is
`sqrt2-plus-sqrt3-irrational-oq-02` (per S4 PREP #18402).

## Session log

### S1 (researcher-8, 2026-05-12) — OBSERVE

**Deliverable**: 4 scaffold files (problem.md, knowledge.md,
state.md, src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-01.json).
No Lean code modified.

**Findings**:
- Proof strategy fixed: **isolate √30 by squaring twice**.
  Concretely α := √2+√3+√5, then (α-√5)² = 5+2√6 (reuses parent's
  `sqrt2_plus_sqrt3_sq`), rearrange α² = 2α√5 + 2√6, square again
  to get α⁴ - 20α² - 24 = 8α · √30. Since α > 0 we can divide and
  conclude √30 ∈ ℚ — contradiction (30 not perfect square).
- Mathlib v4.26.0 ships all needed machinery: `irrational_sqrt_natCast_iff`,
  `sq_sqrt`, `sqrt_mul`, `sqrt_pos`, plus the parent identity from
  `Proofs/Sqrt2PlusSqrt3Irrational.lean`.
- Floating-point sanity check (Python): α⁴ - 20α² - 24 ≈ 235.3 ≈
  8α · √30 — matches within 1e-10 relative error.
- Pristine slug at S1 time: 0 PRs ever with this slug in title;
  8h after seeker creation, well past saturation window.

### S2 (researcher-4, 2026-05-12) — ACT ✅ build verified

**Deliverable**: `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`
(145 lines, 0 sorries, 0 axioms) + registration in `proofs/Proofs.lean`.
PR #18369.

**All 4 theorems proven (+ 1 private bridge)**:

1. `irrational_sqrt_thirty` — `irrational_sqrt_natCast_iff.mpr` + `native_decide` on `¬IsSquare (30 : ℕ)`.
2. `alpha_pos : 0 < sqrt 2 + sqrt 3 + sqrt 5` — `linarith` from `sqrt_nonneg` × 2 + `sqrt_pos.mpr`.
3. `sqrt5_mul_sqrt6 : sqrt 5 * sqrt 6 = sqrt 30` (private bridge) — `← Real.sqrt_mul` + `norm_num`.
4. `alpha_quartic_identity : α⁴ - 20·α² - 24 = 8·α·√30` — parent identity `sqrt2_plus_sqrt3_sq` + `Real.sq_sqrt` × 2 + `sqrt5_mul_sqrt6` + `ring` + `linarith`. Substantive ~25-line proof following the S2 PREP plan locked in by PR #18353.
5. `irrational_sqrt2_plus_sqrt3_plus_sqrt5` (main) — `intro ⟨r, hr⟩`, divide quartic identity by 8α, construct rational witness `(r⁴ - 20r² - 24)/(8r)` for `√30`, contradict (1).

**Build verification**:
- `./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` → "Build completed successfully (3060 jobs)"
- Only warning: deprecation of `Mathlib.Data.Real.Irrational` (matches parent file).
- Log: `.loom/logs/build-researcher-4-sqrt2sqrt3sqrt5-s2.log`.

**Key technique**: the S2 PREP iteration (PR #18353) traded `nlinarith` (which fails on cross-radical products) for an explicit two-substitution + `linarith` chain. This was the proof-of-existence for the strategy and made S2 ACT mechanical.

### S3 (next) — GALLERY

**Goal**: implement
`proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`
(~80 lines, 0 sorries, 0 axioms) containing:

1. `irrational_sqrt_thirty : Irrational (sqrt 30)` — one-liner from
   `irrational_sqrt_natCast_iff.mpr` + `native_decide`.
2. `alpha_pos : 0 < sqrt 2 + sqrt 3 + sqrt 5` — `linarith` from
   three `sqrt_nonneg` + `sqrt_pos.mpr` on √5.
3. `alpha_quartic_identity : α⁴ - 20*α² - 24 = 8*α * sqrt 30` —
   the algebra. Expected ~25 lines: `ring_nf`, then rewrite each
   `(√k)²` and √a·√b cross term, then `ring`.
4. `irrational_sqrt2_plus_sqrt3_plus_sqrt5 : Irrational (sqrt 2 + sqrt 3 + sqrt 5)`
   — main theorem. Assume `⟨r, hr⟩`, derive
   `sqrt 30 = (r^4 - 20*r^2 - 24) / (8 * r)`, exhibit a rational
   witness, contradict `irrational_sqrt_thirty`. Closely modeled on
   the parent's `irrational_sqrt2_plus_sqrt3` proof.

Register in `proofs/Proofs.lean`. Verify build via
`./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01`.

### S3 (legacy) — GALLERY

Create `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/`:
- `meta.json` — verified badge, 4 theorems, 0 axioms, ~80 lines.
- `annotations.json` — section ranges for the 4 theorems.
- `index.ts` — exports.

Cross-references:
- `parent` → `sqrt2-plus-sqrt3-irrational` (2-summand parent).
- `related` → `sqrt2-plus-sqrt3-irrational-oq-03` (minimal poly of
  √2+√3; sibling open question on the same parent).

### S4 (stretch) — Besicovitch hook

Open the door for a future Besicovitch-1940 formalisation: define
the squarefree triple predicate and state the 3-summand
generalisation as a `theorem ... := by sorry` companion in a new
slug `sqrt2-plus-sqrt3-irrational-oq-02` (Besicovitch general form).

## Open questions / blockers

None. S2 implementation is mechanical: parent's
`Sqrt2PlusSqrt3Irrational.lean` provides the template, all required
Mathlib lemmas confirmed available, and the proof structure is fixed
in problem.md.

## Race-risk monitoring

- **S1 push (this session)**: low risk, 0 PRs ever for this slug.
- **S2 push (next session)**: re-probe
  `gh pr list -R rjwalters/lean-genius --state all --search
  "in:title sqrt2-plus-sqrt3-irrational-oq-01"` immediately before
  push. If any S2 PR appears in the interim, narrow scope to a
  unique deliverable (e.g. just the quartic identity, or just the
  Besicovitch hook).
