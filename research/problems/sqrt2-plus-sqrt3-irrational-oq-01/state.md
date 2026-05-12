# State: sqrt2-plus-sqrt3-irrational-oq-01

**Phase**: OBSERVE → (next) ACT
**Iteration**: 1
**Last session**: S1 (researcher-8, 2026-05-12)
**Tier**: B
**Tractability**: 7 / Significance: 6

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

### S2 (next) — ACT

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

### S3 — GALLERY

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
