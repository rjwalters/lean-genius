# S3 PREP — bearer audit of `density_increment_k3_explicit` + parent build blocker (doc-only)

**Date**: 2026-06-10
**Researcher**: researcher-1
**Mode**: PREP — bearer-audit + draft companion + build-blocker discovery
**Status**: doc-only. No `.lean` edits ship. The S4 ACT picker is rewritten to require a doctor/mechanic parent-file repair before any Approach A companion build can succeed.
**Predecessor**: S2 ORIENT (2026-05-31, PR #21377; researcher-1).

## §1. Bearer audit — `density_increment_k3_explicit`

S2 ORIENT recommended Approach A: ship a companion file that derives
the k = 3 specialization of the parent's `density_increment_kAP` axiom
from the already-proved `density_increment_k3_explicit` theorem. This
section inspects the bearer surface.

### §1.1 Parent file at HEAD `d8284214ed0` (this session)

The parent `proofs/Proofs/RothTheoremOQ03.lean` (419 LOC) contains:

* **Axiom (target)**: `density_increment_kAP` at line 251.

  ```lean
  axiom density_increment_kAP (N k : ℕ) [NeZero N] (hk : k ≥ 3) (hN : N ≥ 2)
      (A : Finset (ZMod N)) (δ : ℝ)
      (hδ : δ = A.card / N) (hδ_pos : 0 < δ)
      (hno_kAP : IsKAPFreeZMod A k) :
      ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
        ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
          δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' k
  ```

* **Existing k=3 explicit theorem (source)**: `density_increment_k3_explicit`
  at line 374.

  ```lean
  theorem density_increment_k3_explicit (N : ℕ) (hN : N ≥ 2)
      (A : Finset (ZMod N)) (δ : ℝ)
      (hδ : δ = A.card / N) (hδ_pos : 0 < δ)
      (hno_3AP : IsKAPFreeZMod A 3) :
      ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
        ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
          δ' = A'.card / M ∧ δ' ≥ δ + δ ^ 2 / 100 ∧ IsKAPFreeZMod A' 3
  ```

  Note the source theorem **does not require** `[NeZero N]` as an
  explicit instance argument (introduces it inline via `haveI` at line
  381 from `hN : N ≥ 2`).

### §1.2 Signature delta

| Field | Axiom (k=3 specialization) | Source theorem | Bridge needed |
|---|---|---|---|
| `[NeZero N]` instance | required | introduced internally | introduce externally via the caller-supplied instance |
| `hk : k ≥ 3` | required (with `k = 3` instantiation) | absent | drop / discharge by `Nat.le_refl 3` |
| Bound on `δ'` | `δ' > δ` | `δ' ≥ δ + δ²/100` | weaken: `δ + δ²/100 > δ` since `0 < δ²/100` (from `hδ_pos`) |
| `IsKAPFreeZMod A 3` | inputs k = 3 | inputs k = 3 | identical |
| Output shape | `∃ M _ _, ∃ A' δ', …` (3 ∃s + 3 conjuncts) | identical | identical |

The signatures are **identical** up to the weakening on the strict-vs-
explicit bound (point 3 above). The bridge is a 1-line weakening via
`linarith` after `positivity` proves `0 < δ²/100`.

### §1.3 Bridge code (draft only — does not ship)

The companion file would live at
`proofs/Proofs/RothTheoremK3OQ03Incomplete01.lean` and consist of:

```lean
import Proofs.RothTheoremOQ03

namespace RothTheoremK3OQ03Incomplete01
open RothTheoremOQ03

theorem density_increment_kAP_k3 (N : ℕ) [NeZero N] (hN : N ≥ 2)
    (A : Finset (ZMod N)) (δ : ℝ)
    (hδ : δ = A.card / N) (hδ_pos : 0 < δ)
    (hno_3AP : IsKAPFreeZMod A 3) :
    ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
      ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
        δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' 3 := by
  obtain ⟨M, hM_pos, hM_lt, A', δ', hδ', hδ'_incr, hAP'⟩ :=
    density_increment_k3_explicit N hN A δ hδ hδ_pos hno_3AP
  refine ⟨M, hM_pos, hM_lt, A', δ', hδ', ?_, hAP'⟩
  have h_sq_pos : 0 < δ ^ 2 / 100 := by positivity
  linarith
```

Total ~30 LOC including docstring and references. Approach A is
**mathematically correct and trivially proved** given a working parent.

## §2. Parent build blocker discovered (the load-bearing finding)

While running `./proofs/scripts/docker-build.sh
Proofs.RothTheoremK3OQ03Incomplete01` to verify the draft, the build
failed not in the companion but in the parent. The Docker output reports:

```
error: Proofs/RothTheoremOQ03.lean:156:10: Unknown constant `Complex.abs`
error: Proofs/RothTheoremOQ03.lean:199:72: unexpected token '/--';
       expected 'lemma'
warning: Proofs/RothTheoremOQ03.lean:339:32:
       `ZMod.natCast_zmod_eq_zero_iff_dvd` has been deprecated:
       Use `ZMod.natCast_eq_zero_iff` instead
error: Lean exited with code 1
Some required targets logged failures:
- Proofs.RothTheoremOQ03
error: build failed
```

### §2.1 Error inventory

| Site | Issue | Mathlib v4.26.0 cause | Fix surface |
|---|---|---|---|
| L156:10 `gowersNorm` | `Complex.abs` unknown | `Complex.abs` was deleted in favor of `Complex.norm` / `‖·‖` notation in v4.26.0 (consistent with the broader `Complex` API rename to use `NormedField` infrastructure) | replace `Complex.abs (…)` with `‖(…)‖` or `Complex.norm (…)` — single-token edit per occurrence |
| L199:72 `/--` after `-/` | docstring-block parse error | the block-comment terminator `-/` is immediately followed by another `/--` (stray nested-docstring start), which the v4.26.0 parser rejects as syntactically ambiguous | inspect lines 197–202 to recover the intended structure; likely one of the two block markers is stale |
| L339:32 `ZMod.natCast_zmod_eq_zero_iff_dvd` | deprecation warning only | renamed to `ZMod.natCast_eq_zero_iff` | non-blocking; rename call site for hygiene |

Neither the S2 ORIENT memo (2026-05-31) nor the parent's most recent
file commit (PR #17660, 2026-05-10, "szemeredi_from_density_increment
proved via ZMod transfer (sorry 1→0, build pending)") flagged these
issues. The PR was marked **"build pending"** at merge time — the build
was never confirmed clean. Across the 31 days since (2026-05-10 →
2026-06-10), no follow-on doctor/mechanic PR has touched the parent file
to resolve the v4.26.0 deltas.

### §2.2 Impact on Approach A

Approach A's bridge file imports `Proofs.RothTheoremOQ03`. Any consumer
of the parent's API — including this companion — inherits the parent's
build state. With the parent broken at the source level, the companion
cannot ship a build-verified PR; only a doc-only or build-pending PR
would land, neither of which advances the slug's discharge goal.

### §2.3 Impact on Approach B

Approach B (full k = 3 axiom discharge via Roth Fourier infrastructure)
is **also** blocked: the very Fourier infrastructure it would reuse
lives in the broken parent file (the `gowersNorm` definition at L156 is
the first error site). Until the parent compiles, both Approaches A and
B are blocked.

### §2.4 Approach C

Approach C (general k via Gowers norms) was already out-of-scope per S2
ORIENT (Mathlib v4.26.0 lacks top-level Gowers infrastructure). Not
affected by this finding — was already deferred.

## §3. Picker rewrite

The S2 ORIENT picker proposed:

> S3 PREP (~30–60 min, doc-only): inspect signature, draft companion,
> estimate LOC, confirm Approach A handoff.
> S4 ACT (~30–90 min): write companion file, run docker-build, ship
> build-verified.

This S3 PREP **completes** §1 (bearer audit, signature delta, draft
code) and **adds** the §2 finding that S4 ACT cannot ship until the
parent compiles. The revised picker:

| Phase | Action | Owner | Effort | Blocker |
|---|---|---|---|---|
| **S4 INFRA-RECOVER (NEW)** | Hand off the parent's three v4.26.0 deltas to doctor/mechanic | doctor / mechanic | ~10–30 min | none — small fix |
| **S5 ACT (REVISED)** | After S4, write companion file + Docker-verify ship | researcher | ~15 min (bridge code is in §1.3 above; paste-ready) | resolved by S4 |

## §4. Honest scope of this S3 PREP

* **Mathematical advance**: 0 new theorems, 0 axiom-count delta. The
  bridge code is drafted but does not ship.
* **Doc value**: the S2 ORIENT picker assumed S4 ACT could ship
  build-verified; this S3 PREP corrects that assumption with concrete
  Docker output and the §2.1 error inventory. The S4 INFRA-RECOVER
  phase is now the load-bearing next step.
* **Build verification**: attempted; failed in the parent (not the
  companion). Docker output preserved in §2 verbatim.
* **No `.lean` ship**: the draft companion file was created and tested
  locally, then reverted before commit. Only the session memo (this
  file), state.md, and JSON registry update ship.

## §5. Memory citation

Following the same pattern as similar parent-file-blocker discoveries
(e.g. `four-square-distribution-oq-01` at 2026-06-09's session log:
"parent-file blocker (87 ord_compl errors) is doctor/mechanic scope per
S28 state.md line 139; STATE-SYNC at S28 (2026-06-09) is current; no new
researcher progress possible until blocker cleared."), this S3 PREP
flags `Proofs.RothTheoremOQ03` as a doctor/mechanic-scope blocker
without attempting an in-session repair. The researcher-scope
deliverable is the doc-only memo + revised picker, not the parent
patch.

## §6. References

* **S2 ORIENT** (PR #21377, 2026-05-31, researcher-1) — discharge target
  survey + Approach A/B/C scoping.
* **Parent file last touched**: PR #17660 (2026-05-10, "szemeredi_from_
  density_increment proved via ZMod transfer (sorry 1→0, build
  pending)"). The "build pending" status was never resolved.
* **Mathlib v4.26.0** — `Complex.abs` deletion / `Complex.norm`
  promotion to canonical absolute value via `NormedField`.
