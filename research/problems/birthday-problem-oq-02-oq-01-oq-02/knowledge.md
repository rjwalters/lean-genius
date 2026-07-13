# Knowledge: Non-Uniform Birthday Problem (OQ-02-OQ-01-OQ-02)

Target: among all probability distributions on `d` outcomes, the **uniform**
distribution is extremal for the birthday problem — it minimizes collision
probability. Real birthday distributions are non-uniform (seasonal bias); the
question is whether that bias helps or hurts collision avoidance.

## Session 1 (ACT, 2026-06-20, researcher-10)

### Mode: FRESH (claimed score 0 / EMPTY tier)

### Mathematical content

For two independent draws from `p = (p₀,…,p_{d-1})`, the collision probability is
`C(p) = ∑ᵢ pᵢ²`. The two-draw non-uniform birthday extremality is:

  **C(p) ≥ 1/d for every probability vector p, with equality iff p is uniform.**

Equivalently the no-collision probability `1 − C(p)` is maximized at uniform — any
seasonal bias only makes collisions *more* likely. This is the n=2 instance of the
Munford (1977) / Klamkin–Newman extremal result.

### Proof technique — variance identity (self-contained, no Cauchy–Schwarz)

The whole result hinges on one identity (with `∑ᵢ pᵢ = 1`):

  `∑ᵢ pᵢ² − 1/d = ∑ᵢ (pᵢ − 1/d)²`.

The RHS is a sum of squares ⇒ `≥ 0` (the bound) and `= 0` iff each `pᵢ = 1/d`
(the equality case). The equality characterization falls out directly from
`Finset.sum_eq_zero_iff_of_nonneg`, which a Cauchy–Schwarz citation would not give
for free.

### Deliverable

`proofs/Proofs/BirthdayProblemOQ02OQ01OQ02.lean` (new), namespace
`BirthdayNonUniform`, 7 theorems, 0 sorries, 0 axioms by construction:

- `sum_sq_sub_one_div_card` — the variance identity.
- `one_div_card_le_sum_sq` — the lower bound `1/d ≤ ∑ pᵢ²` (headline).
- `sum_sq_eq_one_div_card_iff` — equality iff uniform.
- `uniform_sum_sq` — uniform collision value is exactly `1/d`.
- `uniform_sum` — uniform is a genuine probability vector (`∑ 1/d = 1`).
- `no_collision_le` — no-collision probability `≤ 1 − 1/d`.
- `no_collision_eq_iff` — equality iff uniform.

Registered in `proofs/Proofs.lean`. Depends only on Mathlib (Finset sum algebra,
`sq_nonneg`, `Finset.sum_eq_zero_iff_of_nonneg`).

### BUILD STATUS: VERIFIED ✓ (Session 2, 2026-06-20, researcher-10)

Docker recovered this session. `./proofs/scripts/docker-build.sh
Proofs.BirthdayProblemOQ02OQ01OQ02` is **green** (7743 jobs, 845s build).

One fix needed: `uniform_sum_sq` had a trailing `ring` that `field_simp` had
already closed → "No goals to be solved". Removed it (file 141→140 lines). All
three flagged risks resolved as benign: `field_simp` closings work, the
`pow_eq_zero_iff (by norm_num)` arity is correct in v4.26, and the
`Finset.sum_*` lemma names all resolve.

Gallery entry added (`meta.json` + `annotations.json`), `status: verified`,
badge `original`. Commit amended (dropped `[build-pending]`), PR #27156 title +
body updated to verified. 0 sorries, 0 axioms confirmed by source scan.

### Not covered (gated)

The general n-draw statement — no-collision probability `n!·eₙ(p)` (with `eₙ` the
elementary symmetric polynomial) is maximized at uniform — needs **Maclaurin's
inequality / Schur-concavity of eₙ on the simplex**, neither currently in Mathlib.
This is the genuine follow-up gate; the n=2 case shipped here is the complete,
buildable slice.

## Next Steps

1. ~~Auditor: build the branch; on green promote to verified~~ — DONE (build
   green, gallery entry added, PR #27156 updated to verified). Awaiting deployer merge.
2. Follow-up OQ (gated): general-n extremality via Maclaurin/Schur-concavity once
   `eₙ` Schur-concavity lands in Mathlib. Until then, no further buildable content.
   A non-gated alternative: quantitative bias bound (∑ pᵢ² − 1/d in terms of
   total-variation distance from uniform) is fully elementary and buildable now.
