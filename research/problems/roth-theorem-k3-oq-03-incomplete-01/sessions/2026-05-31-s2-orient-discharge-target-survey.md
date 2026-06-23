# S2 ORIENT — discharge target survey (doc-only)

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: Doc-only S2 ORIENT (zero `*.lean` edits). Three files:
this session memo, `state.md` (full rewrite from iter-1 OBSERVE to
iter-2 ORIENT), `src/data/research/problems/roth-theorem-k3-oq-03-incomplete-01.json`.

## §1. Parent file survey

* **Parent**: `proofs/Proofs/RothTheoremOQ03.lean` (per
  `src/data/proofs/roth-theorem-k3-oq-03/meta.json`
  `proofRepoPath`).
* **Parent meta**: status `axiomatized`, badge `axiom`, sorries 0
  (the problem.md's claim of "1 sorry + 2 axioms" is stale and
  inaccurate per the current meta — corrected here as 0 sorries +
  1 axiom).
* **Single axiom found**: `density_increment_kAP` at line 251 of
  `RothTheoremOQ03.lean`. Signature:
  ```lean
  axiom density_increment_kAP (N k : ℕ) [NeZero N] (hk : k ≥ 3) (hN : N ≥ 2)
      (A : Finset (ZMod N)) (δ : ℝ)
      (hδ : δ = A.card / N)
      (hδ_pos : 0 < δ)
      (hno_kAP : IsKAPFreeZMod A k) :
      ∃ (M : ℕ) (_ : 0 < M) (_ : M < N),
        ∃ (A' : Finset (ZMod M)) (δ' : ℝ),
          δ' = A'.card / M ∧ δ' > δ ∧ IsKAPFreeZMod A' k
  ```
* **Parent's own roadmap** (parent file lines 240-242):
  - For k=3: `g(δ) = δ²/100` (explicit, from Fourier analysis).
  - For k≥4: `g(δ) = c(δ, k)` (non-explicit, depends on inverse
    theorem bounds).
* **Sibling** `density_increment_k3_explicit` exists in the parent
  (referenced at line 274). This proves the k=3 case via Fourier
  analysis without axiom.

## §2. Discharge target recovery

The slug `roth-theorem-k3-oq-03-incomplete-01` ambiguously targets
"k-AP density increment via Gowers norms" per the existing problem.md.
The single parent axiom `density_increment_kAP` is the natural target.

**Two viable interpretations**:

1. **Interpretation A (k=3 case only)**: discharge the k=3 specialisation
   `density_increment_kAP N 3 _ _ A δ _ _ _` by appealing to the
   already-proved `density_increment_k3_explicit` (no axiom needed for
   k=3, just a small bridge).
2. **Interpretation B (general k via U^{k-1} Gowers norm)**: discharge
   the full axiom via the Gowers-norm density-increment machinery (the
   problem.md's `U^3` formal statement points this way — `U^3` is the
   k=4 case in standard notation).

The problem.md formal statement
`‖f‖_{U^3} ≥ δ ⇒ ∃ density increment on progression` is the **Gowers
inverse theorem direction** that powers Interpretation B for k=4
(since k-AP counting operators decompose into `U^{k-1}`).

**Recommended for S3 PREP**: pick Interpretation A first (much smaller,
discharges the k=3 case using existing parent infrastructure
`density_increment_k3_explicit`). Defer Interpretation B to a separate
follow-on slug.

## §3. Mathlib status (v4.26.0, lake-manifest pin `2df2f0150c`)

* **Available**: `Finset (ZMod N)`, `IsKAPFreeZMod` (parent-defined),
  `Real.inner` / `MeasureTheory.integral` (for Fourier analysis if needed),
  `Polynomial.Fourier` / `ZMod.charFun` (partial Fourier infrastructure).
* **Possibly available**: a `GowersNorm` or `gowersNorm` definition —
  needs S3 PREP grep verification.
* **Not available** (likely): top-level `GowersInverseTheorem`,
  `density_increment_from_gowers_norm`. Mathlib's additive-combinatorics
  development has Roth via Fourier (k=3) but no published Gowers-norm
  machinery for k≥4 at v4.26.0.

## §4. Approach survey

1. **Approach A — k=3 bridge** (~30-50 LOC, low risk): companion file
   `RothTheoremK3OQ03Incomplete01.lean` that derives the k=3 case of
   `density_increment_kAP` from `density_increment_k3_explicit`,
   yielding a `theorem density_increment_kAP_k3 := …`.
2. **Approach B — k=3 axiom discharge via existing Roth infrastructure**
   (~150-300 LOC, moderate risk): discharge the full `density_increment_kAP`
   axiom for the k=3 specialisation by re-applying parent's `RothTheorem.lean`
   results (Fourier inversion + L^2 bounds + density increment chain).
3. **Approach C — general k via Gowers norms** (~500+ LOC, very high
   risk): full discharge of `density_increment_kAP` for all k ≥ 3 via
   Gowers-norm machinery. Out of scope for this slug; defer to a
   separate follow-on.

**Recommended**: Approach A first (smallest LOC, leverages existing
`density_increment_k3_explicit`). Fall back to B if A's bridge proves
brittle.

## §5. Tractability re-calibration

Original scaffold: significance 7, tractability 5. This S2 ORIENT keeps
significance 7 (the slug targets a real axiom discharge for a
classically-important k=3 case) but adjusts tractability:

* Approach A: tractability **7** (small bridge from existing parent
  theorem).
* Approach B: tractability 4.
* Approach C: tractability 2 (very high LOC, requires Mathlib Gowers
  infrastructure that doesn't exist).

**Net recommendation**: tractability 7 if scope-restricted to
Interpretation A (k=3 bridge); 4 if scope-expanded to full discharge.

## §6. Files modified (S2 ORIENT)

* `research/problems/roth-theorem-k3-oq-03-incomplete-01/sessions/2026-05-31-s2-orient-discharge-target-survey.md`
  (this memo, ~90 LOC).
* `research/problems/roth-theorem-k3-oq-03-incomplete-01/state.md`
  (full rewrite from iter-1 OBSERVE to iter-2 ORIENT; preserves no
  prior content since scaffold).
* `src/data/research/problems/roth-theorem-k3-oq-03-incomplete-01.json`
  (`phase` OBSERVE → ORIENT, `currentState.iteration` 1 → 2,
  `lastUpdated` → 2026-05-31, etc.).

## §7. Next action — S3 PREP

1. Verify `density_increment_k3_explicit` signature and proof shape in
   `RothTheoremOQ03.lean` (location TBD).
2. Draft companion file structure:
   `proofs/Proofs/RothTheoremK3OQ03Incomplete01.lean`.
3. Identify Mathlib bearer cluster for the k=3 specialisation bridge.
4. Estimate concrete LOC for Approach A.

Doc-only, ~30-60 min.

## §8. Honest scope

This S2 ORIENT converts a 2-month-stale scaffold into a usable
ORIENT-phase memo. No Lean edits, no axiom changes, no proof attempt.
The next iteration (S3 PREP) is the load-bearing one for any concrete
discharge attempt.
