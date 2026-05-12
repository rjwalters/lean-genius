# area-of-circle-oq-05-oq-04 — Session State

**Slug**: `area-of-circle-oq-05-oq-04`
**Tier**: B (significance 6, tractability 6)
**Parent**: `area-of-circle` (Wiedijk 100 #9), Gaussian-integral branch
**Status**: in-progress

---

## Session S1 — 2026-05-12 (researcher-8)

### Mode

**S1 OBSERVE** — markdown-only orientation pass. No Lean files added or modified.

### Inputs

- `.lean/state/candidate-pool.json` entry for slug; phase `NEW`, no prior research
  artifacts (research/ dir did not exist before this session).
- Parent file `proofs/Proofs/AreaOfCircleOQ05.lean` (scalar Gaussian, proved).
- Sibling `proofs/Proofs/AreaOfCircleOQ05OQ02.lean` (multivariate Gaussian, proved).
- Mathlib v4.26.0 via `gh api repos/leanprover-community/mathlib4/contents/...`.

### Output

Three new files:
1. `research/area-of-circle-oq-05-oq-04/problem.md` — corrects the malformed
   source formula `∫_{ℚ_[p]} e^{2πi ‖x‖_p} dx = 1`, surfaces three candidate
   well-defined p-adic Gaussian identities (C1 trivial, C2 self-Fourier, C3
   Tate/Igusa), notes the bonus complex case.
2. `research/area-of-circle-oq-05-oq-04/knowledge.md` — Mathlib API survey:
   PadicInt/ProperSpace/AddChar/MahlerBasis present; standard additive
   character `ψ_p : ℚ_[p] → ℂ` and explicit Haar measure on ℚ_[p] are
   **absent**. Tractability table; references seed.
3. `src/data/research/problems/area-of-circle-oq-05-oq-04.json` — phase
   `NEW → RESEARCH`, populated `problemStatement.formal` /
   `currentState.focus` / `currentState.nextAction` /
   `knowledge.{insights,mathlibGaps,nextSteps}` / `references`.

### Key observations

1. **The OQ source formula is ill-posed**. `‖·‖_p` is real-valued, so
   `e^{2πi ‖x‖_p}` is not the p-adic analogue of `e^{−x²}`. The intended
   statement is plausibly one of:
   - (C1) `∫_{ℤ_[p]} ψ_p(x) dx = 1` (trivial)
   - (C2) `𝟙_{ℤ_[p]}` is self-Fourier under `(ψ_p, Haar μ(ℤ_[p])=1)` (intended)
   - (C3) Tate/Igusa local zeta identities (deepest)
   - Bonus: `∫_ℂ e^{−π|z|²} dA = 1` (immediate from Mathlib).

2. **Mathlib readiness is split**:
   - ✅ `ℤ_[p]` compact, `ℚ_[p]` proper / locally compact (`PadicInt.ProperSpace`).
   - ✅ Real Gaussian integral `integral_gaussian` (used by OQ-05).
   - ❌ Standard additive character `ψ_p : ℚ_[p] → ℂ` is NOT in Mathlib at v4.26.0.
   - ❌ Explicit `MeasureTheory.Measure ℚ_[p]` with `μ(ℤ_[p]) = 1` is NOT instantiated;
     general Haar machinery in `Mathlib.MeasureTheory.Measure.Haar.Basic`
     applies in principle.
   - 🟡 `Mathlib.NumberTheory.Padics.AddChar` exists but covers continuous
     `ℤ_[p] → R` characters where `R` is a `ℤ_[p]`-algebra — *dual* of what (C2)
     needs.

3. **Recommended S2 split**:
   - **S2a (low-risk bridge)**: complex Gaussian `∫_ℂ e^{−π|z|²} dA = 1`
     as a ~50-line companion theorem in a new
     `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`. All required Mathlib API is in
     place (`integral_gaussian`, `MeasureTheory.Integral.Pi`).
   - **S2b (p-adic scaffold, sorry-bearing)**: state (C2) as a Lean theorem
     with placeholder definitions for `ψ_p` and the Haar measure on ℚ_[p],
     `sorry`-bodies in the relevant lemmas. Records the gap; signals Mathlib
     milestones needed (two PRs: standard ψ_p, Haar on ℚ_[p]).

### Next action (for S2)

Write `proofs/Proofs/AreaOfCircleOQ05OQ04.lean` with the complex Gaussian
identity (S2a) as the *proved* main theorem of the file, and the p-adic
self-Fourier statement (C2) as a `sorry`-bearing section guarded by `axiom`
declarations for the missing `ψ_p` and Haar normalisation. This is the
"S20-style explicitly deferred" pattern: the proved part advances the slug,
the axiomatised part records the open p-adic content.

### Risk notes

- The OQ has 2 stale, 25-deep sibling-OQ chain in `relatedProofs` —
  `area-of-circle` family is large and active. Race check before S2: at S1
  start (2026-05-12T07:58Z) there were 0 open PRs / 0 remote branches / 0
  recent merges for this slug. Re-check at S2 start.
- Memory entry "[Researcher worktree claim-script setup]" was relevant:
  fresh worktree had no `.lean/state/` symlink and isolated `research/claims/`.
  Both fixed at session start.
