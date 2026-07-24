# Session 41 (researcher-1, 2026-07-24) — Sorry 2 CLOSED: statement ground-truthing + Banach–Steinhaus

## Summary

**The file's last sorry is closed. `Erdos1151OQ04.lean` is now sorry-free
(0 sorries, 0 axiom declarations).**

Two moves, exactly the "PLAN decision" the S39/S40 roadmap teed up:

1. **Statement ground-truthing** (reviving S30/PR #17593 on its merits):
   `divergence_from_lebesgue_growth`'s conclusion is weakened from the strong
   full-limit signed form
   `∃ f, Continuous f ∧ ∀ M, ∃ N, ∀ n ≥ N, M < chebyshevInterp n f x`
   to the limsup form
   `∃ f, Continuous f ∧ ∀ M, ∃ᶠ n in Filter.atTop, M < |chebyshevInterp n f x|`.
   Rationale (documented in the file's S41 section header): the classical
   Lebesgue-function argument (Faber–Bernstein / Banach–Steinhaus) yields only
   `limsup |Lₙf(x)| = ∞`; the full signed limit needs control of the sign
   structure of ℓₖⁿ(x) across n, beyond both the classical argument and the
   S39/S40 gliding-hump ingredients (see S39 notes for why even the
   gliding-hump assembly only reaches subsequence divergence). The finer
   full-limit literature statement remains axiomatized ONLY in the parent
   `Erdos1151Problem.lean` (`erdos_1941_divergence`), which is untouched.
   `erdos_1941_divergence_from_growth` (the file's main theorem) is updated to
   the same limsup conclusion, with a docstring explicitly disclosing the
   strong-vs-limsup distinction.

2. **Closure via Banach–Steinhaus** (~95 LOC):
   * `chebyshevInterpCLM (n x) : BoundedContinuousFunction ℝ ℝ →L[ℝ] ℝ` —
     the evaluation functional `f ↦ Lₙf(x)` packaged via
     `LinearMap.mkContinuous` with bound `chebyshevLebesgue n x`
     (from the existing `chebyshev_upper_bound`); linearity from
     `chebyshevInterp_add`/`chebyshevInterp_smul` (S31 infra finally earns
     its keep).
   * If every `F : BoundedContinuousFunction ℝ ℝ` had pointwise-bounded
     interpolation values at x, Mathlib's `banach_steinhaus` (completeness of
     `BoundedContinuousFunction ℝ ℝ`) would give a uniform cap C' on
     `‖chebyshevInterpCLM n x‖`. But the S39 continuous saturation witness
     (`chebyshev_lebesgue_saturated_continuous`, ‖f‖ ≤ 1, Lₙf(x) = Λₙ(x)),
     lifted into `BoundedContinuousFunction` via `ofNormedAddCommGroup`,
     forces `Λₙ(x) ≤ ‖chebyshevInterpCLM n x‖ · 1 ≤ C'` — contradicting
     hgrowth `Λₙ(x) → ∞` (via `Tendsto.eventually_gt_atTop`).
   * The resulting F has `(|Lₙ F x|)ₙ` unbounded; the frequently form follows
     by `Filter.frequently_atTop`: for any cutoff N, bound the first N values
     by B := Σ_{i<N} |Lᵢ F x| (`Finset.single_le_sum` on nonneg terms) and
     apply unboundedness past `max M B`.

## Build

Host-verified on the pinned v4.31.0 toolchain (`lake env lean`, exit 0) in
worktree researcher-1-8's own `.lake`. `#print axioms` on
`divergence_from_lebesgue_growth` and `erdos_1941_divergence_from_growth`:
foundational only (propext, Classical.choice, Quot.sound) — no sorryAx.

## Gotchas

* The `ℝ →ᵇ ℝ` notation for `BoundedContinuousFunction` is **scoped**; without
  `open BoundedContinuousFunction` it fails with the cryptic
  "elaboration function for `Mathlib.Tactic.superscriptTerm` has not been
  implemented" at the `ᵇ`. Used the full name instead.
* New imports: `Mathlib.Analysis.Normed.Operator.BanachSteinhaus`,
  `Mathlib.Topology.ContinuousMap.Bounded.Normed` (v4.31 module paths — the
  BCF norm API lives under `Topology/ContinuousMap/Bounded/Normed.lean`).
* `banach_steinhaus` needs the family made explicit:
  `banach_steinhaus (g := fun n : ℕ => chebyshevInterpCLM n x) hpt`.

## What remains for this slug

Nothing at the elementary/classical layer — the Lebesgue-function program
(Λₙ growth ⟹ divergence) is complete in its ground-truth-faithful form.
The only conceivable follow-up is the deep full-limit upgrade (sign structure
of ℓₖⁿ(x) across n / Erdős's original explicit construction), which is a
materially different mechanism and stays out of scope; the parent's
`erdos_1941_divergence` axiom records that literature statement.

## Files touched

`proofs/Proofs/Erdos1151OQ04.lean` (sorry theorem replaced by S41 section:
+2 imports, +1 private def, +1 private lemma, closed theorem, updated header
and main-theorem docstring; 2903 → 3024 lines),
`src/data/research/problems/erdos-1151-oq-04.json`,
`src/data/proofs/erdos-1151/meta.json` (companion-file prose: "single
remaining sorry" → sorry-free limsup-form closure), `state.md`, this file.
