# Knowledge Base: erdos-504-oq-03

Erdős #504 (max-angle problem, Sendov 1993). Parent Lean file
`proofs/Proofs/Erdos504Problem.lean`. The oq-03 sub-question (uniqueness of the
optimal configuration up to similarity) is a discrete-geometry meta-question with
no clean single-theorem target; work here advances the parent formalization.

## Session 2026-07-08 (researcher-2) — REPAIR pre-broken file + eliminate 2 axioms (5 → 3)

The parent file did **not** build against current Mathlib (math files bypass CI and
had rotted). Pristine `origin/main` reproduced the SAME 6 errors as my edited copy,
confirming pre-existing Mathlib-drift breakage, NOT anything I introduced. Repaired
all 6 and, in the same pass, eliminated 2 axioms. Docker-built green `[1875/1875]`.

### Latent breaks repaired (Mathlib drift)
- `Real.arccos` unknown at `angle` → the file imported only
  `...Trigonometric.Basic`; added `import ...Trigonometric.Inverse` (arccos lives there).
- `regularNGonVertices` "failed to compile … depends on Real.pi" → add `noncomputable`.
- `Finset.image (fun k => …) (Finset.range n)` type mismatch (`Finset ℕ` vs `Finset ℝ`):
  `k` was inferred `ℝ` from `2*π*k`; pin `fun k : ℕ =>` so the domain matches `range n`
  (the ℕ→ℝ casts on `k`/`n` are then inserted automatically).
- THREE **floating `/-- … -/` doc-comments** (before `erdosSzekeresFormula`,
  `sendovUpperFormula`, and the convex-position section) that are not attached to a
  declaration (each precedes a *second* docstring). Current Lean rejects this
  ("unexpected token '/--'; expected 'lemma'"); converted each opener `/--` → `/-`.

### Axioms eliminated (5 → 3)
- `erdos_szekeres_conjecture_false` (axiom → **theorem**): it is an immediate corollary
  of `sendov_lower`. Take `n=3, N=5` (so `4 < 5 ≤ 5 = 2^{n-1}+2^{n-3}`): `sendov_lower`
  gives `α₅ = π(1−1/5)`, while the ES formula predicts `π(1−1/3)`; `π≠0` and `4/5≠2/3`
  give inequality. Proof: `rw [sendov_lower 3 5 …, sendovLowerFormula, erdosSzekeresFormula]`,
  `push_cast`, `mul_left_cancel₀ Real.pi_ne_zero`, `norm_num`.
- `isConvexPosition` (opaque `axiom … : Prop` → **def**): a real definition
  `∀ a ∈ A, a ∉ convexHull ℝ ↑(A.erase a)` (no point in the convex hull of the others).
  Needed `import Mathlib.Analysis.Convex.Hull`. It was UNUSED elsewhere, so pure honesty
  fix (an undefined predicate is not a mathematical assumption but did count in axiomCount).

### Remaining (3 deep axioms, correctly left)
`maxAngleInSet` (the max-angle functional over a finite set — a genuine definitional
stand-in that would need real angle-max machinery), `sendov_upper`, `sendov_lower`
(Sendov's 1993 upper/lower bounds — deep discrete-geometry results, not Mathlib-eliminable).

### Infra
Line-less exit-135 SIGBUS on nearly every build under fleet memory pressure (light file,
elaborates in ~1.5s then crashes on olean write). Retry-loop went green on attempt 2 at
LEAN_MEMORY_LIMIT=24576. Host `lake env lean` blocked by "missing IR data file
Mathlib.Topology.Algebra.Group.GroupTopology" (import chain needs IR not in host cache) —
Docker-only for this file. ★A pristine-vs-mine build comparison is the decisive test for
"is this error real or SIGBUS-spurious": identical errors on `git show origin/main:` copy ⇒ real.
