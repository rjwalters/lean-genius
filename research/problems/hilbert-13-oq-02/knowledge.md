# Knowledge: hilbert-13-oq-02

## Status: COMPLETED (verified, 0 axioms, 0 sorries)

Created `proofs/Proofs/Hilbert13OQ02.lean` — a self-contained, Mathlib-only, fully verified
account of the **provable kernel** of Hilbert #13's OQ-02 ("how hard is it to *compute* a
Kolmogorov–Arnold superposition?"). It does NOT resolve the computational question; it secures
its well-posedness by proving that the relevant complexity measure is a topological invariant.

### Proved (5 theorems, 5 defs, 0 axioms, 0 sorries)
- `covDimLE` — clean, **universe-safe** Lebesgue covering dimension: finite `Fin m` open covers,
  order via `Set.ncard` (no `DecidablePred`, no universe metavars).
- `covDimLE_succ` — monotonicity (dim ≤ n ⟹ dim ≤ n+1).
- `covDimLE_of_subsingleton` — a space with ≤1 point has covering dimension 0 (empty + one-point).
- `covDimLE_homeo_le` / `covDimLE_homeo` — **covering dimension is a topological invariant**
  (transports along any homeomorphism in both directions; no compactness/metric needed).
- `kaTermCount_invariant` — hence the KA term count `2n+1` is **presentation-independent**.

### Key gotchas
- The companion `Hilbert13GeneralSpaces.lean` does NOT compile under Mathlib 4.26.0:
  `coverOrderAt` (line 91) fails `DecidablePred` synthesis, and `covDimLE`/`covDimEq` hit
  universe-metavariable errors from `∀ (ι : Type*)` inside a Prop. **Mechanic follow-up.**
  This file therefore re-declares covering dimension from scratch with `Fin m`-indexed covers
  (Type 0 → no universe issues) and `Set.ncard` order (no decidability).
- `Set.ncard` is noncomputable → `coverOrderAt` must be marked `noncomputable def`.
- Empty-space case: build the `Fin 0` refinement with `Fin.elim0`; vacuous goals over `Fin 0`
  use `fun j => j.elim0`, vacuous goals over empty `X` use `fun x => (hX.false x).elim`.
- Order preservation under homeo is `rfl`: `{j | x ∈ e⁻¹' S j}` is defeq to `{j | e x ∈ S j}`.

### NOT addressed (open / external)
- The *computational/effective* complexity of producing a KA representation (the real OQ-02).
- The deep axioms in the companion file (Ostrand, generalized KA, Sternfeld) — not assumed here.
