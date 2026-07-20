# Knowledge Base: schroeder-bernstein-oq-03-incomplete-01

Completion task: close the residual `sorry` in `SchroederBernsteinOQ03.lean`
(Myhill's Isomorphism Theorem, 1955 — the computable Schröder–Bernstein).

## Session 2026-07-19 (researcher-1) — problem COMPLETE (stale docstrings corrected)

**Mode:** FRESH · **Outcome:** completed (no code `sorry` remains; corrected misleading docstrings)

### Finding
The residual `sorry` this completion task targets **no longer exists**. The file's hard
direction was closed via **Path C** — the computable extension-only scheduler `sigmaC f g`,
whose read-off `sigmaC_computable` (= `mLookup_computable ∘ stageListC_computable` at the fixed
computable index `2n+1`) makes `Equiv.ofBijective (sigmaC f g)` a genuine `Computable`
permutation. `myhill_isomorphism` proves both directions with **no `sorry`**. Two docstrings
were stale, still describing Path B's open computability gap ("the residual `sorry` below",
"hard direction has sorry"); these are now corrected to reflect the completed Path C.

### Verification (v4.31, host `lake exe cache get` + `lake env lean`)
- `proofs/Proofs/SchroederBernsteinOQ03.lean` (3556 lines, Mathlib.Computability imports)
  elaborates **exit 0, no `sorry`, no errors** (only benign unused-variable/section-var linter
  warnings).
- `#print axioms MyhillIsomorphism.myhill_isomorphism` and `...sigmaC_computable` →
  `[propext, Classical.choice, Quot.sound]` only. No `sorryAx`, no custom axioms.
- Gallery meta `src/data/proofs/schroeder-bernstein-oq-03/meta.json` already correctly reads
  `status: verified, sorries: 0, axiomCount: 0` — no gallery change needed.

### Next steps
- None. Pool status set to `completed`. Myhill's theorem (computable bijection from computable
  injections) is fully machine-checked.
