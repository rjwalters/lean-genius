# Knowledge Base: erdos-116-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-20 (researcher-1) — bare stub → axiom-free foundational core

**Mode**: FRESH (knowledge score 0). **Outcome**: progress (6 theorems, axiom-free), host-verified v4.31.

**Finding**: `Erdos116Problem.lean` had real definitions but **zero theorems**, yet the gallery
meta (`proofStrategy`, `conclusion`) described "four bounds stated as axioms" and a main theorem
`ErdosProblem116` — none of which existed in the source (an overclaim). Fixed both the Lean file and
the prose.

**Added (proofs/Proofs/Erdos116Problem.lean, all 0-axiom, `#print axioms` = propext/Classical.choice/Quot.sound):**
- `UnitDiskPoly.eval_root_eq_zero` — `p(zᵢ)=0` (a factor vanishes); proof `Finset.prod_eq_zero (mem_univ i) (by simp)`.
- `UnitDiskPoly.root_mem_sublevelSet` — every root ∈ `{|p|<1}` (|0|=0<1).
- `UnitDiskPoly.sublevelSet_nonempty` (n>0) — witness `roots ⟨0,hn⟩`.
- `UnitDiskPoly.eval_of_degree_zero` — `n=0 ⟹ p ≡ 1` (empty product).
- `UnitDiskPoly.sublevelSet_of_degree_zero` — `n=0 ⟹ {|p|<1} = ∅` (|1|=1 ≮ 1). The boundary case
  making the `n>0` hypothesis essential.
- `UnitDiskPoly.sublevelMeasure_nonneg` — `0 ≤ μ` (`ENNReal.toReal_nonneg`).

**Gotcha**: file has no namespace (`namespace: null`); shim `noncomputable def Complex.abs (z) := ‖z‖`
for v4.31 (`Complex.abs` removed). `simp [Complex.abs]` unfolds the shim; `Complex.abs 0` → `‖0‖` → `0`.

**Meta synced**: theoremCount 0→6 (both `.meta` and `.leanFile`), lineCount 74→124, imports→`["Mathlib"]`,
`assumptions`/`proofStrategy`/`conclusion` rewritten to stop referencing non-existent axioms/`ErdosProblem116`.

**Still open (Mathlib infra gap)**: the four deep bounds (Pommerenke `c/n⁴`, KLR `c/log n` & `C/loglog n`,
Pólya `π`) need logarithmic-potential / planar-measure-of-lemniscate machinery absent from Mathlib v4.31.
Next foundational step: prove `sublevelSet` is open/measurable (`p` continuous).
