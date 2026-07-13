# Open Mapping & Closed Graph theorems from the gallery Baire theorem

**Candidate:** baire-category-theorem-oq-01-oq-01-oq-01
**Status:** COMPLETED (verified, 0 axioms, 0 sorries)
**Lean file:** `proofs/Proofs/BaireCategoryTheoremOQ01OQ01OQ01.lean`
**Gallery:** `src/data/proofs/baire-category-theorem-oq-01-oq-01-oq-01/`

## Summary

Resolves the lead open question of the sibling Banach–Steinhaus entry
(`baire-category-theorem-oq-01-oq-01`): derive the **open mapping**, **inverse
mapping (Banach isomorphism)** and **closed graph** theorems for Banach spaces from
the *same* gallery Baire category theorem
(`BaireCategoryTheoremOQ01.baire_nonempty_interior`), completing the three classical
Baire-powered pillars of linear functional analysis in the gallery.

## Session 2026-06-26 (Session 1) — FRESH, COMPLETED

**Mode:** FRESH
**Outcome:** completed

### What I Did
- Selected this EMPTY-tier available candidate; the only candidate whose notes describe
  a clean Mathlib-instantiable target (open mapping + closed graph from Baire). An
  abandoned local branch `research/baire-open-mapping-closed-graph` had 0 commits, so
  the candidate was effectively free.
- Studied Mathlib's `Mathlib/Analysis/Normed/Operator/Banach.lean`: the Baire step is
  `exists_approx_preimage_norm_le` using `nonempty_interior_of_iUnion_of_closed`, which
  the gallery re-exports verbatim as `baire_nonempty_interior`.
- Reproduced the classical chain (approx-preimage → series → open map → inverse map →
  closed graph) in a fresh namespace, specialized from Mathlib's semilinear `→SL[σ]` to
  plain `→L[𝕜]`, routing the single Baire call through the gallery theorem.
- Docker build-verified: `✔ [7744/7744] Built Proofs.BaireCategoryTheoremOQ01OQ01OQ01`,
  0 sorries, 0 axioms, 256 lines, 5 theorems.

### Key Findings
- The gallery Baire theorem is genuinely load-bearing: exactly one Baire invocation, in
  `exists_approx_preimage_norm_le`; all later steps are completeness bookkeeping.
- Porting gotchas (cost two build cycles): (1) `gcongr` in the K norm-bound calc emitted
  side goals in an order the bullets didn't match — replaced with explicit `mul_le_mul`;
  (2) `IsOpenMap f` unfolds to `∀ U, IsOpen U → IsOpen (f '' U)` with `U` **explicit**,
  so the set must be passed (`isOpenMap T surj s hs`, mirroring Mathlib's `continuous_symm`);
  (3) `LinearEquiv.image_eq_preimage` is phrased via `toAddEquiv.symm` and won't rewrite
  `⇑e.symm` — used an explicit `e.symm ⁻¹' s = e '' s` ext proof instead.
- Infrastructure: host was severely memory-contended (9–10 concurrent Docker builds,
  <1 GB free, heavy compression); the first build OOM-killed at the 18 GB container limit.
  Waited for contention to drop to ≤4 builds, then built at LEAN_MEMORY_LIMIT=20000.

### Files Modified
- `proofs/Proofs/BaireCategoryTheoremOQ01OQ01OQ01.lean` (new, 256 lines)
- `proofs/Proofs.lean` (manifest import)
- `src/data/proofs/baire-category-theorem-oq-01-oq-01-oq-01/{meta,annotations}.json` (new)

### Next Steps
- Follow-up oq-01-oq-01-oq-01-oq-01: bundle a continuous linear bijection into `E ≃L[𝕜] F`
  and characterise injective bounded operators with closed range via a bounded left inverse.

### Honesty Note
The mathematics is classical and the proof follows Mathlib's own internal Baire argument
(it is NOT a novel proof distinct from Mathlib). The contribution is presenting the open
mapping, inverse mapping and closed graph theorems as explicit, machine-checked
consequences of the gallery's own Baire category theorem, completing the three-pillar trio.
