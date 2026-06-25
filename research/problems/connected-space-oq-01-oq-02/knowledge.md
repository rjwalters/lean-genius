# connected-space-oq-01-oq-02 — The Topologist's Sine Curve Is Connected

**Status:** COMPLETED (verified, 0 sorries, 0 axioms, original)
**Lean file:** `proofs/Proofs/ConnectedSpaceOQ01OQ02.lean`
**Answers:** parent `connected-space-oq-01` second open question (use the bark-and-tree
corollary on a concrete dense-connected-skeleton space).

## Summary

Formalized T = {(x, sin x⁻¹) : x > 0} ∪ ({0} × [−1,1]) in ℝ × ℝ and proved `IsConnected T`.
Graph G = continuous image of `Ioi 0` ⇒ connected; limit segment ⊆ closure G; then the
parent's `IsConnected.subset_closure` (bark and tree) on G ⊆ T ⊆ closure G closes it.

## Session 2026-06-24 (Session 1) — FRESH

**Mode:** FRESH · **Outcome:** completed

### What I Did
- Defined sineCurve / limitSegment / topologistSineCurve.
- isConnected_sineCurve via isConnected_Ioi.image + continuousOn_param.
- limitSegment_subset_closure: the meat — Metric.mem_closure_iff + approximants
  aₙ = arcsin y + n·2π giving sin aₙ = y exactly (periodicity + sin_arcsin), aₙ⁻¹ → 0.
- isConnected_topologistSineCurve via IsConnected.subset_closure.
- Built clean on host `lake env lean` (docker down); axiom-checked → only foundational.

### Key Findings / gotchas
- Pairing continuous functions on a set: `ContinuousOn.prodMk` (NOT `.prod`).
- `inv_lt_comm₀ (0<a) (0<b) : a⁻¹ < b ↔ b⁻¹ < a` turns ε⁻¹ < aₙ into aₙ⁻¹ < ε.
- `div_lt_iff₀` (not `div_lt_iff`) on current Mathlib.
- Unfold the `def topologistSineCurve` (`unfold`) before `rw [union_subset_iff]`.
- Product distance to a same-second-coordinate point collapses to first coord via Prod.dist_eq.
- The approximation is EXACT in the y-coordinate (sin hits y on the nose every period); only
  the x-coordinate needs a limit, so closure membership is a one-axis Archimedean estimate.

### Files Modified
- `proofs/Proofs/ConnectedSpaceOQ01OQ02.lean` (new, 104 lines, 5 thm / 3 def)
- `src/data/proofs/connected-space-oq-01-oq-02/{meta,annotations,index}`

### Next Steps (follow-up open questions)
- Formalize NOT path-connected (the interesting half; needs a no-path argument).
- Local connectedness failure at the segment; closed-curve path-connected variant.

### Note
- This session also lost a race on fibonacci-identities-oq-05-oq-03 (already shipped to main
  as PR #29493 while I was building an identical proof). Pool "available" is stale; now I
  check origin/main + worktrees before claiming. See memory.
