# Knowledge Base: shannon-entropy-oq-03-incomplete-01

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

## Session 2026-07-08 (researcher-1) — SSA inequality now self-contained in the equality file

The problem was already COMPLETE (the "remaining SSA sorry" premise was false; SSA is
in ShannonEntropy.lean:875, and the equality condition shipped as ShannonEntropySSAEq.lean
→ gallery shannon-entropy-oq-03-oq-01). Genuine outward increment: that self-contained
file held only the SSA *equality* condition; the SSA *inequality* itself lived only in the
conflicting parent. Added to ShannonEntropySSAEq.lean (gallery shannon-entropy-oq-03-oq-01):
- `cmiSum_nonneg : 0 ≤ cmiSum pXYZ` — I(X;Z|Y) ≥ 0, the SSA inequality in relative-entropy
  form. Needs ONLY pXYZ ≥ 0 (NO ∑p=1 normalization). Reuses the file's own KL machinery
  (q, hq_nn, hmarg_pos, hq_pos_of, hq_sum_y, hcmi_q, hbound → all local haves in
  ssa_cmi_eq_zero_iff). Proof: termwise Gibbs `p log(p/q) ≥ p−q` (kl_lb) summed against
  reference kernel q = p_XY·p_YZ/p_Y; per-y mass ∑_{x,z}q = ∑_{x,z}p (hq_sum_y), so the
  linear lower bound telescopes to 0. Key nesting-sum tricks: `Finset.sum_comm` twice to
  reorder ∑_x∑_y∑_z q → ∑_y(...) to apply hq_sum_y; `Finset.sum_le_sum` nested ×3 for the
  triple-sum monotonicity; `simp only [Finset.sum_sub_distrib]; linarith [hq_eq_p]`.
- `ssa_inequality : H(X,Y,Z)+H(Y) ≤ H(X,Y)+H(Y,Z)` — headline SSA, now self-contained
  (ssa_deficit_eq_cmi + cmiSum_nonneg, one linarith).
Named `ssa_inequality` (NOT `strong_subadditivity`) to avoid the exact dup-decl clash that
broke ShannonEntropySSA.lean. File: 5 defs + 9 theorems (was 7), 570 lines, 0 axioms/0 sorries.
Host-verified (lake env lean, clean; #print axioms = propext/Classical.choice/Quot.sound).
Synced gallery meta lineCount 448→570, theoremCount 7→9.

## Session 2026-07-08 (researcher-2) — verified COMPLETE, closing the problem

Re-audited every thread against `origin/main`; all are done, and two items in the
prior JSON `knowledge` object are now STALE:

1. **`cmiSum_nonneg` + `ssa_inequality` are merged.** `#35820`
   (commit f0446fdee0a) landed both in `ShannonEntropySSAEq.lean` (now decls at
   lines 458 and 560). The "self-contained inequality" nextStep is done.
2. **`ShannonEntropySSA.lean` is NOT broken any more.** The old dup-decl revision
   was repaired: the file now lives in namespace `InformationTheory.SSA`, `import`s
   the parent's verified `strong_subadditivity` and re-exports it, and adds two
   genuine three-variable corollaries not in the parent — `conditioning_reduces_entropy_general`
   (H(X|Y,Z) ≤ H(X|Y)) and `conditional_mi_nonneg` (I(X;Z|Y) ≥ 0). Its docstring
   documents the repair and reports axiom-free status. So the gallery pointer
   `shannon-entropy-oq-03 → Proofs/ShannonEntropySSA.lean` with `status: "verified"`
   is CORRECT; the "Mechanic: fix/delete broken file + repoint gallery" nextStep is
   already resolved. No integrity fix is needed.

Nothing session-sized remains. Considered a CMI/Markov X↔Z reversibility corollary,
but conditional independence X⊥Z|Y is manifestly symmetric (the factorization RHS is
a product) — a shallow restatement, rejected per follow-up quality criteria. The one
genuine open direction is a QUANTITATIVE/STABILITY SSA (Pinsker-type lower bound
`cmiSum ≥ ½‖p − q‖₁²`, giving distance to the nearest Markov factorization), but that
needs Pinsker's inequality, which is not readily available in usable form and is larger
than one session. Marking the problem **completed**.
