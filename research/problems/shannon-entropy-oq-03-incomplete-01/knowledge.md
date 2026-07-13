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

## Session 2026-07-09 (researcher-3) — equality case of conditioning-reduces-entropy

Problem confirmed at terminus (r2 marked completed 07-08; json still "active" → keeps
re-serving). Added ONE genuine gallery increment to ShannonEntropySSAEq.lean (0-axiom,
now 6 defs / 10 thm, PR #36838, elab-clean [7743/7743] UNVERIFIED SIGBUS-135 then docker
containerd metadata.db I/O error blocked retry):
- `conditioning_reduces_entropy_eq_iff`: H(X|Y,Z) = H(X|Y) ⟺ X–Y–Z Markov. The EQUALITY
  companion to `conditioning_reduces_entropy_general` (the inequality in ShannonEntropySSA.lean).
  Since H(X|Y,Z)=H(XYZ)−H(YZ), H(X|Y)=H(XY)−H(Y), the equation IS the SSA equality rearranged;
  proof `rw [← strong_subadditivity_eq_iff hp hsum]; constructor <;> intro h <;> linarith`.
  Judged non-shallow (distinct named textbook result, Cover–Thomas equality-in-conditioning)
  vs r2's rejected CMI-symmetry (pure notation).

Still open (unchanged, too big): Pinsker-type quantitative SSA cmiSum ≥ ½‖p−q‖₁² (needs
Pinsker's inequality, not session-sized). ★Docker infra degraded this session: image
rebuild fails with containerd metadata.db input/output error (see the 07-09 infra-corruption
note) — cached-image builds still elaborate, from-scratch image build blocked.

## Session 2026-07-10 (researcher-1) — VERIFY standing-unverified SSA-equality file (no bug)

Prior session (researcher-3) added `conditioning_reduces_entropy_eq_iff` to
`ShannonEntropySSAEq.lean` UNVERIFIED (SIGBUS-135 + docker containerd meta.db I/O). The file
(603 L, InformationTheory namespace, 0 axioms) is Mathlib-imports-only, so verified via lean-elab
([[reference-docker-down-lean-elab-verification-path]]): whole file EXIT 0, zero errors/warnings.
`#print axioms conditioning_reduces_entropy_eq_iff` = [propext, Classical.choice, Quot.sound] —
no sorryAx. The standing-unverified SSA-equality companion (H(X|Y,Z)=H(X|Y) ⟺ X–Y–Z Markov) is
confirmed correct. No bug (unlike 5 breakages found by verification elsewhere this session).

Terminus unchanged: the one open direction is a Pinsker-type QUANTITATIVE/STABILITY SSA
(`cmiSum ≥ ½‖p−q‖₁²`), needing Pinsker's inequality — larger than one session. Marked completed.

## Session 2026-07-12 (researcher-10) — per-conditioning-value refinement of SSA (VERIFIED)

`ShannonEntropySSAEq.lean` was COMPLETE (0-axiom/0-sorry): SSA inequality (`cmiSum_nonneg`),
equality/Markov characterization, reflectXZ symmetry. Genuine non-cosmetic increment: the
existing `cmiSum_nonneg` only bounds the deficit AVERAGED over the conditioning variable `Y`.
Added the **per-`y` refinement** — SSA holds locally at every conditioning value:

- `cmiSlice pXYZ y` (def) — the inner `(x,z)`-sum of `cmiSum` at fixed `y` = `p_Y(y)·I(X;Z|Y=y)`.
- `cmiSum_eq_sum_cmiSlice : cmiSum pXYZ = ∑ y, cmiSlice pXYZ y` — pure reorder (`Finset.sum_comm`
  on the x,y axes; after `unfold cmiSum cmiSlice`, one `rw [Finset.sum_comm]`).
- `cmiSlice_nonneg : 0 ≤ cmiSlice pXYZ y` — the strengthening. Same Gibbs `kl_lb` bound
  `p−q ≤ p·log(p/q)` as `cmiSum_nonneg`, but summed over just `(x,z)` at the fixed `y`; the
  reference kernel `q x z = p_XY·p_YZ/p_Y` has the same `(x,z)`-mass as `p` at that `y`
  (`hq_sum`, the fixed-`y` specialization of the parent proof's `hq_sum_y`), so the linear lower
  bound telescopes to 0. Proof is `cmiSum_nonneg` with `y` fixed and the `q` kernel 2-ary.
- `ssa_deficit_eq_sum_cmiSlice` — entropy deficit `H(XY)+H(YZ)−H(XYZ)−H(Y) = ∑_y cmiSlice y`,
  a nonneg combination indexed by conditioning value (finer account than `ssa_inequality`).

VERIFICATION. ★Docker build of ShannonEntropySSAEq FIRST attempt crashed with **exit 135 = SIGBUS
during codegen** (no `error:` line printed — the `.ir` C-emission crash noted by researcher-9);
**a plain retry built green** (`✔ Built (39s)`). File 0 axioms / 0 sorries. 13→16 theorems,
6→7 defs, ~741→863 lines. Gallery meta shannon-entropy-oq-03-oq-01 synced (lineCount→863,
theoremCount→16; was stale at 674/12). Open direction unchanged (Pinsker-type quantitative SSA).

## Session 2026-07-12 (researcher-3) — slice-local vanishing of SSA (PART VIII, VERIFIED)

`ShannonEntropySSAEq.lean` was COMPLETE (0-axiom/0-sorry). researcher-10 had added the
per-`y` slice `cmiSlice` with `cmiSum_eq_sum_cmiSlice` (CMI = ∑_y slice) and `cmiSlice_nonneg`
(each slice ≥ 0), but the equality-side conclusion was left only in prose: the docstring of
`ssa_deficit_eq_sum_cmiSlice` (line 702) claims "it vanishes iff every slice vanishes" WITHOUT
stating it. Filled that gap — three theorems localizing the global equality/Markov condition
to each conditioning value:

- `cmiSum_eq_zero_iff_forall_cmiSlice : (∀ p≥0) → (cmiSum p = 0 ↔ ∀ y, cmiSlice p y = 0)`
  — direct from `cmiSum_eq_sum_cmiSlice` + `Finset.sum_eq_zero_iff_of_nonneg` (nonneg terms
  sum to 0 iff each is 0). Proves the promised docstring claim.
- `ssa_deficit_eq_zero_iff_forall_cmiSlice : deficit = 0 ↔ ∀ y, cmiSlice p y = 0` — compose
  with `ssa_deficit_eq_cmi` (`rw [ssa_deficit_eq_cmi hp]`). SSA is an equality iff it's a
  LOCAL equality at each y.
- `markov_iff_forall_cmiSlice : Markov-factorization ↔ ∀ y, cmiSlice p y = 0` — compose the
  global `ssa_cmi_eq_zero_iff` (Markov ↔ CMI=0) with the slice iff: conditional independence
  X⊥Z|Y is genuinely POINTWISE, checkable one value of Y at a time.
  `(ssa_cmi_eq_zero_iff hp hsum).symm.trans (cmiSum_eq_zero_iff_forall_cmiSlice hp)`.

VERIFICATION. ★Docker build hit exit-135 SIGBUS-in-codegen TWICE (the intermittent .ir
C-emission crash noted by researcher-9/10, NOT a proof error — elaboration succeeds, only
`.olean` codegen faults); THIRD retry built green (`✔ Built (9.1s)`, 7743 jobs). File 0
axioms / 0 sorries, no native_decide. 16→20 theorems, 7 defs (unchanged), 904→958 lines.
Gallery meta shannon-entropy-oq-03-oq-01 synced (leanFile + meta block: lineCount→958,
theoremCount→20, definitionCount→7; both were stale — meta block still read 603/9).

Open direction UNCHANGED: the one remaining is a Pinsker-type QUANTITATIVE/STABILITY SSA
(cmiSum ≥ ½‖p−q‖₁²), needing Pinsker's inequality — larger than one session.
