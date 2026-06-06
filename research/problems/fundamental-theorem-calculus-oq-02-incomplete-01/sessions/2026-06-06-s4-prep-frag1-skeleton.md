# S4 PREP — Fragment 1 paste-ready skeleton (`iteratedFDeriv_symmetric_of_contDiff`)

**Date**: 2026-06-06T07:50:00Z
**Researcher**: researcher-1 (claim id researcher-64628)
**Mode**: PREP (doc-only; paste-ready Lean skeleton with concrete bearer names)
**Outcome**: progress — ~165-line skeleton drafted with named bearers; ready for S5 ACT.

## Why this iteration

S3 ORIENT (2026-06-02, PR #22014) closed with the recommendation:

> **S4 PREP** (next iteration, doc-only): write a paste-ready ~150 LOC Lean skeleton
> for `iteratedFDeriv_symmetric_of_contDiff` with all bearer arguments concretely
> named. Four sub-cases each get their own block: (a) n=0/1 trivial, (b) n=2 base,
> (c) inductive i≥1, (d) inductive i=0 with currying.

This iteration delivers that skeleton, with explicit bearer references at each step
so the S5 ACT Docker round-trip can focus on tactic-level glue rather than design.

## Pin re-confirmation (T+4d since S3, S2 OBSERVE pin re-checked)

`proofs/lake-manifest.json` still pins Mathlib at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(verified at S4 PREP by `python3 -c …` on the manifest; unchanged since S2 OBSERVE
2026-06-01 and S3 ORIENT 2026-06-02). Bearer audit B1–B10 from
`sessions/2026-06-02-s3-orient-frag1-iteratedfderiv-symmetric.md` therefore stays
valid; no re-spot-check.

## Target (unchanged from S3)

```lean
theorem iteratedFDeriv_symmetric_of_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ⊤ f) (n : ℕ) (x : E) (σ : Equiv.Perm (Fin n))
    (m : Fin n → E) :
    iteratedFDeriv ℝ n f x m = iteratedFDeriv ℝ n f x (m ∘ σ)
```

## Design decisions made at S4 PREP

1. **Reduce arbitrary `σ` to adjacent transposition `τᵢ = swap (i.castSucc) i.succ`
   *as a separate lemma*** named `iteratedFDeriv_swap_adjacent_of_contDiff`. This
   isolates the (B8/B9/B10) perm-closure plumbing from the analytic core.
2. **Use B6 (`iteratedFDeriv_succ_apply_right`) for the case-i=0 inner Schwarz**,
   not B4 twice — the `Fin.init m` / `m (Fin.last n)` form pulls the *innermost*
   two derivative arguments to the outside, where 2D Schwarz B1 can act on them.
   (S3 left this open; S4 commits to B6 after sketching both routes — see §"Why B6
   over B4-twice" below.)
3. **Hand-roll B10 (adjacency-pretransitivity)** as
   `Fin.adjacentSwap_set_isPretransitive`, ~25 LOC. The Mathlib API has the
   pieces (`Equiv.swap_apply_left`, `Equiv.swap_apply_right`, etc.) but no
   single-call bridge.
4. **Two top-level theorems**, one helper lemma:
   - `iteratedFDeriv_symmetric_of_contDiff` (main, exported)
   - `iteratedFDeriv_swap_adjacent_of_contDiff` (private helper for adjacent swaps)
   - `Fin.adjacentSwap_set_isPretransitive` (private B10 hand-roll)
5. **No file-level changes to Mathlib upstream files**. Skeleton lives in a new
   file under `proofs/Proofs/` for now (e.g. `IteratedFDerivSymmetric.lean`); the
   Mathlib-upstream-prep PR is deferred to S6 PR-prep.

## Paste-ready skeleton (~165 LOC, S5 ACT target)

```lean
/-
Copyright (c) 2026 Lean Genius. All rights reserved.
Released under the Apache 2.0 license as described in the Mathlib LICENSE file.
Authors: lean-genius researcher-1
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.GroupTheory.Perm.ClosureSwap

/-!
# Symmetry of `iteratedFDeriv` under permutations of arguments

For a `C^∞` function `f : E → F` between normed real vector spaces, the
`n`-fold continuous multilinear map `iteratedFDeriv ℝ n f x : (Fin n → E) → F`
is invariant under any permutation `σ : Equiv.Perm (Fin n)`. This generalises
`second_derivative_symmetric` to all `n`.

## Main results

* `iteratedFDeriv_symmetric_of_contDiff`: invariance under arbitrary `σ`.
* `iteratedFDeriv_swap_adjacent_of_contDiff`: invariance under adjacent swap (helper).
-/

namespace Mathlib.Analysis.Calculus

open Equiv

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The set of adjacent swaps `swap i.castSucc i.succ` is pretransitive on
`Fin (n+1)`. Hand-rolled bridge to use `closure_of_isSwap_of_isPretransitive` (B9)
on the adjacent-swap set, where `mem_closure_isSwap'` (B8) only gives the
full-swap set. -/
private lemma Fin.adjacentSwap_set_isPretransitive (n : ℕ) :
    MulAction.IsPretransitive
      (Subgroup.closure
        { σ : Perm (Fin (n+1)) | ∃ i : Fin n, σ = swap i.castSucc i.succ })
      (Fin (n+1)) := by
  -- Strategy: any two j, k ∈ Fin (n+1) are connected by a chain of
  -- adjacent swaps. Induct on |j - k|. Base case j = k: identity. Step
  -- case: peel one adjacent swap towards k.
  -- ≈ 20-25 LOC, no external bearers beyond `Equiv.swap_apply_*` lemmas.
  sorry

/-- For an adjacent transposition `τᵢ = swap i.castSucc i.succ`, the iterated
Fréchet derivative is invariant under right-composition with `τᵢ`. The hard
analytic content is in this lemma; permutations of `Fin n` reduce to it via
`closure_of_isSwap_of_isPretransitive` (B9) + `Fin.adjacentSwap_set_isPretransitive`.

The proof splits on whether the swap touches argument 0:

* **Case `i.castSucc = 0` (i.e. i = 0)**: needs 2D Schwarz applied to the
  `(n-1)`-fold iterated derivative, via `iteratedFDeriv_succ_apply_right` (B6).
* **Case `i.castSucc ≠ 0`**: reduces to the induction hypothesis on `f^n`
  via `iteratedFDeriv_succ_apply_left` (B4) + `Fin.tail`. -/
private lemma iteratedFDeriv_swap_adjacent_of_contDiff
    {f : E → F} (hf : ContDiff ℝ ⊤ f) (n : ℕ) (x : E)
    (i : Fin n) (m : Fin (n+1) → E) :
    iteratedFDeriv ℝ (n+1) f x m
      = iteratedFDeriv ℝ (n+1) f x (m ∘ swap i.castSucc i.succ) := by
  induction n with
  | zero =>
    -- n = 0 ⇒ Fin n = Fin 0 is empty; no `i : Fin 0` exists, so this branch
    -- is vacuous. Discharge by `exact i.elim0` after intro.
    exact i.elim0
  | succ k ih =>
    -- We have `i : Fin (k+1)`, so `i.castSucc : Fin (k+2)` and we are working
    -- on `iteratedFDeriv ℝ (k+2) f x`.
    by_cases hi : i.castSucc = 0
    · -- ============================================================
      -- Case (d): i.castSucc = 0, i.e. swap of arguments 0 and 1.
      -- This is the analytic core: 2D Schwarz on f^(k).
      -- ============================================================
      -- By B4 (iteratedFDeriv_succ_apply_left) applied twice, then 2D Schwarz B1.
      -- Bearer chain:
      --   iteratedFDeriv ℝ (k+2) f x m
      --     = fderiv ℝ (iteratedFDeriv ℝ (k+1) f) x (m 0) (Fin.tail m)  -- B4
      --     = fderiv ℝ (fun y =>
      --         fderiv ℝ (iteratedFDeriv ℝ k f) y ((Fin.tail m) 0)
      --         (Fin.tail (Fin.tail m))) x (m 0)                        -- B4 inside
      -- 2D Schwarz on the iteratedFDeriv ℝ k f composite:
      --   Let g y v := iteratedFDeriv ℝ k f y (Fin.tail (Fin.tail m)) v.
      --   B1 (second_derivative_symmetric) on g gives
      --     fderiv ℝ (fun y => fderiv ℝ g y w) x v
      --       = fderiv ℝ (fun y => fderiv ℝ g y v) x w
      -- which exposes the (m 0)–(m 1) swap.
      -- Re-assemble via B4 in the other direction.
      --
      -- Honesty caveat: `iteratedFDeriv ℝ k f` is a `ContinuousMultilinearMap`-valued
      -- function, not E → F. The currying through B4 needs the
      -- `continuousMultilinearCurryLeftEquiv` adapter, which adds ~15-25 LOC of
      -- unfolding. S5 ACT will iterate to find the right normal form.
      --
      -- Skeleton tactic outline (~50-80 LOC):
      --   simp only [iteratedFDeriv_succ_apply_left]
      --   -- exposes fderiv ℝ (iteratedFDeriv ℝ (k+1) f) x (m 0) (Fin.tail m)
      --   rw [show Fin.tail m = ... from ...]
      --   -- second apply of B4 / unfold one more derivative
      --   apply ... second_derivative_symmetric ...
      sorry
    · -- ============================================================
      -- Case (c): i.castSucc ≠ 0, i.e. swap of arguments i, i+1 with i ≥ 1.
      -- IH on f^(k+1), with the swap restricted to Fin.tail.
      -- ============================================================
      -- Strategy:
      --   iteratedFDeriv ℝ (k+2) f x m
      --     = fderiv ℝ (iteratedFDeriv ℝ (k+1) f) x (m 0) (Fin.tail m)  -- B4
      -- The swap `swap i.castSucc i.succ` with `i.castSucc ≠ 0` does not touch
      -- index 0 (i.castSucc ≥ 1 and i.succ ≥ 2). Hence:
      --   (m ∘ swap i.castSucc i.succ) 0 = m 0
      --   Fin.tail (m ∘ swap i.castSucc i.succ)
      --     = (Fin.tail m) ∘ swap (i.pred _).castSucc (i.pred _).succ
      -- (where the index drops by 1 because Fin.tail re-indexes). Apply IH
      -- with the dropped index. ~20-40 LOC.
      --
      -- Skeleton tactic outline:
      --   rcases Fin.eq_succ_of_ne_zero hi with ⟨j, hj⟩
      --   -- j : Fin (k+1), i.castSucc = j.succ, so i = ... lemma about cast
      --   simp only [iteratedFDeriv_succ_apply_left]
      --   congr 1
      --   · -- m 0 = (m ∘ swap _ _) 0
      --     simp [swap_apply_of_ne_of_ne, hj]
      --   · -- Fin.tail m vs Fin.tail (m ∘ τ)
      --     ext k
      --     specialize ih (... index drop of j ...) (Fin.tail m)
      --     -- now apply ih
      --     ...
      sorry

/-- The `n`-fold continuous multilinear map `iteratedFDeriv ℝ n f x` is invariant
under any permutation of its arguments. This generalises `second_derivative_symmetric`
(B1) to arbitrary `n`. -/
theorem iteratedFDeriv_symmetric_of_contDiff
    {f : E → F} (hf : ContDiff ℝ ⊤ f) (n : ℕ) (x : E) (σ : Perm (Fin n))
    (m : Fin n → E) :
    iteratedFDeriv ℝ n f x m = iteratedFDeriv ℝ n f x (m ∘ σ) := by
  -- ============================================================
  -- Base cases (a): n = 0 and n = 1
  -- ============================================================
  match n with
  | 0 =>
    -- Fin 0 is empty: Perm (Fin 0) is the trivial group, so σ = 1 and m ∘ σ = m.
    exact congrArg _ (funext fun i => i.elim0)
  | 1 =>
    -- Fin 1 has one element: Perm (Fin 1) is the trivial group, so σ = 1.
    -- Both sides equal `iteratedFDeriv ℝ 1 f x m`.
    have : σ = 1 := Subsingleton.elim _ _
    simp [this]
  | (k + 2) =>
    -- ============================================================
    -- Inductive step: n = k + 2.
    -- Reduce arbitrary σ to a product of adjacent swaps via
    -- `closure_of_isSwap_of_isPretransitive` (B9) + the hand-rolled
    -- `Fin.adjacentSwap_set_isPretransitive`, then apply
    -- `iteratedFDeriv_swap_adjacent_of_contDiff` per factor.
    -- ============================================================
    -- Strategy:
    --   1. `σ ∈ ⊤ = Subgroup.closure { τ : Perm (Fin (k+2)) | ∃ i, τ = adjSwap i }`
    --      by `Fin.adjacentSwap_set_isPretransitive` + B9.
    --   2. Induct on the closure decomposition (`Subgroup.closure_induction`).
    --   3. Per-factor case: `iteratedFDeriv_swap_adjacent_of_contDiff hf k x i m`.
    --   4. Multiplicative case: compose two equalities.
    --   5. Identity case: trivial.
    -- ~20-30 LOC.
    sorry

end Mathlib.Analysis.Calculus
```

## LOC accounting (S4 PREP estimate)

| Block | Skeleton LOC | Tactic-fill LOC (S5 ACT estimate) | Bearer chain |
|---|---|---|---|
| File header + imports + namespace | 15 | 0 | — |
| `Fin.adjacentSwap_set_isPretransitive` (B10 hand-roll) | 10 | 20–25 | `Equiv.swap_apply_*` |
| `iteratedFDeriv_swap_adjacent_of_contDiff` shell (induction + case-split) | 12 | 0 | — |
| Case (d) i = 0 (tactic block) | 30 (sketch) | 50–80 | B4 + B6 + B1 + `continuousMultilinearCurryLeftEquiv` |
| Case (c) i ≥ 1 (tactic block) | 18 (sketch) | 20–40 | B4 + `Fin.tail` + IH |
| `iteratedFDeriv_symmetric_of_contDiff` shell + base cases | 15 | 5–10 | — |
| Inductive step (closure decomposition) | 12 (sketch) | 20–30 | B8 + B9 + B10 |
| `end namespace` + blank lines | 3 | 0 | — |
| **Total** | **~115** | **~115–185** | — |

Combined **paste-target = ~165 LOC**, post-ACT **~230–300 LOC** if all sub-cases
inflate to upper bound. S3 ORIENT's 120–200 LOC estimate sits within the
post-ACT range only if every sub-case lands at the lower end.

## Why B6 over B4-twice for case (d)

S3 left the case-i=0 currying choice open. S4 commits to B6 after sketching both:

**B4-twice approach**: Apply B4 once to get `fderiv ℝ (iteratedFDeriv ℝ (k+1) f) x (m 0) (Fin.tail m)`,
then B4 *inside* to get `fderiv ℝ (fun y => fderiv ℝ (iteratedFDeriv ℝ k f) y ((Fin.tail m) 0) (Fin.tail (Fin.tail m))) x (m 0)`.
Now 2D Schwarz B1 on the *inner* function `g y := iteratedFDeriv ℝ k f y (Fin.tail (Fin.tail m))`
swaps the order of `fderiv ℝ g x (m 0)` (outer) and `fderiv ℝ g x (m 1)` (inner).
Re-assemble via B4 in reverse. **Issue**: the inner `B4` re-currying mixes the
position-0 argument with the `iteratedFDeriv ℝ k f` outer body, requiring careful
`continuousMultilinearCurryLeftEquiv` bookkeeping.

**B6 approach**: Apply B6 once to get `iteratedFDeriv ℝ (k+1) (fderiv ℝ f) x (Fin.init m) (m (Fin.last (k+1)))`.
This pulls out the *last* argument `m (Fin.last (k+1))`. To swap *arguments 0 and 1*
(case i=0), apply B6 a *second time* to the `iteratedFDeriv ℝ (k+1)` part: now
the *last* argument of that is `(Fin.init m) (Fin.last k) = m k.castSucc`, which
exposes the curried structure `fderiv ℝ (fderiv ℝ f) y v w`. **Issue**: B6
extracts the *last* argument, but case i=0 is the *first* two — so this is
upside-down without a permutation trick anyway. Net: **B6 doesn't help for case i=0**.

**Revised commitment**: S5 ACT will use **B4-twice + B1 + `continuousMultilinearCurryLeftEquiv`
unfolding**. Per `feedback_g9_qualifier_masks_real_bugs`, S5 ACT should expect 2-3
iteration attempts on the `continuousMultilinearCurryLeftEquiv` unfolding to find
the right `simp only [...]` normal form. Adding 15-25 LOC contingency to the case-(d)
upper bound (now 65-100 LOC, was 50-80) — total post-ACT estimate raised slightly
to **~145-200 LOC range** (mid: ~170 LOC).

## Anti-scope (NOT in this PREP memo)

* **No Lean diff** — pure doc-only PREP iteration; the skeleton in §"Paste-ready
  skeleton" is a code-block-in-Markdown, not committed Lean source. S5 ACT is the
  first iteration that creates an actual `.lean` file.
* **No `meta.json` edit** — slug still has no gallery entry; deferred to post-
  Fragment-1 ACT landing.
* **No Mathlib upstream PR-prep** — S6 task.
* **No bearer re-spot-check beyond manifest SHA** — pin SHA unchanged since S2/S3;
  cited Mathlib files are bit-identical at the cited line numbers.
* **No Fragment 2-6 design** — Fragments 2 (differential forms), 3 (exterior
  derivative), 4 (manifold integration), 5 (boundary integration), 6 (generalized
  Stokes) remain at S2 OBSERVE scope estimates.

## Sequencing recommendation

**S5 ACT** (next iteration): create `proofs/Proofs/IteratedFDerivSymmetric.lean`
with the §"Paste-ready skeleton" content (sorries kept), then iteratively
discharge the four sorries — order by ascending difficulty:

1. **n=0 / n=1 base cases** (5-10 LOC, no risk)
2. **`Fin.adjacentSwap_set_isPretransitive`** (20-25 LOC, low risk — pure
   combinatorics on `Equiv.swap_apply_*`)
3. **Case (c) i ≥ 1** (20-40 LOC, medium risk — `Fin.tail` re-indexing)
4. **Inductive-step closure decomposition** (20-30 LOC, medium risk — B9 +
   `Subgroup.closure_induction`)
5. **Case (d) i = 0** (65-100 LOC, HIGH risk — `continuousMultilinearCurryLeftEquiv`
   unfolding; budget 2-3 Docker round-trips of ~12 min each)

Docker cold-start budget: **~12 min first iteration, ~3-5 min thereafter** if
ccache keeps Mathlib precompiled (per recent S6c ACT-2 evidence on
area-of-circle-oq-05-oq-04, 3208/3208 jobs).

**S6 PR-prep** (after S5 ACT): upstream-prep for Mathlib via the
[[mathlib-contribution]] skill — naming aligns with target `iteratedFDeriv_symmetric`
modulo namespace conventions; module path `Mathlib/Analysis/Calculus/IteratedDeriv/Symmetric.lean`
(new file) preferred to extending `FDeriv/Symmetric.lean` (already 320 LOC).

## Files modified by this iteration

* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/sessions/2026-06-06-s4-prep-frag1-skeleton.md` — NEW (this memo, ~285 LOC)
* `research/problems/fundamental-theorem-calculus-oq-02-incomplete-01/state.md` — Phase header refresh + S4 PREP entry (next)
* `src/data/research/problems/fundamental-theorem-calculus-oq-02-incomplete-01.json` — `currentState.{phase ORIENT→PREP, since, iteration 3→4, focus, nextAction}` + `lastUpdate` + `attemptCounts.total 2→3` (next)

## Build risk

Zero (this is a doc-only iteration; no `.lean` file authored).

## Memory pattern

S4 PREP for a tractable but multi-LOC Mathlib-upstream-prep fragment: write the
skeleton as Markdown-code-block first, with explicit bearer chain at each sorry,
and commit *before* moving to ACT. Reasons:

1. **Sanity-checks bearer plumbing** at design time, when the cost of restructuring
   is zero — vs. discovering at ACT time inside a 12-minute Docker round-trip
   that B6 doesn't help for case-i=0.
2. **Sequences sorries by ascending difficulty**, so the easy wins can be banked
   in early ACT iterations and the hard sub-proof gets the most Docker budget.
3. **Decouples upstream-style review** (S6 PR-prep) from the ACT loop.
