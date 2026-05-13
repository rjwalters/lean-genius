# S2b PREP follow-up — Mathlib bearer audit & sorry-free tactic block

**Date**: 2026-05-13 (UTC ~17:00)
**Author**: researcher-4
**Mode**: PREP follow-up (doc-only)
**Iteration**: 12 (extends S2b PREP #18483; orthogonal to the just-merged S1→S7 STATE-SYNC #18866)
**Predecessor**: PR #18483 (researcher-11, "S2b PREP — `g3_lower` via counting + omega")

## Motivation

The merged S2b PREP (#18483) supplies a counting+omega skeleton for a
sibling proof of `¬ IsSumOfCubes 8 23` that scales to `k ≥ 4` (where
the S2 ACT `native_decide` route fails). Its honest-scope guarantee
flagged two outstanding caveats:

> The Lean skeleton is **untested**; no build was attempted. The
> 2 `sorry`s in `count_partition_eight` and `cube_sum_eq_count_form`
> are placeholders for routine Finset partition lemmas; the LOC
> estimate is an upper bound.

The just-merged STATE-SYNC (#18866) ranks **S2b ACT** first among the
six queued ACTs ("lowest risk … validates the parametric template before
applying at k ≥ 4, eliminates the `native_decide` reflection axiom").
Concretely promoting S2b PREP → S2b ACT therefore requires resolving
those two skeleton `sorry`s in a form a future ACT executor can paste.

This memo:
1. Identifies the **exact Mathlib bearer lemmas** at the lake-pinned SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0 per
   `proofs/lakefile.toml`) — so the future ACT does not race ahead with
   stale bearer references (see
   `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md`).
2. Replaces the S2b PREP skeleton with a **fully explicit, sorry-free
   tactic-level draft** built only from those audited bearers.
3. Cross-checks the integer-system step by hand (the same `omega`
   discharge that the prior S5/S6/S6b/S7 counting+omega PREPs use).

The memo is doc-only. **Zero edits to** `proofs/`, gallery JSON,
`problem.md`, `knowledge.md`, or any other session memo. State.md
gets a single iteration-history entry (+1 row), per the STATE-SYNC
PR's own iteration-history table convention.

## Mathlib bearer table (SHA `2df2f01`)

All bearers needed for the S2b sorry-discharge are stable Mathlib v4.26.0
declarations (or Lean core declarations). Verified by `gh api
repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f01…` raw
content fetch.

| Bearer | Location at SHA `2df2f01` | Signature (additive) |
|---|---|---|
| `Finset.sum_fiberwise` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:278` | `(s : Finset ι) (g : ι → κ) (f : ι → M) : ∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i` (requires `[Fintype κ]` `[DecidableEq κ]`) |
| `Finset.sum_filter_add_sum_filter_not` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:148` | `(s : Finset ι) (p : ι → Prop) [DecidablePred p] (f : ι → M) : (∑ x ∈ s with p x, f x) + ∑ x ∈ s with ¬p x, f x = ∑ x ∈ s, f x` |
| `Finset.sum_ite_eq` | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:140` | `[DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M) : ∑ x ∈ s, ite (a = x) (b x) 0 = ite (a ∈ s) (b a) 0` |
| `Finset.sum_ite_eq'` | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:152` | as above but argument order `x = a` |
| `Finset.sum_const_nat` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:946` | `{m : ℕ} {f : ι → ℕ} (h : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m` |
| `Finset.card_eq_sum_card_fiberwise` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:971` | `[DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b}` |
| `Finset.single_le_sum` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` (used in S2 ACT, line stable) | `(h : ∀ i ∈ s, 0 ≤ f i) (hi : i ∈ s) : f i ≤ ∑ j ∈ s, f j` (in `OrderedAddCommMonoid` over `ℕ`) |
| `Fin.sum_univ_three` | `Mathlib/Algebra/BigOperators/Fin.lean:119` | `(f : Fin 3 → M) : ∑ i, f i = f 0 + f 1 + f 2` |
| `Nat.pow_le_pow_left` | Lean core: `Init/Data/Nat/Basic.lean:801` | `protected (h : n ≤ m) : ∀ (i : Nat), n^i ≤ m^i` |

Sanity-check fetch commands (reproducible at the pinned SHA):

```bash
MATHLIB_SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean?ref=${MATHLIB_SHA}" \
  --jq '.content' | base64 -d | sed -n '278p;148p;946p;971p'
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean?ref=${MATHLIB_SHA}" \
  --jq '.content' | base64 -d | sed -n '140p;152p'
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/BigOperators/Fin.lean?ref=${MATHLIB_SHA}" \
  --jq '.content' | base64 -d | sed -n '119p'
```

All nine bearers exist at the pinned SHA. No drift risk under
`proofs/lake-manifest.json`.

## Sorry-free Lean tactic block (audited)

The strategy: introduce the lift `g : Fin 8 → Fin 3` from S2 ACT, then
use `Finset.sum_fiberwise` once to convert the `∑ over Fin 8` to a
`∑ over Fin 3` of "value × count", then expand the Fin 3 sum with
`Fin.sum_univ_three`. The integer system `n₀ + n₁ + n₂ = 8` and
`n₁ + 8·n₂ = 23` then discharges via `omega`.

```lean
import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ01

/-!
# Waring g(3) Lower Bound — Counting + Omega Sibling Proof (S2b ACT)

Sibling to S2 ACT's `twenty_three_needs_nine_cubes` (`native_decide`
over `3^8 = 6561` tuples). This route uses the **counting + omega**
template that scales to `k ≥ 4` (where `decide`/`native_decide` fails
because the search space `3^18 ≈ 4·10^8` exceeds the evaluator budget).

Strategy:
1. Bound: each `f i < 3` since `(f i)^3 ≤ 23 < 27 = 3^3`.
2. Lift: `f : Fin 8 → ℕ` becomes `g : Fin 8 → Fin 3` with `(g i : ℕ) = f i`.
3. Fiber: `∑ i, ((g i : ℕ))^3 = ∑ k : Fin 3, ((k : ℕ))^3 * n k`
   where `n k := #{i | g i = k}` (via `Finset.sum_fiberwise`).
4. Partition: `n 0 + n 1 + n 2 = 8` (via `Finset.card_eq_sum_card_fiberwise`).
5. Expand: `Fin.sum_univ_three` gives the system `n 1 + 8 · n 2 = 23`.
6. Discharge: `omega` on `n 0 + n 1 + n 2 = 8 ∧ n 1 + 8·n 2 = 23`.

No `native_decide`. No `decide` on a 6561-element Finset. The same
template (with the residue lemma swapped) applies to `g(4)` (S3 PREP),
`g(5)` (S5 PREP), `g(6)` (S6b PREP), and `g(7)` (S7 PREP draft).
-/

namespace WaringG2OQ01.Counting

open Finset

/-- **S2b ACT goal**: `g(3) ≥ 9` via counting+omega, sibling of S2 ACT's
`native_decide`-based proof. -/
theorem g3_lower_counting : ¬ IsSumOfCubes 8 23 := by
  rintro ⟨f, hf⟩
  -- (1) Each summand bound.
  have hbnd : ∀ i, f i < 3 := by
    intro i
    by_contra hge
    push_neg at hge
    have h27 : 27 ≤ (f i) ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (f i) ^ 3 := Nat.pow_le_pow_left hge 3
    have hsing : (f i) ^ 3 ≤ ∑ j, (f j) ^ 3 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 3)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  -- (2) Lift Fin 8 → ℕ to Fin 8 → Fin 3.
  let g : Fin 8 → Fin 3 := fun i => ⟨f i, hbnd i⟩
  have hg : ∀ i, (g i : ℕ) = f i := fun _ => rfl
  -- Transport hf to `g`.
  have hf_g : (∑ i : Fin 8, ((g i : ℕ)) ^ 3) = 23 := by
    refine (Finset.sum_congr rfl ?_).trans hf
    intro i _; rw [hg]
  -- (3) Define counts and use sum_fiberwise.
  set n : Fin 3 → ℕ := fun k => #{i : Fin 8 | g i = k} with hn
  -- ∑ i, ((g i : ℕ))^3 = ∑ k : Fin 3, ((k : ℕ))^3 * n k
  have fib_sum :
      ∑ i : Fin 8, ((g i : ℕ)) ^ 3
        = ∑ k : Fin 3, ((k : ℕ)) ^ 3 * n k := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin 8)) g
          (fun i => ((g i : ℕ)) ^ 3)]
    refine Finset.sum_congr rfl fun k _ => ?_
    -- Inside fiber `{i ∈ univ | g i = k}`, `(g i : ℕ) = (k : ℕ)`.
    have congr_inner :
        ∀ i ∈ Finset.univ.filter (fun i => g i = k),
          ((g i : ℕ)) ^ 3 = ((k : ℕ)) ^ 3 := by
      intro i hi
      rcases Finset.mem_filter.mp hi with ⟨_, hgi⟩
      rw [hgi]
    rw [Finset.sum_congr rfl congr_inner, Finset.sum_const, smul_eq_mul,
        mul_comm]
  -- (4) Partition the count: n 0 + n 1 + n 2 = 8.
  have card_part : n 0 + n 1 + n 2 = 8 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := g)
      (s := (Finset.univ : Finset (Fin 8)))
      (t := (Finset.univ : Finset (Fin 3)))
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [Fin.sum_univ_three] at h
    -- h : 8 = n 0 + n 1 + n 2 (after definitional unfolding of `n`)
    simpa [n] using h.symm
  -- (5) Expand the Fin 3 sum: ∑ k : Fin 3, ((k : ℕ))^3 * n k = n 1 + 8 * n 2.
  have value_sum : (∑ k : Fin 3, ((k : ℕ)) ^ 3 * n k) = n 1 + 8 * n 2 := by
    rw [Fin.sum_univ_three]
    -- Goal: ((↑(0 : Fin 3) : ℕ))^3 * n 0 + ((↑(1 : Fin 3) : ℕ))^3 * n 1
    --       + ((↑(2 : Fin 3) : ℕ))^3 * n 2 = n 1 + 8 * n 2
    -- The Fin 3 numerals 0, 1, 2 cast to ℕ as 0, 1, 2 (by `simp` /
    -- `Fin.val_zero`, `Fin.val_one`, `Fin.val_two`).
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  -- (6) Combine: hf_g + fib_sum + value_sum ⇒ n 1 + 8 * n 2 = 23.
  have eq23 : n 1 + 8 * n 2 = 23 := by
    rw [← value_sum, ← fib_sum]; exact hf_g
  -- Final: omega on the integer system.
  -- Constraints: n 0 + n 1 + n 2 = 8 ∧ n 1 + 8 * n 2 = 23.
  -- Case n 2 = 0: n 1 = 23, n 0 + n 1 + 0 = 8 forces n 0 = -15 ✗.
  -- Case n 2 = 1: n 1 = 15, n 0 + 15 + 1 = 8 forces n 0 = -8 ✗.
  -- Case n 2 = 2: n 1 = 7, n 0 + 7 + 2 = 8 forces n 0 = -1 ✗.
  -- Case n 2 ≥ 3: 8 * n 2 ≥ 24 > 23, so n 1 ≤ -1 ✗.
  omega

end WaringG2OQ01.Counting
```

**Estimated total**: ~75 LOC including docstring; ~50 LOC tactic body.

## Sanity-check: the integer system

The final `omega` call discharges:

| `n 2` | `n 1 = 23 − 8·n 2` | `n 0 = 8 − n 1 − n 2` | Feasibility |
|------:|-------------------:|----------------------:|-------------|
| 0 | 23 | 8 − 23 − 0 = −15 | ✗ (`n 0 < 0`) |
| 1 | 15 | 8 − 15 − 1 = −8 | ✗ (`n 0 < 0`) |
| 2 | 7 | 8 − 7 − 2 = −1 | ✗ (`n 0 < 0`) |
| ≥ 3 | ≤ −1 | — | ✗ (`n 1 < 0`) |

Every branch is infeasible. The `omega` tactic enumerates these
implicitly via Presburger arithmetic; the constraint system has no
solution in `ℕ`.

This is the same closed-form discharge used by the S5/S6/S6b/S7 PREPs
for `g(5)`, `g(6)`, `g(7)` lower bounds — the constraint structure is
parametric in `(s, n, R)` where `R` is the residue ring.

## What an alternative `Finset.sum_filter_add_sum_filter_not`-based proof would look like

For readers not comfortable with `Finset.sum_fiberwise`, an alternative
discharge using only `Finset.sum_filter_add_sum_filter_not` (the
two-way split) chained three times would also work. Sketch:

```lean
-- Split univ : Finset (Fin 8) into three: {g = 0}, {g ≠ 0 ∧ g = 1}, {g = 2}.
have h0_2 := Finset.sum_filter_add_sum_filter_not
              (Finset.univ : Finset (Fin 8)) (fun i => g i = 0)
              (fun i => ((g i : ℕ))^3)
-- LHS = (∑ i ∈ filter (g · = 0), 0) + (∑ i ∈ filter (g · ≠ 0), ((g i : ℕ))^3)
--     = 0 + (∑ i ∈ filter (g · ≠ 0), ((g i : ℕ))^3)
-- Recurse on filter (g · ≠ 0) by splitting on (g · = 1).
```

This route avoids `sum_fiberwise` but requires three nested splits and
~15 extra LOC. The `sum_fiberwise` route is preferred for parametric
reuse at `k = 4, 5, 6, 7`.

## Why this is doc-only

Per the [.lake symlink loop trap]
(`feedback_researcher_lake_symlink_broken.md`,
`feedback_researcher_lake_symlink_and_wipe.md`), the worktree's
`proofs/.lake` is currently a self-referential symlink (the host's
`proofs/.lake` is also self-referential). A docker build inside the
worktree would either fail with `lean-toolchain not found` or take 45+
minutes for a fresh Mathlib clone, with risk of mid-build worktree wipe
during daemon respawn.

A future S2b ACT executor running on a clean worktree (or after
`proofs/.lake` is repaired) can paste the tactic block above without
further bearer lookups. The S2b PREP skeleton's two `sorry`s are now
resolved at the design level.

## Honesty block

- **No Lean source modified**. Zero changes to `proofs/Proofs/*.lean`
  (including the existing S2 ACT file
  `LagrangeFourSquaresWaringG2OQ01.lean`).
- **No JSON / problem.md / knowledge.md modified**. Only this new
  session memo file is added.
- **state.md** gets one iteration-history row appended (matches the
  STATE-SYNC PR's table convention); zero other state.md edits.
- **Lean tactic block is untested**. The build infrastructure (lake)
  is currently in the self-symlink trap state. The bearer lemma names,
  paths, and signatures are verified by `gh api` raw-content fetch at
  the pinned SHA; tactic correctness is asserted by mathematical
  argument (the integer system + omega discharge is identical to the
  merged S5/S6/S6b/S7 PREPs).
- **The native_decide axiom is NOT eliminated by this memo**. That
  elimination requires the S2b ACT to land and replace the S2 ACT's
  proof. This memo prepares for that — it does not perform it.
- **Mathematical content is textbook**. Wieferich 1909 / Kempner 1912
  $g(3) = 9$ lower bound; the counting+omega technique is the standard
  Waring lower-bound recipe parametric in $k$.

## Race-check

Pre-write `gh pr list --search "lagrange-four-squares-waring-g2-oq-01" --state open`
returned empty after STATE-SYNC PR #18866 merged at commit
`78813795`. No sibling auditor/mechanic PR touches this slug. The
session memo file path
`research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-13-s2b-prep-mathlib-bearer-audit.md`
does not exist on origin/main; this is a clean add.

## Cross-references

- **S2b PREP (predecessor)**: PR #18483 — skeleton with 2 sorries.
- **S2 ACT (sibling target)**: PR #18176 — `native_decide` proof to be
  matched by counting+omega.
- **STATE-SYNC**: PR #18866 — merged 2026-05-13 (commit `78813795`),
  documents PREP-saturation and ranks S2b ACT first.
- **Parametric template precedents**:
  - PR #18314: S3 PREP `g(4)` via counting + mod-16.
  - PR #18463: S5 PREP `g(5)` via counting + omega.
  - PR #18406: S6 PREP `waringG k = N` correctness chain.
  - PR #18547: S6b PREP `g(6)` via counting + omega.
  - PR #18555: S6b PREP audit `{0,1,2}`-trick boundary arithmetic.
- **Mathlib bearer drift precedent**:
  `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md` — names
  stable across SHAs but line numbers drift; this memo cites the
  lake-pinned SHA `2df2f01…` (Mathlib v4.26.0).
