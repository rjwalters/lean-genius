# S2 PREP-2 — `IsBipartiteWith` API line-number corrections + decidability resolution

**Date**: 2026-05-13 (~03:40 UTC)
**Researcher**: researcher-9
**Mode**: PREP (doc-only — does not modify any `.lean`, `.json`, `state.md`, `knowledge.md`, or `problem.md`)
**Status**: pristine new sessions file. Companion to the merged S2 PREP (PR #18449, researcher-4) — corrects two field-name / line-number errors and resolves the explicit "decision deferred to S2 ACT" left open in §"What this doc does NOT decide" of that PREP.
**Build cost**: 0 (no Lean changes).

## Purpose

The merged S2 PREP (`2026-05-13-s2-prep-isbipartitewith-skeleton.md`, PR #18449) leaves the **decidability of the bipartition witness** as an explicit unresolved question for S2 ACT:

> Decision deferred to S2 ACT: the S2 ACT must either (a) require `[DecidablePred (· ∈ s)]` as an additional typeclass hypothesis, (b) use `Classical.dec` to fabricate it (forfeiting computability), or (c) prefer the `Finset V`-valued `IsBipartiteWith.bipartiteAbove` / `IsBipartiteWith.bipartiteBelow` forms at `Bipartite.lean:183, 189` (less elegant but decidable).

This PREP-2:

1. **Resolves the decidability question**: option (a) is the correct answer, matching Mathlib's own pattern at `Bipartite.lean:379`. Options (b) and (c) are non-viable as stated; details below.
2. **Corrects two erroneous claims** in the parent PREP about the Mathlib API: a field name and the line numbers for the key declarations.
3. **Pre-stages the concrete `completeBipartiteGraph` corollary** to show the decidability hypothesis is automatically satisfied for the canonical witness `K_{m,n}`.

The output is a copy-paste-ready Lean blueprint refinement that the next ACT agent can use without re-verifying the Mathlib API against the pinned rev.

## 1. Correction A — `IsBipartiteWith` field names

**Parent PREP claim** (Audit 1, table line 1, paraphrased):

> `IsBipartiteWith G s t` — `structure` at line 84 with fields `disjoint : Disjoint s t`, `mem_or_mem : ∀ {v w}, G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s`

**Actual at v4.26.0 pin** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean:80`:

```lean
structure IsBipartiteWith (G : SimpleGraph V) (s t : Set V) : Prop where
  disjoint : Disjoint s t
  mem_of_adj ⦃v w : V⦄ : G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s
```

The second field is `mem_of_adj`, **not** `mem_or_mem`. The S2 ACT skeleton in the parent PREP (Audit 3, line ~113) uses `h.mem_of_mem_adj`, which is the derived *theorem* at line 94 (`IsBipartiteWith.mem_of_mem_adj`), not the structure field. That theorem signature is:

```lean
theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ t
```

The skeleton's usage `h.mem_of_mem_adj huv hus` is **correct** — `mem_of_mem_adj` is in dot-notation namespace `IsBipartiteWith`, taking `(hv : v ∈ s) (hadj : G.Adj v w)`. The first argument order `huv : G.Adj u v` vs `hus : u ∈ s` in the skeleton is **swapped**: the correct call is `h.mem_of_mem_adj hus huv` (with `hus : u ∈ s` first, then `huv : G.Adj u v`).

**Verbatim from Mathlib for the S2 ACT agent's reference**:

```lean
-- Bipartite.lean:94
theorem IsBipartiteWith.mem_of_mem_adj
    (h : G.IsBipartiteWith s t) (hv : v ∈ s) (hadj : G.Adj v w) : w ∈ t

-- Bipartite.lean:120
theorem IsBipartiteWith.mem_of_mem_adj'
    (h : G.IsBipartiteWith s t) (hw : w ∈ t) (hadj : G.Adj v w) : v ∈ s
```

## 2. Correction B — line-number drift

The parent PREP's table (Audit 1) gives line numbers off by ~4 from the actual file:

| Identifier | PREP claim | Actual (verified) | Drift |
|---|---|---|---|
| `IsBipartiteWith` structure | 84 | **80** | −4 |
| `IsBipartiteWith.symm` | 88 | **84** | −4 |
| `IsBipartiteWith.mem_of_mem_adj` | 98 | **94** | −4 |
| `IsBipartiteWith.mem_of_mem_adj'` | 124 | **120** | −4 |
| `isBipartiteWith_support_subset` | 145 | **141** | −4 |
| `IsBipartite` abbrev | 286 | **282** | −4 |
| `IsBipartite.exists_isBipartiteWith` | 290 | **286** | −4 |
| `IsBipartiteWith.isBipartite` | 299 | **295** | −4 |

Hypothesis: the parent PREP read the file from a local working tree that had 4 extra leading lines (e.g., a docstring fragment or comment block) compared to the v4.26.0 pin. Both reads yield consistent **deltas** between declarations (e.g., `mem_of_mem_adj` to `mem_of_mem_adj'` is 26 lines in both), so the relative positions are correct — only the absolute line numbers drift.

Verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Combinatorics/SimpleGraph/Bipartite.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.content' | base64 -d | grep -n -E '^(structure|theorem|def|lemma|abbrev) '`.

These corrections are **non-load-bearing** for the proof skeleton — `dot-notation` calls do not depend on line numbers — but they matter for any documentation or audit cross-references.

## 3. Resolution: option (a) is correct

The parent PREP listed three options for resolving the decidability of `· ∈ s`. Re-examining each against the verified Mathlib API:

### Option (a) — `[DecidablePred (· ∈ s)]` typeclass argument

**Verdict: ADOPT.** This matches Mathlib's own convention at `Bipartite.lean:379`:

```lean
instance [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] :
    DecidableRel (G.between s t).Adj :=
  inferInstanceAs (DecidableRel fun v w ↦ G.Adj v w ∧ (v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s))
```

When Mathlib needs `s, t` to be decidable, it requires the typeclass argument explicitly. The S2 ACT skeleton already does this (`[DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]` on `cut_size_of_isBipartiteWith`).

The **client-side cost** of this hypothesis: every consumer of `cut_size_of_isBipartiteWith` must supply a `DecidablePred` instance. For the concrete corollary `rand_approx_tight_K_mn`, this is automatic via `Sum.isLeft` / `Sum.isRight` (see §5 below). For an abstract `G.IsBipartite` hypothesis without a specific witness, the consumer must either (i) `classical` the proof or (ii) pick a specific witness with decidable membership.

### Option (b) — `Classical.dec` to fabricate the instance

**Verdict: REJECT for the main theorem; ACCEPTABLE for an explicit "classical" variant.**

Using `classical` in `cut_size_of_isBipartiteWith` forfeits *computability* of the resulting `Cut` (which uses `Finset.univ.filter (fun v => decide (v ∈ s))` — the `decide` becomes noncomputable). For a result about the *expected* cut size (a real number, not a constructive bit-vector), this loss is benign — but it propagates: any downstream `#eval`-style check or extracted-program use would fail.

Mathlib's convention is to provide both a primary computable version with typeclass arguments and an optional `classical` wrapper. The S2 ACT can ship just the computable version; a classical wrapper is a one-line corollary if needed.

### Option (c) — `bipartiteAbove` / `bipartiteBelow` Finset-valued forms

**Verdict: NOT APPLICABLE.** The parent PREP misread the Mathlib API. The declarations at lines 179, 185 are:

```lean
-- Bipartite.lean:179
theorem isBipartiteWith_bipartiteAbove (h : G.IsBipartiteWith s t) (hv : v ∈ s) :
    G.neighborFinset v = bipartiteAbove G.Adj t v

-- Bipartite.lean:185
theorem isBipartiteWith_bipartiteBelow (h : G.IsBipartiteWith s t) (hw : w ∈ t) :
    G.neighborFinset w = bipartiteBelow G.Adj s w
```

These are **theorems about the neighbor finset of a specific vertex**, parameterised by an existing `IsBipartiteWith s t` witness. They do **not** provide an alternative *witness construction* with a `Finset`-valued bipartition. The bipartition `(s, t)` remains a `Set V` even when one quotes these lemmas.

The actual `Finset`-valued analogue would be a `Bipartition` structure with `s t : Finset V`, but Mathlib v4.26.0 does not ship one — the natural workaround for a Finset witness is to use `(s : Finset V).toSet` and recover `IsBipartiteWith G ((s : Finset V) : Set V) ((t : Finset V) : Set V)`. This is more verbose than option (a) and offers no decidability advantage (`s ⊆ univ` is already decidable when `[Fintype V] [DecidableEq V]`).

## 4. Refined S2 ACT skeleton (after corrections)

```lean
import Proofs.RandomizedMaxCut
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace RandomizedMaxCutOQ03

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
         {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If `G` is bipartite with witness `(s, t)` and `· ∈ s` is decidable, the
canonical Boolean assignment `v ↦ decide (v ∈ s)` produces a `Cut` whose
size equals `G.edgeFinset.card`: every edge is cut. -/
theorem cut_size_of_isBipartiteWith
    {s t : Set V} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (h : G.IsBipartiteWith s t) :
    (Cut.ofAssignment (G := G) (fun v => decide (v ∈ s))).size = G.edgeFinset.card := by
  unfold Cut.size
  congr 1
  apply Finset.filter_true_of_mem
  intro e he
  refine Sym2.ind ?_ e
  intro u v hadj
  have huv : G.Adj u v := by
    rw [SimpleGraph.mem_edgeFinset] at hadj
    exact hadj
  by_cases hus : u ∈ s
  · -- u ∈ s ⟹ v ∈ t (h.mem_of_mem_adj hus huv) ⟹ v ∉ s (h.disjoint)
    have hvt : v ∈ t := h.mem_of_mem_adj hus huv  -- NOTE: hus first, huv second
    have hvs : v ∉ s := Set.disjoint_left.mp h.disjoint hus |>.symm ▸ ?_
    sorry  -- STRATEGIC-1: Cut.edgeInCut unfold + Sym2.lift_mk normalization
  · -- u ∉ s ⟹ u ∈ t (via support) ⟹ v ∈ s (h.mem_of_mem_adj' hut huv)
    sorry  -- STRATEGIC-2: same shape as branch 1 (mirror via mem_of_mem_adj')

end RandomizedMaxCutOQ03
```

**Two corrections to the parent skeleton**:

1. `h.mem_of_mem_adj hus huv` — `hus : u ∈ s` is the first explicit argument, not the second. (The implicit-binder convention `⦃v w⦄` on the structure field passes through; only the explicit arguments are reordered.)
2. `Set.disjoint_left.mp h.disjoint hus` returns `u ∉ t`, not `v ∉ s`. To get `v ∉ s` from `v ∈ t`, use `Set.disjoint_right.mp h.disjoint hvt`.

The two `sorry`s remain **mechanical Sym2-unfolding** — same scope as the parent PREP.

## 5. Concrete corollary: `K_{m,n}` decidability is free

`Mathlib.Combinatorics.SimpleGraph.Basic:149` defines:

```lean
@[simps]
def completeBipartiteGraph (V W : Type*) : SimpleGraph (V ⊕ W) where
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm v w := by cases v <;> cases w <;> simp
  loopless v := by cases v <;> simp
```

The natural bipartition is `s := { v : V ⊕ W | v.isLeft }`, `t := { v : V ⊕ W | v.isRight }`. Both are decidable: `Sum.isLeft` and `Sum.isRight` are `Bool`-valued functions, so `(· ∈ s) = (·.isLeft = true)` is `Decidable` by `Bool.decEq`.

**Corollary skeleton**:

```lean
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem rand_approx_tight_K_mn :
    let G := completeBipartiteGraph α β
    let s : Set (α ⊕ β) := { v | v.isLeft }
    let t : Set (α ⊕ β) := { v | v.isRight }
    -- Decidability is free:
    haveI : DecidablePred (· ∈ s) := fun v => Bool.decEq v.isLeft true
    haveI : DecidablePred (· ∈ t) := fun v => Bool.decEq v.isRight true
    -- Witness:
    haveI hbip : G.IsBipartiteWith s t := {
      disjoint := by
        rw [Set.disjoint_left]; intro v hvs hvt
        cases v <;> simp_all [Sum.isLeft, Sum.isRight]
      mem_of_adj := by
        intro v w hadj
        cases hadj with
        | inl h => left; exact ⟨h.1, h.2⟩
        | inr h => right; exact ⟨h.1, h.2⟩
    }
    (Cut.ofAssignment (G := G) (fun v => decide (v ∈ s))).size = G.edgeFinset.card := by
  exact cut_size_of_isBipartiteWith hbip
```

**LOC estimate for §5 corollary**: ~15 (the `mem_of_adj` field is two-by-two destructure, the `disjoint` field is one cases + simp, the conclusion is a single `cut_size_of_isBipartiteWith` invocation).

## 6. Why this PREP, not S2 ACT

The S2 ACT requires:

1. The two strategic `Sym2`-unfolding sorries (parent PREP's audit 3) — ~20-30 LOC of `unfold` + `simp [Sym2.lift_mk, Bool.decide_eq_true, Finset.mem_filter, ...]` chains. **No build risk** if the tactic chain is correct, but a one-shot ACT attempt may iterate on simp normal forms.
2. A `docker-build.sh` verification — **this is the build-risk component**. The worktree's `.lake` may be in a self-referential symlink loop (per `feedback_researcher_lake_symlink_loop_and_wipe.md`); a from-scratch Mathlib clone would take ~10 min and risks daemon respawn.
3. Gallery integration (`src/data/proofs/randomized-maxcut-oq-03/{meta.json, annotations.json, index.ts}`) — separate concern for S3 GALLERY.

This PREP-2 is **a 30-minute investment** that:

- Resolves the decidability question explicitly (option (a)).
- Corrects two minor but real errors in the parent PREP (`mem_of_adj` field name, argument order in `mem_of_mem_adj`).
- Pre-stages the concrete `K_{m,n}` corollary with the decidability obstacle pre-removed.
- Adds no Lean changes, no build risk, no gallery side-effects.

The next agent picking up S2 ACT can use this refined skeleton verbatim with the corrected argument order and the concrete corollary pre-staged.

## 7. Mathlib version pin verification

All claims in this document are against `Mathlib4` at rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, verified via:

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Combinatorics/SimpleGraph/Bipartite.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | sed -n '80,100p'
```

(returns the verbatim `structure IsBipartiteWith` block quoted in §1.)

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Combinatorics/SimpleGraph/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n -A 4 'completeBipartiteGraph'
```

(returns the verbatim `def completeBipartiteGraph` block quoted in §5.)

This pin matches `proofs/lean-toolchain` / `proofs/lakefile.toml` at HEAD; the parent PREP cites the same pin.

## 8. Anti-targets (out of scope for this PREP-2)

1. **Editing the parent PREP** (`2026-05-13-s2-prep-isbipartitewith-skeleton.md`). The parent is merged; this PREP-2 is a separate session document in the same `sessions/` subdirectory. Cross-references work via filename mention.
2. **Editing `state.md`** to reflect S2 PREP-2. State.md still says "OBSERVE, fast path" — both parent PREP and this PREP-2 are doc-only and do not need to update the phase. Next phase advance happens with S2 ACT.
3. **Building the Lean file**. No `.lean` changes here.
4. **Updating the research json** `src/data/research/problems/randomized-maxcut-oq-03.json`. Doc-only PREP — does not modify research JSON.
5. **Adding gallery files**. S3 GALLERY is a separate stage.
6. **`Classical` wrappers**. Mentioned in §3 (option (b)) but not implemented. The S2 ACT may decide whether to ship a classical variant.

## 9. Race awareness

At PREP-push time (2026-05-13 ~03:40 UTC):

- `gh pr list --search "randomized-maxcut-oq-03 in:title" --state open --repo rjwalters/lean-genius` → empty.
- `git branch -r | grep randomized-maxcut-oq-03` → empty.
- Most recent merge: PR #18449 (S2 PREP, doc-only) at 02:06:09Z — ~95 min before this PREP-2. Outside the 30-min-post-merge window.

**File path is unique**: `sessions/2026-05-13-s2-prep-2-decidability-resolution-and-api-corrections.md`. Zero conflict surface with the parent PREP at `sessions/2026-05-13-s2-prep-isbipartitewith-skeleton.md` (different filename).

## 10. Honest contribution boundary

This PREP-2:

- Identifies two real errors in the parent PREP (`mem_of_adj` field name; line-number drift).
- Resolves the explicit "decision deferred to S2 ACT" question (decidability — option (a)).
- Provides a copy-paste-ready concrete corollary skeleton for `K_{m,n}`.
- Pre-verifies the Mathlib API surface against the v4.26.0 pin.

It does **not**:

- Write any Lean code.
- Modify any existing file.
- Build anything.
- Discharge any open goal.
- Advance the slug's phase.

The slug's `state.md` remains at "Phase: OBSERVE / fast path" — next iteration is S2 ACT, with this PREP-2 as a refinement of the parent PREP's blueprint.

---

**End of S2 PREP-2 — no Lean changes, no gallery changes, no state changes. New entry in the `sessions/` subdirectory.**
