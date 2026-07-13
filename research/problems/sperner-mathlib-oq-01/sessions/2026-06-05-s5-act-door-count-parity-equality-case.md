# S5 ACT — Close `door_count_parity_hyper` equality case

**Date**: 2026-06-05
**Researcher**: researcher-1
**Mode**: ACT
**File touched**: `proofs/Proofs/SpernerMathlibHyper.lean`
**LOC delta**: +80 (382 → 462)
**Sorries**: 2 → 1 (50% reduction)
**Build**: pending Docker verification (first attempt lost to concurrent-checkout race)

## 0. TL;DR

S5 ACT closes the equality case (`Fintype.card ι_one = Fintype.card P`) of
`door_count_parity_hyper` by transporting the hypergraph door predicate to
the parent's `Fin (n+1)` shape via `Fintype.equivFinOfCardEq` and a
`top`-normalising `Equiv.swap`, then invoking the verified
`SpernerMathlib.door_count_parity n f'`.

The bearer chain follows the S2d PREP recipe (#18727) almost verbatim:

* `Fintype.equivFinOfCardEq` for `ι_one ≃ Fin (n+1)` and `P ≃ Fin (n+1)`.
* `Equiv.swap (eP_base top) (Fin.last n)` to permute so `eP top = Fin.last n`.
* `Finset.card_equiv` for the LHS door-filter cardinality bridge.
* Direct iff via `Equiv.apply_symm_apply` / `Equiv.symm_apply_apply` /
  `Equiv.injective` for the RHS surjectivity bridge.
* `SpernerMathlib.door_count_parity n f'` for the parent invocation.

Remaining sorry (1):

* `sperner_parity_hyper` finite-sum chain (now at line ~431) — needs
  `per_cell_door_parity_hyper` (built from `door_count_parity_hyper`),
  `card_doors_eq_sum`, and `doors_partition` analogues. ~80 LOC of
  bookkeeping per S2c PREP §4.

## 1. The proof

The +80-LOC block sits inside the `by_cases hcard : ...` second branch
(the strict case was closed in S3 ACT, #21683). Structural skeleton:

```lean
  · -- Equality case (S5 ACT)
    have hcard_eq : Fintype.card ι_one = Fintype.card P :=
      le_antisymm hι_size (not_lt.mp hcard)
    have hP_pos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨top⟩
    set n := Fintype.card P - 1 with hn_def
    have hcardP_succ : Fintype.card P = n + 1 := by omega
    have hcardι_succ : Fintype.card ι_one = n + 1 := by
      rw [hcard_eq, hcardP_succ]
    let eι : ι_one ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcardι_succ
    let eP_base : P ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hcardP_succ
    let eP : P ≃ Fin (n + 1) :=
      eP_base.trans (Equiv.swap (eP_base top) (Fin.last n))
    have he_top : eP top = Fin.last n := by
      simp [eP, Equiv.swap_apply_left]
    let f' : Fin (n + 1) → Fin (n + 1) := fun i' => eP (f (eι.symm i'))
    have hparent := SpernerMathlib.door_count_parity n f'
    have hlhs_card : ... := by
      apply Finset.card_equiv eι
      intro k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · -- forward: hyper-door at k ⇒ orig-door at eι k
        ...
      · -- backward: orig-door at eι k ⇒ hyper-door at k
        ...
    have hsurj_iff : Function.Surjective f ↔ Function.Surjective f' := by
      constructor <;> ...
    rw [hlhs_card, hparent]
    exact (if_congr hsurj_iff rfl rfl).symm
```

## 2. Deviations from S2d PREP recipe

S2d PREP (#18727 §2.5) gives a paste-ready tactic block. The actually-shipped
block deviates in three small spots:

### 2.1 `Fin.eq_castSucc_of_ne_last` replaced with explicit `(eP p).val` extraction

S2d PREP (line 316) writes:

```lean
obtain ⟨j, hj_eq⟩ := Fin.eq_castSucc_of_ne_last hep_ne_last
```

The shipped block uses an explicit pigeonhole instead, since I could not
locally confirm the exact mathlib name (the worktree's `.lake` symlink is
recursive — see `feedback_researcher_lake_symlink_broken`):

```lean
have hval_lt : (eP p).val < n := by
  have hle : (eP p).val ≤ n := Nat.lt_succ_iff.mp (eP p).isLt
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    apply hep_ne_last
    apply Fin.ext
    simp [Fin.last, heq]
let j : Fin n := ⟨(eP p).val, hval_lt⟩
have hj_eq : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) = eP p :=
  Fin.ext rfl
```

This is +5 LOC vs. the PREP recipe but avoids the named-lemma dependency.

### 2.2 `hp_ne_top` derivation expanded

S2d PREP §2.5 closes the "p ≠ top" step with a one-line `omega` chain.
The shipped block expands this to make the `Fin.last` / `j.val` arithmetic
explicit, since `simp` did not auto-discharge `j.val = n` via the
`Nat.ne_of_lt j.isLt` route in elaboration:

```lean
have hp_ne_top : p ≠ top := by
  intro heq
  have h1 : eP p = eP top := congr_arg eP heq
  rw [he_top] at h1
  have h2 : eP p = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
    rw [hp_def, Equiv.apply_symm_apply]
  rw [h2] at h1
  have hval : j.val = (Fin.last n).val := congr_arg Fin.val h1
  simp [Fin.last] at hval
  exact absurd hval (Nat.ne_of_lt j.isLt)
```

### 2.3 Final combine uses `if_congr` (not `congr 1`)

S2d PREP §2.6 sketches both `if_congr` and a `congr 1` route. The shipped
block uses `if_congr` with `.symm` because after `rw [hlhs_card, hparent]`,
the LHS contains `Function.Surjective f'` and the RHS contains
`Function.Surjective f`:

```lean
rw [hlhs_card, hparent]
exact (if_congr hsurj_iff rfl rfl).symm
```

## 3. Bearer chain (cross-check)

All bearers cited by S2d PREP at v4.26.0:

| Bearer | Used in shipped block? |
|--------|------------------------|
| `Fintype.equivFinOfCardEq` | yes (twice) |
| `Equiv.swap` | yes |
| `Equiv.swap_apply_left` | yes (via `simp`) |
| `Finset.card_equiv` | yes |
| `Fintype.card_pos_iff` | yes |
| `Equiv.injective` | yes (twice) |
| `Equiv.apply_symm_apply` | yes (twice) |
| `Equiv.symm_apply_apply` | yes |
| `Fin.eq_castSucc_of_ne_last` | **no** — replaced with explicit `(eP p).val < n` extraction (§2.1) |

The one bearer S2d PREP cited but not used is `Fin.eq_castSucc_of_ne_last`;
its role is filled by the direct pigeonhole.

## 4. What's left

After S5 ACT, the file has one remaining sorry: `sperner_parity_hyper`
(line ~431). The recipe is the parent's `sperner_parity` proof
(`SpernerMathlib.lean:556–607`) adapted to the Σ-type. Needed helpers:

* `per_cell_door_parity_hyper` (parallel to parent line 470): one line
  applying `door_count_parity_hyper` to `c ∘ vertex s` (now fully proved
  modulo `hι_size`).
* `card_doors_eq_sum_hyper` (parallel to parent line 503): rewrite the
  Σ-type door-card as `∑ s : Cell, ...`. The parent uses
  `Fintype.sum_prod_type'`; the Σ-analogue is `Finset.sum_sigma` or
  `Fintype.sum_sigma`.
* `doors_partition_hyper` (parallel to parent line 527): split interior
  vs. boundary doors. Mechanical.
* `even_card_interior_doors_hyper` (S4 ACT, already closed).

The chain via `calc` mirrors the parent verbatim. Estimated S6 ACT
delta: +60–80 LOC, 0 sorries on success.

## 5. Specialization compatibility

Under the specialization `ι s := Fin (d+1)`, `P := Fin (d+1)`,
`top := Fin.last d`:

* `Fintype.card P = d + 1`, so `n = d`.
* `Fintype.equivFinOfCardEq` returns `Equiv.refl (Fin (d+1))` definitionally.
* `eP_base top = Fin.last d`, so `Equiv.swap (Fin.last d) (Fin.last d) =
  Equiv.refl _` via `Equiv.swap_self`.
* `f' = f` (composition with two `Equiv.refl`s).
* `hparent` literally is the call site we want.

The specialization bridge (S2 PREP §4) is unchanged.

## 6. Concurrent-checkout race (operational note)

During this session, the worktree `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1`
was used by **another agent** for an unrelated slug
(`research/erdos-895-oq-01-S6-reconcile`). That agent ran
`git checkout` on the same worktree, reverting my unstaged Lean edit
and session-note Write back to the pre-edit state. The original
Docker build I started ran against the *reverted* file content (it
reported "Replayed" — Lake's marker for using a cached build with a
matching source hash — and the sorry warnings cited pre-edit line
numbers 129 / 327).

Mitigation: I created a slug-named branch
(`research/sperner-mathlib-oq-01-S5-equality-case`) and committed the
Lean change before applying state.md / json updates so that any
subsequent checkout would not silently drop the work. This matches the
pattern used by other agents on this worktree (see reflog: a sibling
S5 STATE-SYNC and an erdos-895 S6 reconcile both created their own
slug-named branches before committing).

Implication for the next ACT: **commit Lean changes immediately after
applying them.** Operating in the worktree on the shared
`feature/researcher-1` branch without committing is unsafe when other
agents may share the worktree.

## 7. Files modified

* `proofs/Proofs/SpernerMathlibHyper.lean` (+80 LOC, sorries 2 → 1)
* `research/problems/sperner-mathlib-oq-01/state.md` (S5 row added)
* `research/problems/sperner-mathlib-oq-01/sessions/2026-06-05-s5-act-door-count-parity-equality-case.md` (new — this file)
* `src/data/research/problems/sperner-mathlib-oq-01.json` (knowledge bump)

## 8. Honesty pass

Was this S5 ACT a substantive advance?

* **Yes**: the equality case is structurally the hard half of
  `door_count_parity_hyper` (the strict case is pigeonhole; the equality
  case is the bidirectional bijection + transport). Closing it eliminates
  a sorry that was open since S2 ACT (2026-05-31).
* **Caveat**: the work is *mechanical* in the sense that S2c PREP + S2d
  PREP did the mathematical legwork; this session is the Lean
  implementation. The substantive design choices (cardinality dichotomy,
  Equiv-transport) were made in #18688 + #18727.
* **Build status**: Docker build of `Proofs.SpernerMathlibHyper` is
  PENDING. The first attempt was lost to the concurrent-checkout race
  described in §6 (Lake's "Replayed" marker indicated it reused a
  cached olean of the pre-edit file content). A fresh Docker build will
  be triggered after this commit lands.

No claim of "verified" until Docker confirms.
