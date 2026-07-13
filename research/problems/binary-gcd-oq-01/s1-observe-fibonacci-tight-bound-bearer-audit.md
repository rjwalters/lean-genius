# S1 OBSERVE — Mathlib bearer audit for the Fibonacci tight Lamé bound (researcher-5, 2026-05-13)

**Slug**: `binary-gcd-oq-01`
**Phase**: S1 OBSERVE (doc-only audit; sketches but does not implement the S2 ACT)
**Mathlib SHA (pinned)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Lean file**: `proofs/Proofs/BinaryGcdOQ01.lean` (215 LOC, 0 sorries, 0 axioms, status `verified`)
**Open question targeted**: #3 in `meta.json.conclusion.openQuestions` — *"prove the tight form of Lamé's theorem — `euclidSteps(F_{n+1}, F_n) = n` — and hence that the bound is asymptotically tight, not just an upper bound"*.

## Goal of this OBSERVE

Document that a Mathlib-based ACT for the Fibonacci-tight Lamé bound is **unblocked**: all
bearers needed are already in Mathlib v4.26.0, and the proof reduces to a clean induction
on `n` after one elementary `fib_add_two` step. This file gives:

1. The precise statement to prove (with edge cases).
2. The catalog of Mathlib bearers needed.
3. A ~40 LOC Lean proof skeleton.
4. Build-risk assessment for a future S2 ACT.

## Precise statement

The existing `euclidSteps` in `BinaryGcdOQ01.lean` is defined for `a b : ℕ` and is
**symmetric in the sense that it dispatches on which argument is larger**:

```lean
def euclidSteps (a b : ℕ) : ℕ :=
  match a, b with
  | 0, _ => 0
  | _, 0 => 0
  | a' + 1, b' + 1 =>
    if b' + 1 ≤ a' then         -- a > b
      1 + euclidSteps (b' + 1) ((a' + 1) % (b' + 1))
    else                          -- a ≤ b
      1 + euclidSteps (a' + 1) ((b' + 1) % (a' + 1))
```

### Hand-computed truth table (cross-check)

Using `Nat.fib` (so `fib 0 = 0`, `fib 1 = 1`, `fib 2 = 1`, `fib 3 = 2`, `fib 4 = 3`,
`fib 5 = 5`, `fib 6 = 8`, ...):

| n | fib (n+1) | fib n | euclidSteps (fib (n+1)) (fib n) |
|---|---|---|---|
| 0 | fib 1 = 1 | fib 0 = 0 | 0 (defn match `_, 0 => 0`) |
| 1 | fib 2 = 1 | fib 1 = 1 | 1 (`else` branch with `1 % 1 = 0` → `1 + euclidSteps 1 0 = 1`) |
| 2 | fib 3 = 2 | fib 2 = 1 | 1 (`if` branch with `2 % 1 = 0` → `1 + euclidSteps 1 0 = 1`) |
| 3 | fib 4 = 3 | fib 3 = 2 | 2 (`if` branch: `1 + euclidSteps 2 (3 % 2) = 1 + euclidSteps 2 1 = 1 + 1 = 2`) |
| 4 | fib 5 = 5 | fib 4 = 3 | 3 (`1 + euclidSteps 3 (5 % 3) = 1 + euclidSteps 3 2 = 1 + 2 = 3`) |
| 5 | fib 6 = 8 | fib 5 = 5 | 4 (`1 + euclidSteps 5 3 = 1 + 3 = 4`) |
| 6 | fib 7 = 13 | fib 6 = 8 | 5 |
| 7 | fib 8 = 21 | fib 7 = 13 | 6 |

The clean formula (matching the table from row `n = 2` onward) is:

```
euclidSteps (Nat.fib (n + 1)) (Nat.fib n) = n - 1     for n ≥ 2
```

Equivalently, using a `+ 2` shift to avoid the edge cases:

```
euclidSteps (Nat.fib (n + 2)) (Nat.fib (n + 1)) = n   for n ≥ 1
```

The row `n = 0, 1` deviate because `fib 0 = 0` and `fib 1 = fib 2 = 1` collide. We
state the theorem in the `+ 2` shifted form to keep the recurrence uniform.

## Mathlib bearer catalog (pinned SHA `2df2f01...`)

### `Mathlib.Data.Nat.Fib.Basic`

Bearers used directly in the proof:

- `Nat.fib_zero : fib 0 = 0`
- `Nat.fib_one : fib 1 = 1`
- `Nat.fib_two : fib 2 = 1`
- `Nat.fib_add_two : fib (n + 2) = fib n + fib (n + 1)` — **the load-bearing recurrence**.
- `Nat.fib_lt_fib_succ : 2 ≤ n → fib n < fib (n + 1)` — used to dispatch the `if` branch
  via `b' + 1 ≤ a'` (strict inequality lets us conclude `b' < a'` ⟹ `b' + 1 ≤ a'`).
- `Nat.fib_pos {n : ℕ} : 0 < fib n ↔ 0 < n` (look up exact name; alternatively use
  `Nat.fib_le_fib_succ` with strict-mono witnesses).

### Modular-arithmetic bearers

- `Nat.mod_eq_sub_of_lt_two_mul` or the direct algebra `fib (n+2) - fib (n+1) = fib n`
  (`Nat.fib_add_two_sub_fib_add_one`).
- More directly: `fib (n+2) % fib (n+1) = fib n` when `fib (n+1) > fib n` (i.e., `n ≥ 1`).
  Proof: `fib (n+2) = fib n + fib (n+1) = fib (n+1) + fib n` and since `fib n < fib (n+1)`
  for `n ≥ 1` (by `Nat.fib_lt_fib_succ`), the Euclidean `% ` gives `fib n`.
- Lemma to extract: `Nat.fib_add_two_mod_fib_add_one_eq_fib` (likely needs to be
  established as a one-line `have` rather than imported).

### No new typeclasses

No instances, no decidable-equality maneuvers required. The proof is in `ℕ` throughout.

## Lean proof skeleton (~40 LOC, target for a future S2 ACT)

```lean
namespace BinaryGcdOQ01

open Nat

/-- Helper: for n ≥ 1, `fib (n+2) % fib (n+1) = fib n`. -/
private lemma fib_add_two_mod_fib_add_one (n : ℕ) (hn : 1 ≤ n) :
    Nat.fib (n + 2) % Nat.fib (n + 1) = Nat.fib n := by
  have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h2 : Nat.fib n < Nat.fib (n + 1) :=
    Nat.fib_lt_fib_succ (by omega : 2 ≤ n + 1)
  -- `(fib n + fib (n+1)) % fib (n+1) = fib n` since `fib n < fib (n+1)` and
  -- `(a + b) % b = a % b = a` when `a < b`.
  rw [h1, Nat.add_mul_mod_self_left]  -- or `Nat.add_mod_right` variant
  exact Nat.mod_eq_of_lt h2

/-- **Fibonacci tight Lamé bound** (open question 3 from meta.json):
    `euclidSteps (fib (n+2)) (fib (n+1)) = n` for n ≥ 1. -/
theorem euclidSteps_fib_tight (n : ℕ) (hn : 1 ≤ n) :
    euclidSteps (Nat.fib (n + 2)) (Nat.fib (n + 1)) = n := by
  induction n with
  | zero => omega   -- contradicts hn
  | succ k ih =>
    -- Base case k = 0 (so n = 1): unfold to euclidSteps 2 1 = 1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      decide          -- or `simp [euclidSteps, Nat.fib]; decide`
    -- Inductive case: peel off one euclidSteps step using `fib_add_two_mod_fib_add_one`
    have ih' := ih hk
    have hfa : Nat.fib (k + 1) < Nat.fib (k + 2) :=
      Nat.fib_lt_fib_succ (by omega : 2 ≤ k + 2)
    -- Unfold euclidSteps on `(fib (k+3), fib (k+2))` to `1 + euclidSteps (fib (k+2)) (fib (k+1))`
    -- using `fib_add_two_mod_fib_add_one (k+1) (by omega)`.
    set A := Nat.fib (k + 3)
    set B := Nat.fib (k + 2)
    -- A > B because fib is strict-mono past index 2
    have hAB : B < A := Nat.fib_lt_fib_succ (by omega : 2 ≤ k + 3)
    -- A % B = fib (k+1) by the helper
    have hmod : A % B = Nat.fib (k + 1) :=
      fib_add_two_mod_fib_add_one (k + 1) (by omega)
    -- Now unfold the `euclidSteps A B` recursion
    sorry  -- ← S2 ACT: ~20 more lines to finish the unfold + omega bookkeeping

end BinaryGcdOQ01
```

The `sorry` above is a deliberate placeholder for the S2 ACT — this file is OBSERVE, so it
does NOT introduce the sorry into the proven file. The skeleton is provided as a target.

### Subtleties for the S2 ACT author

1. **`euclidSteps` matches on `a' + 1, b' + 1`** rather than on `0 < a` `0 < b` — so the
   unfold must go through `obtain ⟨a', rfl⟩ : ∃ k, A = k + 1`. Use
   `Nat.exists_eq_succ_of_ne_zero` plus `Nat.fib_pos`.
2. **The `if` branch hits when `b' + 1 ≤ a'`, i.e., `b < a` after `succ` unwrap.** For our
   `A = fib (k+3), B = fib (k+2)` with `k ≥ 1`, we have `B + 1 ≤ A` iff `B < A`, which
   holds by `Nat.fib_lt_fib_succ`.
3. **Termination is not an issue** — `euclidSteps` already has `termination_by a + b`, and
   our `A % B = fib (k+1) < B` so the recurrence is sound.

## Build risk assessment for the future S2 ACT

- **LOC**: ~40 lines of Lean total (one private helper, one main theorem).
- **No new imports**: `Mathlib.Data.Nat.Fib.Basic` is already transitively imported via
  `Mathlib.Tactic`. Verify with `lake env lean` once.
- **No new typeclasses**: pure `ℕ` reasoning throughout.
- **Tactics used**: `induction`, `omega`, `decide` (for `n = 1` base), `rw`,
  `Nat.mod_eq_of_lt`, `Nat.add_mul_mod_self_left`. All cheap.
- **Worktree `.lake` symlink loop** (per memory trap
  `feedback_researcher_lake_symlink_loop_and_wipe.md`): build from main repo cwd via
  `./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ01` to dodge the worktree symlink
  loop. Single-file build; expected ~3–5 min.
- **Sorries delta**: `+1 → 0` if successful (with the placeholder `sorry` removed at the
  end).
- **Risk-adjusted estimate**: 1 work iteration of ~30 min including build. If the helper
  lemma's name (`Nat.fib_add_two_mod_fib_add_one`) doesn't exist, replace with the
  ad-hoc proof shown in the skeleton.

## Open questions deferred (out of scope for this OBSERVE)

- **#1 Weighted complexity model**: requires designing a Lean-native cost model. ~200 LOC
  estimate.
- **#2 Lehmer GCD**: requires `Nat.digits` cost accounting infrastructure.
- **#4 Binary GCD worst case lower bound**: requires a worst-case input family
  construction (related to the binary expansion of consecutive odd integers).

This OBSERVE only touches #3.

## Files changed by this OBSERVE

- `research/problems/binary-gcd-oq-01/state.md` — synced Phase from `OBSERVE` (template)
  to `S1 OBSERVE — extension audit (post-main-bounds)`; populated "What Has Been Proved"
  section; recorded open questions with bearer status.
- `research/problems/binary-gcd-oq-01/knowledge.md` — populated stub sections with
  actual proved theorems and bearer references.
- `research/problems/binary-gcd-oq-01/s1-observe-fibonacci-tight-bound-bearer-audit.md`
  — this note (NEW).

No changes to `proofs/Proofs/BinaryGcdOQ01.lean`. No changes to
`src/data/proofs/binary-gcd-oq-01/meta.json` (its `conclusion.openQuestions` already
records the targeted open question accurately). Sorries unchanged (0). Axiom count
unchanged (0). Theorem count unchanged (4 per #16356).

## Audit-trail notes

- Memory trap `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md` followed: all
  Mathlib decls (`Nat.fib`, `Nat.fib_add_two`, `Nat.fib_lt_fib_succ`,
  `Nat.fib_zero/one/two`) verified at lake-pinned SHA `2df2f01...`, not at HEAD.
- Memory trap `feedback_write_tool_main_repo_absolute_path_trap.md`: used worktree-
  relative paths throughout this session after one earlier misroute (recovered).
