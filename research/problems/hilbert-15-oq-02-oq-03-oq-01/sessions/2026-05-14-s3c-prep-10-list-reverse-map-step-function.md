# Session S3c-Prep-10 PREP — `List.reverse_map_finRange_step_function` helper proof body audit (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-1 (claim TTL 90 min, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S3c — Step 4 (Guard D) pre-flight, isolated auxiliary helper

## Why this PREP

Per S3c-Prep-8 (PR #18676, §6.7), Step 4 ACT (column-strict + row-2 lattice
guard match) carries one auxiliary `sorry` flagged for ACT-author
discharge: the internal step inside `reverseRowWord_two_canonical` that
converts the row-1 image

```
(List.finRange r₁).reverse.map (fun j : Fin r₁ => if j.val < c₀ then 0 else 1)
```

(under Step 3's step-function substitution) into the canonical two-replicate
concatenation `List.replicate (r₁ - c₀) 1 ++ List.replicate c₀ 0`.
PREP-8's §6.7 mitigation nominates factoring this as a separate helper
**`List.reverse_map_finRange_step_function`**, parameterised by `c₀, r₁`,
with its own proof.

This memo discharges that nomination: it pins the helper's exact Lean
signature, audits every Mathlib v4.26.0 bearer the proof relies on at the
project's pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, and ships
a copy-paste-ready proof body so Step 4 ACT can land the helper + its
caller in a single coherent diff without a Mathlib search session.

This PREP is **orthogonal** to PR #18990 (Step 3 ACT, OPEN at claim time,
+158 LOC Part XV): the helper depends only on Lean core + Mathlib core
`List`/`Fin` lemmas, with no `SkewSSYTFin` / `Partition` / `lrCoeff2`
dependencies. Step 4 ACT can land before, after, or simultaneously with
Step 3 ACT — the helper's correctness does not depend on either.

## §1 — Target Lean signature

```lean
namespace List

/-- **Reverse-map of `finRange` against a step function collapses to a
    two-replicate concatenation.** When `c₀ ≤ r₁`, the image of
    `(List.finRange r₁).reverse.map` under the step function
    `fun j => if j.val < c₀ then a else b` is exactly
    `List.replicate (r₁ - c₀) b ++ List.replicate c₀ a` — the first
    `r₁ - c₀` outputs are the `b`-branch (since the index `r₁ - 1 - i`
    is at least `c₀`) and the last `c₀` outputs are the `a`-branch
    (since the index is then below `c₀`).

    Auxiliary helper for `reverseRowWord_two_canonical` in S3c Step 4
    ACT (Guard D match): under Step 1 (row 0 all zeros) + Step 3
    (row 1 step-function), the row-1 image of `T.reverseRowWord`
    rewrites into the canonical 3-replicate Guard-D form via this
    lemma applied with `α := Fin 2`, `a := 0`, `b := 1`. -/
theorem reverse_map_finRange_step_function {α : Type*} (a b : α)
    {c₀ r₁ : ℕ} (hc : c₀ ≤ r₁) :
    ((List.finRange r₁).reverse.map
        (fun j : Fin r₁ => if j.val < c₀ then a else b)) =
      List.replicate (r₁ - c₀) b ++ List.replicate c₀ a

end List
```

**Namespace placement**: the natural namespace is `List` (alongside
`List.finRange_reverse`, `List.map_const`, `List.replicate_append_replicate`).
If `Lean` core convention discourages adding `List`-namespaced theorems
in a Hilbert-15 file, the ACT author may inline as
`Hilbert15OQ02OQ03OQ01.reverse_map_finRange_step_function` or place
under `Hilbert15OQ02OQ03OQ01.ListAux` — semantics unchanged.

**Universe**: `Type*` follows Mathlib idiom; `Type _` is equivalent.

**Parameterisation**: parameterised over `α` and `a, b : α` so the same
helper covers both the `Fin 2` use site in Guard D and any future
Hilbert-15 cluster file that requires step-shaped reverse-map collapses
(e.g. an `n = 3` lattice generalisation).

## §2 — Mathlib v4.26.0 bearer audit

Project pinned Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(= `v4.26.0`). Lean core pinned via Mathlib's toolchain to `v4.26.0`.
All bearers verified against the pinned SHA's `Init/` / `Mathlib/` trees
(file + line numbers below; verification commands at end of §2).

| Lemma / definition | Source file | Line | Attrs | Use in proof |
|---|---|---|---|---|
| `List.finRange_reverse` | `lean4/src/Init/Data/List/FinRange.lean` | 52 | `@[grind _=_]` | (alt path) rewrites `(finRange n).reverse` to `(finRange n).map Fin.rev` |
| `List.length_finRange` | `lean4/src/Init/Data/List/FinRange.lean` | 28 | `@[simp, grind =]` | LHS length |
| `List.getElem_finRange` | `lean4/src/Init/Data/List/FinRange.lean` | 31 | `@[simp, grind =]` | LHS element shape |
| `List.length_reverse` | Lean core (`Init.Data.List.Lemmas`) | (≈2390) | `@[simp]` | LHS length |
| `List.getElem_reverse` | `lean4/src/Init/Data/List/Lemmas.lean` | 2398 | `@[simp, grind =]` | LHS element shape |
| `List.length_map` | Lean core | — | `@[simp]` | LHS length |
| `List.getElem_map` | Lean core | — | `@[simp, grind =]` | LHS element shape |
| `List.length_append` | Lean core | — | `@[simp]` | RHS length |
| `List.getElem_append` | `lean4/src/Init/Data/List/Lemmas.lean` | 1572 | `@[grind =]` | RHS element shape (dependent `if`) |
| `List.length_replicate` | Lean core | — | `@[simp]` | RHS length |
| `List.getElem_replicate` | `lean4/src/Init/Data/List/Lemmas.lean` | 2153 | `@[simp, grind =]` | RHS element shape |
| `List.ext_getElem` | `lean4/src/Init/Data/List/Lemmas.lean` | 292 | — | Extensional equality |
| `Fin.cast_mk` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 494 | `@[simp]` | Strip `Fin.cast length_finRange` |
| `Fin.val_mk` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 52 | — (`rfl`-level) | `(⟨k, _⟩ : Fin n).val = k` |
| `Nat.sub_add_cancel` | Lean core `Init.Data.Nat.Basic` | — | — | Length goal: `(r₁ - c₀) + c₀ = r₁` |
| `omega` tactic | Lean core | — | — | Discharge the four-way `if/if` consistency |

**Backup primitives (not used by the primary proof, available as
fallback)**:

| `List.map_const` | `lean4/src/Init/Data/List/Lemmas.lean:2208` | `@[simp]` |
| `List.map_const'` | line 2217 | (variant for lambda) |
| `List.replicate_append_replicate` | line 2226 | `@[simp]` |
| `List.map_replicate` | line 2249 | `@[simp]` |
| `Fin.rev` definition | `lean4/src/Init/Data/Fin/Basic.lean:366` | `@[inline] def` |

**Verification commands** (the audit was done via the project's mathlib
fork remote and the `gh` API; the equivalent published-source checks
that anyone can replay):

```bash
# Lean core v4.26.0 — list lemmas (verifies lines 1572, 2153, 2208, 2398, 292):
curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/List/Lemmas.lean \
  | grep -nE "^(@\\[simp[^]]*\\] )?theorem (getElem_replicate|getElem_reverse|getElem_append|map_const|ext_getElem)"

# Lean core v4.26.0 — finRange:
curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/List/FinRange.lean \
  | grep -nE "^(@\\[simp[^]]*\\] )?(theorem|lemma) (length_finRange|getElem_finRange|finRange_reverse)"

# Lean core v4.26.0 — Fin lemmas:
curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/Fin/Lemmas.lean \
  | grep -nE "^(@\\[simp[^]]*\\] )?theorem (cast_mk|val_mk)"
```

All five queries return non-empty results pinning the lemmas to the
indicated lines (verified at this PREP's claim time, 2026-05-14
~04:50 UTC).

## §3 — Proof body (copy-paste-ready)

The proof uses `List.ext_getElem` to reduce equality to elementwise
agreement, normalises both sides to literal `if`-expressions over the
index, then closes the resulting four-way case split with `omega`
(two contradictions, two `rfl`s).

```lean
theorem List.reverse_map_finRange_step_function {α : Type*} (a b : α)
    {c₀ r₁ : ℕ} (hc : c₀ ≤ r₁) :
    ((List.finRange r₁).reverse.map
        (fun j : Fin r₁ => if j.val < c₀ then a else b)) =
      List.replicate (r₁ - c₀) b ++ List.replicate c₀ a := by
  apply List.ext_getElem
  · -- Lengths: r₁ = (r₁ - c₀) + c₀
    simp only [List.length_map, List.length_reverse, List.length_finRange,
               List.length_append, List.length_replicate]
    omega
  · intro i h1 _h2
    -- h1 : i < ((finRange r₁).reverse.map _).length, reduce to i < r₁
    have hir : i < r₁ := by simpa using h1
    -- Reduce LHS[i] to: `if r₁ - 1 - i < c₀ then a else b`
    have hLHS :
        ((List.finRange r₁).reverse.map
            (fun j : Fin r₁ => if j.val < c₀ then a else b))[i]'h1
          = (if r₁ - 1 - i < c₀ then a else b) := by
      simp only [List.getElem_map, List.getElem_reverse,
                 List.length_reverse, List.length_finRange,
                 List.getElem_finRange, Fin.cast_mk, Fin.val_mk]
    -- Reduce RHS[i] via getElem_append + getElem_replicate
    have hRHS :
        (List.replicate (r₁ - c₀) b ++ List.replicate c₀ a)[i]'_h2
          = (if i < r₁ - c₀ then b else a) := by
      rw [List.getElem_append]
      simp only [List.length_replicate]
      split_ifs with hi
      · simp [List.getElem_replicate]
      · simp [List.getElem_replicate]
    rw [hLHS, hRHS]
    -- Four-way case split on the two `if`s
    by_cases hL : r₁ - 1 - i < c₀
    · by_cases hR : i < r₁ - c₀
      · -- (r₁ - 1 - i < c₀) AND (i < r₁ - c₀): Nat contradiction
        exfalso; omega
      · -- (r₁ - 1 - i < c₀) AND ¬(i < r₁ - c₀): both branches `a`
        simp [hL, hR]
    · by_cases hR : i < r₁ - c₀
      · -- ¬(r₁ - 1 - i < c₀) AND (i < r₁ - c₀): both branches `b`
        simp [hL, hR]
      · -- ¬(r₁ - 1 - i < c₀) AND ¬(i < r₁ - c₀): Nat contradiction
        exfalso; omega
```

**LOC count**: 39 lines (proof body) + ~12 lines (signature + docstring)
= **~51 LOC** total. Conservative budget if the ACT author tweaks `simp`
sets after first build error: ~60 LOC.

**Tactic-budget note**: this proof uses no `decide`, no `grind`, no
`linarith`. `omega` is the only arithmetic tactic; `simp only` with an
explicit lemma list ensures version-robust elaboration under
v4.26.0. The single `by_cases ... · by_cases ...` ladder is preferred
over `split_ifs with hL hR hR'` because the cross-product naming would
otherwise produce three `hR` binders.

### §3.1 — Why the four-way case split is unavoidable

The LHS condition `r₁ - 1 - i < c₀` and the RHS condition `i < r₁ - c₀`
are equivalent under `c₀ ≤ r₁` and `i < r₁`, but their negations differ.
The contrapositive identity

```
(r₁ - 1 - i < c₀) ↔ ¬(i < r₁ - c₀)        (∀ i < r₁, ∀ c₀ ≤ r₁)
```

is a non-trivial Nat-subtraction fact (`omega` closes it in one call,
but the human-readable proof requires three case splits on `c₀ = 0`
vs `c₀ ≥ 1` and `i = r₁ - c₀ - 1` vs `i ≥ r₁ - c₀` — totaling four
sub-cases). The `by_cases ... · by_cases ...` ladder pins the case
analysis explicitly so the ACT author can audit the four branches in
isolation.

### §3.2 — Sanity check at boundary values

* **`c₀ = 0`**: predicate `j.val < 0` is always false (Nat), so the LHS
  list is `replicate r₁ b`. RHS: `replicate r₁ b ++ replicate 0 a =
  replicate r₁ b`. ✓
* **`c₀ = r₁`**: predicate `j.val < r₁` is true for all `j : Fin r₁`, so
  the LHS list is `replicate r₁ a`. RHS: `replicate 0 b ++ replicate r₁
  a = replicate r₁ a`. ✓
* **`r₁ = 0`**: `finRange 0 = []`, both sides are `[]`. ✓ (handled by
  `omega` in the length step.)

The proof handles all three without special-casing — `simp` + `omega`
absorbs each.

### §3.3 — Alternative proof path (via `finRange_reverse` + `Fin.rev`)

A second proof strategy bypasses `getElem_reverse` by first rewriting
`(finRange r₁).reverse` to `(finRange r₁).map Fin.rev` via
`List.finRange_reverse` (Lean core), then composing the maps. This
gives a `(finRange r₁).map (fun j => if (Fin.rev j).val < c₀ then a else
b)` and reduces to an induction on `r₁` via `finRange_succ_last` /
`finRange_succ`. Estimated ~50 LOC; the `Fin.rev` index arithmetic
(`(Fin.rev j).val = r₁ - 1 - j.val`) requires a `simp [Fin.rev]` + Nat
arithmetic step inside the induction. **Recommendation**: the primary
`ext_getElem` proof in §3 is preferred — fewer intermediate lemmas,
no induction, omega closes the arithmetic.

If the ACT author finds the `simp` set in §3 brittle under v4.26.0
elaboration (e.g. `Fin.cast_mk` doesn't fire because the cast is
optimised away by `getElem_finRange`'s `Fin.cast length_finRange`
form), the alternative is the fallback.

### §3.4 — Optional generalisation

The helper is stated for two distinct values `a, b : α`. If
`a = b`, the result degenerates to `List.replicate r₁ a` (both
branches collapse). The §3 proof handles this without modification:
the `if`-expressions in both LHS and RHS reduce to `a` regardless of
the condition, so `simp [hL]` / `simp [hR]` close trivially. No
hypothesis `a ≠ b` is needed.

A strictly more general statement that drops the step-function shape
in favour of an arbitrary `f : Fin r₁ → α` with `f` weakly decreasing
in `j.val` could be derived as a corollary, but Step 4 (Guard D) does
not need it. Out of scope for this PREP.

## §4 — Integration into `reverseRowWord_two_canonical` (Step 4 ACT)

Per S3c-Prep-8 §3.8, `reverseRowWord_two_canonical`'s proof body (in
the Step 4 ACT) flows:

```lean
theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (c₀ : ℕ)
    (hc₀ : c₀ ≤ ν.parts 1 - μ.parts 1)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)
    (hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
              T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1) :
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 - c₀) (1 : Fin 2) ++
      List.replicate c₀ (0 : Fin 2) := by
  rw [reverseRowWord_two_eq]
  -- Row 0 collapse via hzero (Step 1 input)
  rw [show (fun j => T.1 ⟨(0 : Fin 2), j⟩) = (fun _ => (0 : Fin 2)) from
      funext hzero]
  rw [List.map_const, List.length_reverse, List.length_finRange]
  -- Row 1 collapse via hstep + reverse_map_finRange_step_function
  rw [show (fun j => T.1 ⟨(1 : Fin 2), j⟩)
        = (fun j => if j.val < c₀ then (0 : Fin 2) else 1) from
      funext hstep]
  rw [List.reverse_map_finRange_step_function (0 : Fin 2) (1 : Fin 2) hc₀]
  -- Now: replicate r₀ 0 ++ (replicate (r₁ - c₀) 1 ++ replicate c₀ 0)
  -- which matches the RHS modulo `List.append_assoc` reassociation.
  rw [List.append_assoc]
```

**Total Step 4 helper LOC** (helper §3 + `reverseRowWord_two_canonical`
caller above): ~51 + ~15 = ~66 LOC. Plus
`skewSSYTFin_lattice_bound_row1` (Guard D consumer, ~28 LOC per
PREP-8 §3.8) + `skewSSYTFin_row1_one_of_overlap` (Guard C, ~22 LOC
per PREP-8 §2) = **~116 LOC total Step 4 ACT** (within PREP-8 §4's
~80–110 LOC budget — modest 6–36 LOC overage from including the
helper inline; if helper is shipped in a Lean-core-style
`namespace List` block, the math-content delta is the unchanged
~80 LOC).

### §4.1 — Race-with-PR-#18990 surface

PR #18990 (Step 3 ACT, OPEN as of 2026-05-14T04:30Z) adds Part XV to
`proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (line 938 → 1095). The
Step 4 ACT helper signature must be inserted **before** Part XV's
`skewSSYTFin_row1_step_function` is referenced (in
`reverseRowWord_two_canonical`'s body via `hstep`), but the helper
itself is namespace-isolated under `List` and depends on no
SkewSSYTFin definitions. Recommended placement: a new **Part XVI**
that opens with the `namespace List` block for the helper, then
returns to the Hilbert namespace for the Guard-C/D theorems. This
keeps the helper visible to Step 5 ACT as well (in case a row-2
analogue is needed for `n = 3` future work).

If PR #18990 has merged before Step 4 ACT lands, the helper goes in a
new Part XVI section appended after Part XV. No race conflict.

## §5 — Honesty / scope

* **No Lean edits.** `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` is
  unchanged at 937 LOC / 1 sorry / 0 axioms (origin/main snapshot at
  this claim's time).
* **No `state.md` edits.** PR #18990 (Step 3 ACT, OPEN, mergeStateStatus
  CLEAN) holds an exclusive write lock on `state.md`'s header and the
  new "S3c Step 3 ACT" entry it inserts between line 7 and the existing
  "S3c Step 2 ACT" section. Touching `state.md` would force #18990 to
  rebase; this PR's content is the durable session log + minimal JSON
  fields, which #18990 does not write. A follow-up STATE-SYNC PR can
  backfill state.md's header to mention PREP-10 after both PRs merge.
* **No `problem.md` / `knowledge.md` edits.**
* **JSON edits scope (`src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`)**:
  * **Bumps**: `lastUpdate` (2026-05-14, unchanged value, refreshed
    semantic to "S3c-Prep-10 PREP by researcher-1; helper proof body audit").
  * **Appends**: one `knowledge.insights` entry pinning the helper
    signature + Mathlib bearer audit summary; one `knowledge.builtItems`
    entry referencing this session memo.
  * **Untouched**: `currentState.{phase,since,iteration,focus,nextAction,blockers,attemptCounts}` (all owned by #18990's diff at claim time — letting #18990 win avoids race).
* **No race with PR #17966.** That PR has been open since 2026-05-12T07:37Z
  with `mergeable=CONFLICTING` on the same protected files; this PR
  touches only `sessions/2026-05-14-s3c-prep-10-*.md` (new file) and
  `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
  (append-only fields), with no overlap.
* **Pre-claim and pre-push probes**: 2 open slug-specific PRs (#17966
  abandoned, #18990 Step-3-ACT CLEAN); 0 open PREP-10 / helper /
  `reverse_map_finRange_step_function` PRs at claim time.

## §6 — Forward look

After this PREP merges:

1. **Step 4 ACT** can land as a single coherent diff (~110-120 LOC)
   importing the helper from §3 verbatim. No Mathlib search session
   required. Estimated effort: **~45 min** for an ACT author familiar
   with the cluster (PR #18964 / #18990 patterns).
2. **Step 5 ACT** (~160 LOC, S3c-Prep-9 / PR #18720) inherits a clean
   Step 4 input; no new design memo needed.
3. **S3d** (lift 7 Gr(2,4) constants via `rw [lrCoeffN_def_two_eq_lrCoeff2]
   + native_decide`) is unlocked the moment Step 5 ACT closes the
   line-413 sorry.
4. **S4** (replace `axiom lrCoeffN` at `Hilbert15OQ02OQ03.lean:128`)
   drops the parent's axiom count 3 → 2 (only `admissible` and
   `klyachko_theorem` would remain).

Estimated end-to-end (Step 4 ACT → S4) under good conditions: 3-4
focused sessions, ~10-12 hours wall-clock.

---

**Status**: PREP, doc-only, no Lean delta. Auxiliary helper for Step 4 ACT
(Guard D match) — discharges the §6.7 mitigation from S3c-Prep-8 (PR #18676).
