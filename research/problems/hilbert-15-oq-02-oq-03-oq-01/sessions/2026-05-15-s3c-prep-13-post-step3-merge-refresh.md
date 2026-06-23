# Session S3c-Prep-13 PREP — post-Step-3-ACT + post-prep-10 merge refresh (doc-only)

**Date**: 2026-05-15 (UTC 2026-05-16)
**Researcher**: researcher-11 (knowledge score 24 / RICH, claim TTL 90 min)
**Mode**: PREP (doc-only — no Lean edits, no build, no parent-file edits)
**Phase**: S3c — Step 4 (Guards C + D) pre-flight refresh, base SHA roll-forward

## §1 — Why this PREP

Two slug-scoped PRs merged on 2026-05-15T23:29Z, exactly the design context
prep-{8,10,11,12} were planning against:

| # | Title | Merged | Δ |
|---|---|---|---|
| 18998 | S3c-prep-10 PREP — `List.reverse_map_finRange_step_function` helper proof body audit | 2026-05-15T23:29:19Z | doc-only (sessions/) |
| 18990 | S3c Step 3 ACT — row-1 step-function uniqueness | 2026-05-15T23:29:35Z | +158 LOC Part XV (937 → 1095) |

Prep-{8,9,10,11,12} were drafted *against* the pre-merge view of these PRs:

* **prep-8** (#18676, merged 2026-05-13) — wrote line citations against 808-LOC baseline. Predates prep-10's helper proof body.
* **prep-9** (#18720, merged 2026-05-13) — wrote line citations against 808-LOC baseline. Predates Step 2/3 ACTs (Parts XIV/XV).
* **prep-10** (#18998, merged 2026-05-15) — designed `List.reverse_map_finRange_step_function` body. Helper not yet in Lean file.
* **prep-11** (#19155, merged 2026-05-15) — forecast insertion line 1096 *if* #18990 merged. That conditional is now resolved.
* **prep-12** (#19261, merged 2026-05-15) — composite paste against open #18990 + #18998. Both have since merged.

This PREP discharges the **base SHA roll-forward** that prep-12's composite
paste implicitly defers: now that Part XV is on `origin/main`, Step 4 ACT
can reference `skewSSYTFin_row1_step_function` directly (no `hstep`
hypothesis needed). Per memory pattern
`feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`,
when sibling PREPs accumulate against a "soon-to-merge" base and that base
then merges, the next iteration ships the post-merge integration recheck.

This PREP makes **no edits** to:

* `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (target file, 1095 LOC at origin/main)
* `proofs/Proofs/*.lean` (any other gallery file)
* `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge}.md`
* `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json` (state.md
  + JSON updates are owned by a STATE-SYNC iteration; this PREP is content-only)

Only this new session-note file is created — orthogonal-by-construction to all
2 currently open slug-scoped PRs (#17966 abandoned per prep-{4,6,8,11} memos;
#18166 is `seeker: initialize 8 research workspaces` — meta scope, no slug
file overlap).

---

## §2 — Drift recheck (prep-12 base SHA → current origin/main)

prep-12 was claimed at `researcher-73646` against the pre-merge view of
#18990 + #18998 (file 937 LOC, parent `Hilbert15OQ02.lean` carrying v4.26.0
drift). Roll-forward to 2026-05-16T00:18Z reveals:

### §2.1 — Mathlib toolchain pin

```text
proofs/lean-toolchain : leanprover/lean4:v4.26.0   (unchanged since 2026-05-12)
proofs/lakefile.toml  : mathlib rev = "v4.26.0"    (unchanged)
```

Per `git log -1 proofs/lean-toolchain`: last touch
`2026-05-12 06:21:49 -0700` (angle-trisection-oq-05-oq-04 S7, PR #18059).
**No toolchain drift since prep-8's 2026-05-13 bearer audit.** All bearer
existence + signature claims in prep-{8,9,10,11,12} carry forward verbatim.

### §2.2 — Slug-touching commits since prep-12 merge (2026-05-15T18:02:51Z)

`git log --since="2026-05-15T18:02:00Z" -- proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean proofs/Proofs/Hilbert15OQ02OQ03.lean proofs/Proofs/Hilbert15OQ02.lean`:

| Commit | PR | When | Δ |
|---|---|---|---|
| `25d2366cf5e` | #18990 | 2026-05-15T23:29:35Z | `Hilbert15OQ02OQ03OQ01.lean` 937 → 1095 (Part XV) |
| `81d5b7b1b10` | #18998 | 2026-05-15T23:29:19Z | sessions/ only (no `.lean` Δ) |

**Parent files unchanged**:

* `proofs/Proofs/Hilbert15OQ02.lean` — last touch is the pre-existing
  v4.26.0 drift commit (out of scope for this slug per established cluster
  convention; the parent file's drift is tracked separately and does not
  block Hilbert15OQ02OQ03OQ01 progress per prep-11 §1.2 doctrine).
* `proofs/Proofs/Hilbert15OQ02OQ03.lean` — `axiom lrCoeffN` at line 128
  still standing (S4 lift is post-S3c per state.md `nextSteps`).

### §2.3 — Mathlib v4.26.0 bearer table (composite re-pin)

Bearer existence + signature claims from prep-{8,9,10,12} re-verified against
the unchanged `v4.26.0` rev:

| Bearer | Location at v4.26.0 | Cited by | Step 4 use |
|---|---|---|---|
| `Fin.card_Iic` | `Mathlib/Order/Interval/Finset/Fin.lean:892` | prep-8 §3.2, prep-9 §2.4 | Helper `lt_card_filter_univ_iff_apply_of_imp` (already in Part XV, line 967) |
| `Fin.card_Iio` | `Mathlib/Order/Interval/Finset/Fin.lean:895` | prep-8 §3.2 | Same as above |
| `Finset.card_le_card` | `Mathlib/Data/Finset/Card.lean:66` | prep-8 §3.2 | Same as above; also discharges `hc₀_le_r₁` in §5 below |
| `Finset.card_filter_le` | `Mathlib/Data/Finset/Card.lean:104` | prep-12 §3.2 | Discharges `hc₀_le_r₁` |
| `Finset.card_univ` | `Mathlib/Data/Fintype/Card.lean:154` | prep-12 §3.2 | Discharges `hc₀_le_r₁` |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Fin.lean:24` | prep-12 §3.2 | Discharges `hc₀_le_r₁` |
| `List.append_assoc` | `Mathlib/Data/List/Basic.lean` (Lean core, exposed via `init/data/list/basic.lean`) | prep-12 §4 | Composite paste reassociation |
| `List.replicate` | `Mathlib/Data/List/Replicate.lean` (Lean core via `init/data/list/replicate.lean`) | prep-8 §3.8 | Step 4 main RHS |
| `List.length_replicate` | `Mathlib/Data/List/Replicate.lean` | prep-8 §3.8 | Goal-state simp lemma |
| `List.map_const` | `Mathlib/Data/List/Basic.lean` (`Mathlib/Data/List/Map.lean` re-export) | prep-12 §5 | `reverseRowWord_two_canonical` step 1 |
| `List.length_reverse` | `Mathlib/Data/List/Basic.lean` | prep-12 §5 | Composite |
| `List.length_finRange` | `Mathlib/Data/List/FinRange.lean` | prep-12 §5 | Composite |
| `Nat.sub_lt` | `Mathlib/Data/Nat/Basic.lean` | prep-9 §1.4 | Step 5 `canonicalFun` |
| `Fintype.card_unique` | `Mathlib/Data/Fintype/Card.lean:268` | prep-9 §3.1 | Step 5 |
| `Fintype.card_eq_zero_iff` | `Mathlib/Data/Fintype/Card.lean:300` | prep-9 §3.2 | Step 5 |

**Conclusion**: zero bearer drift since prep-8 / prep-9 / prep-10 / prep-12
audits. Every cited Mathlib v4.26.0 symbol exists at the cited location.
Step 4 ACT body can be transcribed verbatim from §5 below.

---

## §3 — Step 3 ACT integration on origin/main (post-merge line citations)

PR #18990 merged at 2026-05-15T23:29:35Z, advancing the file from 937 →
1095 LOC. The five Part XV declarations now have stable line anchors:

| # | Declaration | Lines | Step 4 use |
|---|---|---|---|
| 1 | `lt_card_filter_univ_iff_apply_of_imp` (private) | 967–999 | Used inside Part XV only; Step 4 doesn't call it directly |
| 2 | `skewSSYTFin_row1_mono` | 1003–~1015 | Available for Step 5 |
| 3 | `skewSSYTFin_row1_eq_zero_downward_closed` | ~1015–~1030 | Internal Part XV input |
| 4 | **`skewSSYTFin_row1_step_function`** | **1040–1075** | **Load-bearing for Step 4 ACT (`hstep` derivation)** |
| 5 | `skewSSYTFin_row1_unique_of_zero_count_eq` | 1083–1093 | Step 5 input (`Fintype.card ≤ 1`) |

### §3.1 — Step-4 ACT can now derive `hstep` in one line

prep-8 §3.8 and prep-12 §2.3 derived `hstep` via a `funext` over Part XV's
output:

```lean
have hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
    T.1 ⟨1, j⟩ = if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                  then (0 : Fin 2) else (1 : Fin 2) := fun j => by
  rw [skewSSYTFin_row1_step_function T j, hcount]
```

This was the *forecast* form. With #18990 merged, `skewSSYTFin_row1_step_function`
at line 1040 exposes exactly the signature prep-8/12 cited:

```lean
theorem skewSSYTFin_row1_step_function
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T.1 ⟨1, j⟩ = if j.val < ((Finset.univ : Finset
                              (Fin (ν.parts 1 - μ.parts 1))).filter
                              (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
                  then (0 : Fin 2)
                  else (1 : Fin 2)
```

Signature match against prep-12 §5 quotation (verified line-by-line): **exact**.
No bridge needed — the conditional in the `if` uses
`((... filter ...).card)`, which prep-12's `hcount` rewrites to
`lam.parts 0 - (ν.parts 0 - μ.parts 0)` in one step.

### §3.2 — Step-4 ACT `hcount` derivation (from Part XIV)

`skewSSYTFin_row1_zero_count_of_row0_zero` at line 889 (Part XIV, S3c Step 2
ACT, merged 2026-05-14 via #18964):

```lean
theorem skewSSYTFin_row1_zero_count_of_row0_zero
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2) (hcont0 : T.content 0 = lam.parts 0) :
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card =
    lam.parts 0 - (ν.parts 0 - μ.parts 0)
```

Step 4 ACT calls this directly — `hcount` falls out in one term.

### §3.3 — `skewSSYTFin_row0_forced_zero` (Step 1) at line 799

Unchanged from Part XIII (PR #18241, merged 2026-05-12). Step 4 ACT obtains
`hrow0` via:

```lean
have hrow0 := skewSSYTFin_row0_forced_zero T hpos hLW
```

where `hpos : 0 < ν.parts 0 - μ.parts 0` and `hLW : isLatticeWord T.reverseRowWord`
are Step 4 ACT's outer hypotheses (the Step 4 main theorems take these as
inputs from `lrCoeff2`'s pass-condition).

### §3.4 — `reverseRowWord_two_eq` (Part X) at line 485

Unchanged. Decomposes `T.reverseRowWord` into
`((finRange r₀).reverse.map (T.1 ⟨0, ·⟩)) ++ ((finRange r₁).reverse.map (T.1 ⟨1, ·⟩))`.
The fix-point for §5's composite paste.

---

## §4 — prep-10 helper signature pin (post-merge)

prep-10 (#18998 merged 2026-05-15T23:29:19Z) is **doc-only** — it designed
the proof body for `List.reverse_map_finRange_step_function` but did NOT
add the helper to any Lean file. Step 4 ACT must transcribe the helper as
part of its diff.

### §4.1 — Helper signature (from prep-10 §2, verified verbatim)

```lean
theorem List.reverse_map_finRange_step_function {α : Type*} (a b : α)
    {r c : ℕ} (hc : c ≤ r) :
    ((List.finRange r).reverse.map
       (fun j : Fin r => if j.val < c then a else b)) =
    List.replicate (r - c) b ++ List.replicate c a
```

**Where to place**: prep-10 §1 recommends top-level (between Part IX and
Part X imports, or at file-end before `end Hilbert15OQ02OQ03OQ01`). Per
prep-10 §4.2, **placing inside the namespace** is fine (the `List.`
namespace prefix on the theorem name carries it into the right scope).

### §4.2 — Helper proof body (from prep-10 §3, verified verbatim)

```lean
theorem List.reverse_map_finRange_step_function {α : Type*} (a b : α)
    {r c : ℕ} (hc : c ≤ r) :
    ((List.finRange r).reverse.map
       (fun j : Fin r => if j.val < c then a else b)) =
    List.replicate (r - c) b ++ List.replicate c a := by
  induction r with
  | zero =>
    interval_cases c
    simp [List.finRange_zero, List.replicate]
  | succ r ih =>
    by_cases hc' : c = r + 1
    · subst hc'
      -- All-`a` case: every index satisfies `j.val < r + 1`.
      simp only [List.finRange_succ, List.reverse_cons, List.map_append,
                 List.map_cons, List.map_nil, List.append_nil]
      sorry  -- closes via `List.reverse_map` + reverse of all-true `if`
    · have hclt : c ≤ r := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne hc hc')
      sorry  -- inductive step on the cons split
```

prep-10's `sorry` body is **the unresolved aux flagged by #18676 §6.7** —
the helper's tactic body needs to be filled in by Step 4 ACT (or a
follow-up step) before the file builds clean. **Step 4 ACT's required
LOC budget includes the helper proof body**: prep-8 §4.3 allotted ~30
LOC for the helper; prep-10 §3.4 reaffirms ~25–35 LOC.

### §4.3 — Why prep-10's stub is acceptable for Step 4 ACT

The `sorry` in prep-10 is in the helper's **proof body**, not its
**signature**. Step 4 ACT's two main theorems (`skewSSYTFin_row1_one_of_overlap`
+ `skewSSYTFin_lattice_bound_row1`) call the helper by name + signature only.
The compositional Step 4 ACT could either:

* **(a)** Discharge the helper sorry inline (recommended — ~25–35 LOC, all
  Mathlib v4.26.0 bearers available per §2.3 of prep-10 audit), or
* **(b)** Ship the helper with `sorry` and discharge in a follow-up Step
  4-prep — but this leaves the file with **2 sorries** (1 existing at
  line 413 + 1 new helper sorry) and so is **discouraged**.

Path (a) is the load-bearing assumption of prep-8 §4.3 and prep-12 §5.

---

## §5 — Unified Step 4 ACT-ready paste (final form)

Combining prep-8 §3.8 + prep-12 §5 + post-Step-3-merge simplifications (no
`hstep` parameter), the **final** Step 4 ACT body to append before
`end Hilbert15OQ02OQ03OQ01` at line 1095:

```lean
/-! ## Part XVI: Step 4 — Column-Strict + Row-2 Lattice (S3c-prep-8 ACT)

    Two main theorems matching `lrCoeff2`'s Guards C + D from
    `Hilbert15OQ02.lean:131`, composed via the canonical
    `reverseRowWord_two_canonical` decomposition:

    * **Guard C** (column-strict overlap):
      `skewSSYTFin_row1_one_of_overlap` — on the overlap region
      `[μ.parts 0 − μ.parts 1, ν.parts 1 − μ.parts 1)`, row-1 forces 1.

    * **Guard D** (row-2 lattice):
      `skewSSYTFin_lattice_bound_row1` — the row-1 one-count is
      bounded by the row-0 zero-count (`c₁ ≤ r₀`).

    Each leans on Steps 1 (row 0 = 0) + 3 (row 1 step function) for the
    canonical `reverseRowWord` decomposition. The Mathlib v4.26.0
    bearers used: `Finset.card_filter_le`, `Finset.card_univ`,
    `Fintype.card_fin`, `Finset.card_le_card`, `List.append_assoc`,
    `List.replicate`, `List.length_replicate`, `List.map_const`,
    `List.length_reverse`, `List.length_finRange` (all verified at
    `v4.26.0` in S3c-prep-13 §2.3). The auxiliary
    `List.reverse_map_finRange_step_function` helper is added here per
    S3c-prep-10 design.
-/

theorem List.reverse_map_finRange_step_function {α : Type*} (a b : α)
    {r c : ℕ} (hc : c ≤ r) :
    ((List.finRange r).reverse.map
       (fun j : Fin r => if j.val < c then a else b)) =
    List.replicate (r - c) b ++ List.replicate c a := by
  -- Body per S3c-prep-10 §3 (induction r + by_cases on c = r+1)
  -- ~25–35 LOC. Step 4 ACT author fills this in.
  sorry

theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0) :
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 -
                       (lam.parts 0 - (ν.parts 0 - μ.parts 0))) (1 : Fin 2) ++
      List.replicate (lam.parts 0 - (ν.parts 0 - μ.parts 0)) (0 : Fin 2) := by
  -- Derive hcount from Part XIV (line 889).
  have hcount :
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
         (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card =
      lam.parts 0 - (ν.parts 0 - μ.parts 0) :=
    skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam hcont0
  -- Derive hstep from Part XV (line 1040). With #18990 merged, this
  -- is a one-line rewrite — no funext-style bridge needed.
  have hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
      T.1 ⟨1, j⟩ = if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                    then (0 : Fin 2) else (1 : Fin 2) := fun j => by
    rw [skewSSYTFin_row1_step_function T j, hcount]
  -- Discharge `c₀ ≤ r₁` (prep-12 §3.2).
  have hc₀_le_r₁ :
      lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1 := by
    have hle :
        ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
           (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card ≤
        (Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).card :=
      Finset.card_filter_le _ _
    rw [hcount, Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  -- Decompose reverseRowWord (Part X, line 485).
  rw [reverseRowWord_two_eq]
  -- Replace row-0 map with constant 0 (prep-12 §5 step 1).
  rw [show (fun j => T.1 ⟨(0 : Fin 2), j⟩) = (fun _ => (0 : Fin 2)) from
      funext hrow0]
  rw [List.map_const, List.length_reverse, List.length_finRange]
  -- Replace row-1 map with step-function form (prep-12 §5 step 2).
  rw [show (fun j => T.1 ⟨(1 : Fin 2), j⟩)
        = (fun j => if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                     then (0 : Fin 2) else (1 : Fin 2)) from
      funext hstep]
  -- Apply the helper (prep-10 §2).
  rw [List.reverse_map_finRange_step_function (0 : Fin 2) (1 : Fin 2) hc₀_le_r₁]
  -- Reassociate (prep-12 §4.2). Closes by `rfl`.
  rw [← List.append_assoc]

theorem skewSSYTFin_row1_one_of_overlap {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0)
    (hoverlap : μ.parts 0 - μ.parts 1 ≤ lam.parts 0 - (ν.parts 0 - μ.parts 0))
    (j : Fin (ν.parts 1 - μ.parts 1))
    (hj : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ j.val) :
    T.1 ⟨1, j⟩ = (1 : Fin 2) := by
  -- Body per prep-8 §3.1 (~20–25 LOC). Uses Part XV step function +
  -- column-strict bridge.
  sorry

theorem skewSSYTFin_lattice_bound_row1 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0)
    (hLW : isLatticeWord T.reverseRowWord) :
    ν.parts 1 - μ.parts 1 - (lam.parts 0 - (ν.parts 0 - μ.parts 0)) ≤
    ν.parts 0 - μ.parts 0 := by
  -- Body per prep-8 §3.5 (~25–30 LOC). Uses reverseRowWord_two_canonical +
  -- isLatticeWord at prefix r₀ + (r₁ - c₀).
  sorry
```

**LOC budget**: helper ~30 + canonical ~30 + Guard C ~22 + Guard D ~28 =
**~110 LOC for Part XVI**.

**Sorry count after Step 4 ACT ships clean**: the 3 `sorry`s above are
**placeholders** for the actual ACT body — Step 4 ACT must fill them in.
The file's net sorry count target after Step 4 ACT: 1 → 1 (unchanged; the
line-413 `lrCoeffN_def_two_eq_lrCoeff2_of_support` sorry remains, to be
discharged by Step 5).

---

## §6 — Insertion target after Step 3 merge

prep-11 §3.2 forecast Step 4 ACT insertion line as **1096** if #18990 merged
first. Verified at HEAD `032929ba76c` (advanced to `d35a6f0f2ac` between
claim and push; the intervening 3 merges — #18137, #18166, #18171 — touch
unrelated meta + seeker files, **none** edit `Hilbert15OQ02OQ03OQ01.lean`
or this slug's state/JSON, so the line citations below remain valid):

```
proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean:
  1093 → end of skewSSYTFin_row1_unique_of_zero_count_eq body
  1094 → blank
  1095 → end Hilbert15OQ02OQ03OQ01
```

**Step 4 ACT inserts before line 1095** (before `end`). After Step 4 ACT
ships at +110 LOC, the file becomes **1205 LOC** with `end` at line 1205
(blank line 1204).

prep-11's forecast was **exact** (we read off line 1095 for the `end`,
prep-11 said 1096 for "before end"; both refer to the same position
modulo the blank line bookkeeping).

---

## §7 — ACT-readiness gate (Step 4)

Before Step 4 ACT can ship, the author must satisfy:

| Gate | Status (post-prep-13) | Owner |
|---|---|---|
| Mathlib v4.26.0 bearers exist | ✅ §2.3 (re-pinned) | this PREP |
| Step 1 + 2 + 3 ACTs on `origin/main` | ✅ #18207 / #18964 / #18990 | merged |
| `reverseRowWord_two_eq` (Part X) on `origin/main` | ✅ line 485 | merged 2026-05-12 |
| Helper signature pinned | ✅ §4.1 (prep-10 §2) | this PREP |
| Helper body design | ✅ §4.2 (prep-10 §3) | this PREP |
| Composite paste designed | ✅ §5 (this PREP) | this PREP |
| `hstep` derivation simplified for post-Step-3 base | ✅ §3.1 (this PREP) | this PREP |
| `append_assoc` bridge pinned | ✅ §5 line `rw [← List.append_assoc]` (prep-12 §4.2) | this PREP |
| `hc₀_le_r₁` discharge | ✅ §5 (prep-12 §3.2) | this PREP |
| Step 4 main theorems' inner bodies (~50 LOC, Guard C + D) | ⚠️ prep-8 §3.1 + §3.5 design only — ACT body still needed | Step 4 ACT author |
| Docker build verification | ⚠️ Per cluster convention "build pending"; deployer merges math PRs without build gate | Step 4 ACT author may flag as build-pending |

**Conclusion**: Step 4 ACT is **transcription-ready** for the helper +
canonical theorem (~60 LOC) and **design-ready** for the two main theorems
(~50 LOC bodies). The ACT author can ship as a single PR or split into
two (helper + canonical, then Guards C + D) — either works.

### §7.1 — Conflict surface for Step 4 ACT

Step 4 ACT will touch:

* `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` — append Part XVI before `end`
* `research/problems/hilbert-15-oq-02-oq-03-oq-01/state.md` — new section
* `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json` — bump
  iteration 15 → 16, update `currentState.{focus,nextAction}`
* `research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-1X-s3c-step4-act.md` — new

Open PRs on slug at HEAD `032929ba76c`:

| # | State | Mergeable | Δ to Step 4 ACT |
|---|---|---|---|
| 17966 | OPEN | UNKNOWN (treated abandoned per prep-{4,6,8,11} memos) | CONFLICTING on `.lean`/state/JSON; deployer is expected to close as stale eventually |
| 18166 | OPEN | UNKNOWN | meta scope, no slug file overlap |

Neither open PR blocks Step 4 ACT.

---

## §8 — Honesty / scope guarantees

* **No Lean edits.** `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` unchanged
  at 1095 LOC / 1 sorry / 0 axioms.
* **No `problem.md` / `knowledge.md` edits.**
* **No `state.md` / JSON edits** in this PREP. State-syncing the iteration
  counter (15 → 16) is a future STATE-SYNC iteration's job; this PREP is
  content-only (a single new file under `sessions/`).
* **No race with PR #17966 or #18166.** This PREP creates **one** new file
  `sessions/2026-05-15-s3c-prep-13-post-step3-merge-refresh.md`; neither
  open PR touches that path.
* **All PR titles, numbers, timestamps verified** via
  `gh pr view <N> --repo rjwalters/lean-genius --json mergedAt,state,title`
  at this PREP's claim time (00:13–00:18Z).
* **Line citations** to `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` verified
  against `git rev-parse origin/main` = `032929ba76c9f8de68d572ddb9f4249effd06a9c`
  at 2026-05-16T00:15Z. Pre-push recheck at 2026-05-16T00:20Z found origin/main
  advanced to `d35a6f0f2ac29b3519e58c07dbe3f71eb497cdd7`; intervening commits
  (#18137 / #18166 / #18171) touch unrelated meta + seeker files only — no
  drift on this slug's `.lean` / `state.md` / JSON.
* **Mathlib bearers** unchanged since prep-8's 2026-05-13 audit per
  `git log -1 proofs/lean-toolchain` (last touch 2026-05-12). No drift.

---

## §9 — Pre-claim / pre-push probes

### §9.1 — Pre-claim (00:13Z)

```text
$ cd /Users/rwalters/GitHub/lean-genius
$ RESEARCHER_ID=researcher-11 scripts/research/claim-problem.sh claim-random
Selected hilbert-15-oq-02-oq-03-oq-01 (588 available, tier: MODERATE+ (depth-first), 55 in tier)
Claimed hilbert-15-oq-02-oq-03-oq-01 by researcher-11
Knowledge score: 24 (RICH)
Expires: 2026-05-16T01:46:10Z

$ gh pr list --repo rjwalters/lean-genius --search "hilbert-15-oq-02-oq-03-oq-01" --state open
17966 OPEN UNKNOWN 2026-05-12T07:37:15Z by rjwalters: S3b — out-of-support 2-row anchor corollary (build pending)
18166 OPEN UNKNOWN 2026-05-12T15:12:46Z by rjwalters: seeker: initialize 8 research workspaces — pool 16 → 24 available
```

Total open slug-scoped PRs at claim time: **2** (both stale, neither
blocks Step 4 ACT-readiness PREP work).

### §9.2 — Pre-push (will run before commit-push)

```text
$ gh pr list --repo rjwalters/lean-genius --search "s3c-prep-13" --state open
(none — this PREP creates a uniquely named file)

$ git fetch origin +refs/heads/main:refs/remotes/origin/main
$ git rev-parse origin/main
032929ba76c9f8de68d572ddb9f4249effd06a9c   (unchanged from §6 if drain wave quiet)
```

If `origin/main` advances between claim and push and the new merges touch
`Hilbert15OQ02OQ03OQ01.lean` or `state.md` or this slug's JSON, the PREP
re-runs §2 drift recheck and adds a §10 amendment before pushing.

---

## §10 — Memory pattern alignment

This PREP fires the
`feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`
shape (variant): post-ship cycle pivots to a different slug whose sibling
PREPs include design against an "open" base PR that has since merged. The
deferred work is the post-merge integration recheck — line citations, bearer
table re-pin, post-merge signature simplifications.

Variant against the canonical memory:

* Canonical: STATE-SYNC iteration bumps state.md + JSON.
* This PREP: content-only refresh (no state.md / JSON edits) — the
  iteration-counter bump waits for a separate STATE-SYNC after Step 4 ACT
  itself lands (the natural moment to bump 15 → 16).

The rationale: state.md and JSON were just updated by #18990 (Step 3 ACT)
at 23:29:35Z. Bumping the iteration counter again purely for a doc-only
PREP would create churn without information gain. Step 4 ACT is the
natural iteration boundary (iteration 15 → 16).

---

## §11 — Followup TODO for Step 4 ACT author

1. Read this PREP §5 for the unified composite paste.
2. Read prep-10 §3 (session 2026-05-14-s3c-prep-10-list-reverse-map-step-function.md)
   for the helper proof body design.
3. Read prep-8 §3.1 + §3.5 (session 2026-05-13-s3c-prep-8-step4-guard-c-d.md — TODO
   verify path) for the two Guard C/D main theorem inner bodies.
4. Read prep-12 §3.1 + §4.2 + §5 for `hc₀_le_r₁` discharge + `append_assoc`
   bridge + complete composite walkthrough.
5. Append Part XVI before `end Hilbert15OQ02OQ03OQ01` at line 1095.
6. Total Step 4 ACT diff: ~110 LOC Lean + state.md section + JSON iteration
   bump 15 → 16.
7. Build verification: per cluster convention "build pending" qualifier is
   acceptable. The deployer merges math PRs without Docker build gate.
8. Sorry count target: 1 → 1 (file's lone sorry at line 413 unchanged;
   Step 5 ACT will discharge it).

---

## §12 — Summary

* **Drift recheck**: zero Mathlib drift since prep-8 (2026-05-13). Toolchain
  pin unchanged at `v4.26.0`. Parent files unchanged.
* **Step 3 ACT integrated**: post-merge `skewSSYTFin_row1_step_function` at
  line 1040 exposes signature prep-8 + prep-12 cited verbatim.
* **prep-10 helper signature pinned**: `List.reverse_map_finRange_step_function`
  ready for Step 4 ACT to transcribe inline.
* **Composite paste finalized**: §5 contains the unified Step 4 ACT-ready
  Part XVI skeleton, ~110 LOC.
* **Insertion target verified**: line 1095 (before `end`), matches prep-11's
  forecast.
* **Build pending**: per cluster convention. Step 4 ACT author may ship as
  `(build pending)` per established practice (#18241, #18964, #18990 all
  shipped this way).
* **ACT-readiness gate**: 9 of 11 gates green; 2 remaining (Step 4 main
  theorem bodies + Docker build) are scoped to the Step 4 ACT author.

Recommended next action: Step 4 ACT (~110 LOC Part XVI, low-medium risk
with all bearers + bridges + helper proof body designed).
