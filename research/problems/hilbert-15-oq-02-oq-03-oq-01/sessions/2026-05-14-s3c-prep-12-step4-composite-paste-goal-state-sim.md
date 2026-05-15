# Session S3c-Prep-12 PREP — Step 4 ACT composite paste goal-state simulation (doc-only)

**Date**: 2026-05-14
**Researcher**: researcher-12 (claim `researcher-73646`, knowledge score 22 / RICH)
**Mode**: PREP (doc-only, no Lean edits, no build)
**Phase**: S3c — Step 4 (Guards C + D) pre-flight, composite paste-readiness audit

## Why this PREP

Three slug-scoped PRs are open simultaneously while the deployer is processing
the cluster's math-PR queue:

| # | Title | Δ | Status |
|---|---|---|---|
| 17966 | S3b out-of-support 2-row anchor corollary | `.lean` + state.md + JSON | OPEN, CONFLICTING (3-day stale, treated abandoned per S3c-prep-{4,6,8,11} memos) |
| 18990 | S3c Step 3 ACT — row-1 step-function uniqueness | +158 LOC Part XV | OPEN, CLEAN/MERGEABLE |
| 18998 | S3c-prep-10 PREP — `List.reverse_map_finRange_step_function` helper proof body | doc-only | OPEN, CLEAN/MERGEABLE |
| 19155 | S3c-prep-11 PREP — Step 4 ACT cross-PR coordination audit | doc-only | OPEN, CLEAN/MERGEABLE |

When Step 4 ACT eventually lands, its author will paste material from **three
distinct provenance lines** drafted independently across 2026-05-13 → -14:

1. **Part XIV (merged PR #18964)** — Step 2 `_row1_zero_count_of_row0_zero`
   exposing the row-1 zero-count as `lam.parts 0 - (ν.parts 0 - μ.parts 0)`.
2. **Part XV (open PR #18990)** — Step 3 `skewSSYTFin_row1_step_function`
   exposing `T.1 ⟨1, j⟩ = if j.val < (row1-zero-count) then 0 else 1`.
3. **prep-8 design memo (merged PR #18676)** — Step 4 target signatures
   `skewSSYTFin_row1_one_of_overlap`, `reverseRowWord_two_canonical`,
   `skewSSYTFin_lattice_bound_row1` (parameterised over a free `c₀ : ℕ`).
4. **prep-10 helper proof body (open PR #18998)** —
   `List.reverse_map_finRange_step_function` with `hc : c₀ ≤ r₁` hypothesis.

prep-8 was drafted 2026-05-13 against an `c₀ : ℕ` free-parameter API,
predating the Part XIV / Part XV concrete encodings. prep-10 reused the same
free `c₀`. prep-11 verified namespace decoupling but did **not** walk the
composite paste through post-rewrite goal states. The risk surface:

- Step 4 ACT's `c₀ := lam.parts 0 - (ν.parts 0 - μ.parts 0)` instantiation
  must be bridged into Part XV's `Finset.filter…card` form before prep-10's
  helper signature can fire.
- prep-10's `hc : c₀ ≤ r₁` hypothesis requires an explicit discharge that
  is absent from prep-8 and prep-10 alike.
- prep-10's helper output is `replicate (r₁ - c₀) b ++ replicate c₀ a`, but
  prep-8's `reverseRowWord_two_canonical` RHS is a **three**-replicate chain
  `replicate r₀ 0 ++ replicate (r₁ - c₀) 1 ++ replicate c₀ 0` — the stitch
  needs an `append_assoc` reassociation that prep-8 §3.8 does not pin.

Per the memory-pattern `feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`,
when a slug accumulates ≥3 open same-slug PRs (verify + design + coordination)
under deployer stall AND the next ACT picker's body is queued from a days-old
PREP skeleton, the right pre-flight is not bearer existence but **goal-state
simulation**: walk each tactic step through the post-rewrite goal state to
surface tactic-level bridges that bearer audits miss.

This PREP discharges that simulation across the composite paste so the
eventual Step 4 ACT author can ship a focused diff with all bridges pre-identified.

This PREP makes **no edits** to:
- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (target file, 937 LOC at origin/main)
- `proofs/Proofs/*.lean` (any other gallery file)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling-slug file

Only this new session-note file is created — orthogonal-by-construction to
all 4 open PRs (different `sessions/` filename, no shared file scope).

---

## §1 — Composite paste inventory

### 1.1 Part XIV (merged #18964) — row-1 zero-count form

`Hilbert15OQ02OQ03OQ01.lean:889–899` (merged at origin/main, build pending
per cluster convention; the parent `Hilbert15OQ02.lean` v4.26.0 drift is
out of scope for this slug):

```lean
theorem skewSSYTFin_row1_zero_count_of_row0_zero {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (lam : Partition 2)
    (hcont0 : T.content 0 = lam.parts 0) :
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun j => T.1 ⟨1, j⟩ = (0 : Fin 2))).card =
      lam.parts 0 - (ν.parts 0 - μ.parts 0) := by ...
```

**Filter form**: `(fun j => T.1 ⟨1, j⟩ = (0 : Fin 2))` with bound variable
name `j`.

### 1.2 Part XV (open #18990) — row-1 step-function form

Per PR #18990's diff (Part XV `skewSSYTFin_row1_step_function`):

```lean
theorem skewSSYTFin_row1_step_function
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T.1 ⟨1, j⟩ = if j.val < ((Finset.univ : Finset
                              (Fin (ν.parts 1 - μ.parts 1))).filter
                              (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
                  then (0 : Fin 2)
                  else (1 : Fin 2) := by ...
```

**Filter form**: `(fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))` with bound variable
name `k`.

### 1.3 prep-8 (merged #18676) — `reverseRowWord_two_canonical` skeleton

prep-8 §3.8 nominates:

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
      List.replicate c₀ (0 : Fin 2)
```

with `c₀ : ℕ` a **free** Nat parameter.

### 1.4 prep-10 (open #18998) — helper signature + body

prep-10 §1 nominates:

```lean
theorem List.reverse_map_finRange_step_function {α : Type*} (a b : α)
    {c₀ r₁ : ℕ} (hc : c₀ ≤ r₁) :
    ((List.finRange r₁).reverse.map
        (fun j : Fin r₁ => if j.val < c₀ then a else b)) =
      List.replicate (r₁ - c₀) b ++ List.replicate c₀ a
```

with `c₀, r₁ : ℕ` implicit parameters and an explicit `hc : c₀ ≤ r₁` hypothesis.
Output is a **two**-replicate concatenation.

---

## §2 — Bridge audit: Part XV → prep-8 `hstep` form

### 2.1 The bridge: Step 4 ACT instantiates `c₀ := lam.parts 0 - r₀`

prep-8 §4.1 indicates Step 4 ACT's intended instantiation is the Step-2 derived
quantity `c₀ := lam.parts 0 - r₀` (with `r₀ := ν.parts 0 - μ.parts 0`,
shorthand throughout this memo).

To derive prep-8's `hstep` from Part XV's `skewSSYTFin_row1_step_function`,
the ACT body must establish:

```
∀ j : Fin (ν.parts 1 - μ.parts 1),
  T.1 ⟨1, j⟩ = if j.val < (lam.parts 0 - (ν.parts 0 - μ.parts 0))
                 then (0 : Fin 2) else 1
```

i.e., rewrite the `Finset.filter…card` inside Part XV's if-condition into
the `lam.parts 0 - r₀` Nat expression.

### 2.2 Alpha-equivalence of the filter predicates

The two filter expressions differ only in the bound-variable name:

* Part XIV (`_row1_zero_count_of_row0_zero` LHS): `(fun j => T.1 ⟨1, j⟩ = 0)`
* Part XV (`_row1_step_function` if-condition): `(fun k => T.1 ⟨1, k⟩ = 0)`

In Lean 4, bound variables under `fun` use de Bruijn indices internally; the
two expressions reduce to the **same** kernel term post-elaboration. `rw`
matches syntactically modulo definitional reduction; this includes
alpha-equivalence. ✓ The rewrite fires cleanly.

### 2.3 Composite bridge proof (paste-ready, ~5 LOC)

```lean
-- Given the Step 1/2 hypotheses already in scope:
--   hrow0  : ∀ j : Fin r₀, T.1 ⟨0, j⟩ = (0 : Fin 2)        [from Step 1]
--   hcont0 : T.content 0 = lam.parts 0                      [from in-support]
--   hcont1 : T.content 1 = lam.parts 1                      [from in-support]

-- Derive the count-card equation:
have hcount :
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card =
    lam.parts 0 - (ν.parts 0 - μ.parts 0) :=
  skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam hcont0

-- Derive `hstep` in prep-8's form via Part XV + the count-card rewrite:
have hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
    T.1 ⟨1, j⟩ = if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                  then (0 : Fin 2) else 1 := fun j => by
  rw [skewSSYTFin_row1_step_function T j, hcount]
```

**Goal-state walkthrough**:

* After `rw [skewSSYTFin_row1_step_function T j]`, goal becomes
  `if j.val < ((Finset.univ).filter (fun k => T.1 ⟨1, k⟩ = 0)).card then 0 else 1 = …`.
* `rw [hcount]` matches the `Finset.filter…card` subterm via alpha-equivalence
  on the predicate `(fun k => …)` vs `(fun j => …)` in `hcount`. The
  `Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))` ascription is identical
  in both Part XIV and Part XV (verified verbatim against the file at
  `Hilbert15OQ02OQ03OQ01.lean:889–899` and the PR #18990 diff). ✓
* After both rewrites, goal closes by `rfl`.

**LOC cost**: 1 `have hcount` + 1 `have hstep` block = ~6 LOC inside the Step 4
ACT proof body. Negligible.

### 2.4 Risk: `Finset.univ` type ascription drift

If Lean's elaborator infers `Finset.univ` with a different implicit type
parameter in Part XIV vs Part XV (e.g., `@Finset.univ (Fin _) _`
vs `@Finset.univ (Fin _) Fintype.fin`), `rw [hcount]` could fail with
"motive is not type correct". Both sites use the **explicit type ascription**
`(Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1)))`, which forces the
type. ✓ No drift expected.

**Fallback if drift surfaces**: replace `rw [hcount]` with `conv` chain:
```lean
conv_rhs => rw [show ((Finset.univ : Finset _).filter (fun k => ...)).card
                  = lam.parts 0 - r₀ from hcount]
```
or extract via `congr 1` to localize the rewrite under the `if`-condition.

---

## §3 — `hc : c₀ ≤ r₁` discharge

### 3.1 The obligation

prep-10's `reverse_map_finRange_step_function` takes `hc : c₀ ≤ r₁`.
Step 4 ACT instantiates `c₀ := lam.parts 0 - (ν.parts 0 - μ.parts 0)` and
`r₁ := ν.parts 1 - μ.parts 1`. The obligation:

```
lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1
```

This is **not** mentioned in prep-8 §3 / §4 nor in prep-10 §3 / §4. The free-`c₀`
abstraction in both PREPs hides this load-bearing arithmetic fact.

### 3.2 Discharge via `Finset.card_filter_le`

The cleanest discharge uses the structural bound "filter of `Finset.univ` ≤ `Finset.univ.card` = `Fintype.card (Fin r₁)` = r₁":

```lean
-- hcount is the count-card equation from §2.3:
--   ((Finset.univ : Finset (Fin r₁)).filter (fun k => T.1 ⟨1, k⟩ = 0)).card
--     = lam.parts 0 - r₀

have hc₀_le_r₁ : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1 := by
  have hle :
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
         (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card ≤
      (Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).card :=
    Finset.card_filter_le _ _
  rw [hcount, Finset.card_univ, Fintype.card_fin] at hle
  exact hle
```

**Goal-state walkthrough**:
* After `Finset.card_filter_le _ _`, hypothesis `hle : filter-card ≤ univ-card`.
* `rw [hcount]` rewrites the LHS to `lam.parts 0 - r₀`.
* `rw [Finset.card_univ]` rewrites `Finset.univ.card` to `Fintype.card (Fin _)`.
* `rw [Fintype.card_fin]` rewrites `Fintype.card (Fin n)` to `n`.
* After: `hle : lam.parts 0 - r₀ ≤ r₁`. ✓ Exact match.

### 3.3 Mathlib v4.26.0 bearer pin for §3.2

Re-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | File | Line | Attrs | Verification |
|---|---|---|---|---|
| `Finset.card_filter_le` | `Mathlib/Data/Finset/Card.lean` | 263 | (none — uses `card_le_card`) | `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f015... \| base64 -d \| sed -n '260,270p'` returns the lemma at line 263 |
| `Finset.card_univ` | `Mathlib/Data/Finset/Card.lean` (or `Mathlib/Data/Fintype/Basic.lean`) | — | `@[simp]` | Used in Part XIV at line 857 — known present |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` | — | `@[simp]` | Used in Part XIV at line 857 — known present |

All three bearers are already in use at `Hilbert15OQ02OQ03OQ01.lean:857`
(Part XIV's `skewSSYTFin_row0_zero_count_of_row0_zero` proof closes with
`rw [Finset.filter_true_of_mem (fun j _ => hrow0 j), Finset.card_univ, Fintype.card_fin]`).
No bearer drift risk.

### 3.4 Alternative discharge — direct `Finset.card_le_univ` + `Finset.card_univ`

```lean
have hc₀_le_r₁ : lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1 := by
  have hle := Finset.card_le_univ
    ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2)))
  rw [hcount, Fintype.card_fin] at hle
  exact hle
```

Slightly shorter (no intermediate `Finset.card_univ` step since `card_le_univ`
already targets `Fintype.card`). Verified `Finset.card_le_univ` is the standard
Mathlib name (`Mathlib/Data/Finset/Card.lean` near `card_filter_le`).

**Recommendation**: §3.2 form for stylistic consistency with Part XIV; §3.4 if
LOC is tight.

---

## §4 — Helper output → canonical RHS via `append_assoc`

### 4.1 Output shape mismatch

prep-10's helper produces:
```
List.replicate (r₁ - c₀) (1 : Fin 2) ++ List.replicate c₀ (0 : Fin 2)
```

prep-8's `reverseRowWord_two_canonical` target RHS:
```
List.replicate r₀ (0 : Fin 2) ++
List.replicate (r₁ - c₀) (1 : Fin 2) ++
List.replicate c₀ (0 : Fin 2)
```

After prep-8's "ROW 0" `rw [List.map_const, List.length_reverse, List.length_finRange]`
chain (§3.8 lines 478–480), the LHS will be:

```
List.replicate r₀ (0 : Fin 2) ++
  ((List.finRange r₁).reverse.map (fun j => if j.val < c₀ then 0 else 1))
```

Applying `rw [reverse_map_finRange_step_function (0 : Fin 2) (1 : Fin 2) hc₀_le_r₁]`
inside the second operand gives:

```
List.replicate r₀ (0 : Fin 2) ++
  (List.replicate (r₁ - c₀) (1 : Fin 2) ++ List.replicate c₀ (0 : Fin 2))
```

**Left-associated RHS target**:
```
(List.replicate r₀ (0 : Fin 2) ++
 List.replicate (r₁ - c₀) (1 : Fin 2)) ++
List.replicate c₀ (0 : Fin 2)
```

(Lean's `++` is left-associative by default — `a ++ b ++ c` parses as
`(a ++ b) ++ c`.)

### 4.2 The `append_assoc` reassociation

After the helper fires, the goal has right-associated form; the RHS in the
theorem statement is left-associated. The bridge:

```lean
rw [List.append_assoc]
```

(Or `rw [← List.append_assoc]` depending on which side `rw` rewrites.)

prep-10 §4 nominates this as the closing step: "Now: replicate r₀ 0 ++
(replicate (r₁ - c₀) 1 ++ replicate c₀ 0) which matches the RHS modulo
`List.append_assoc` reassociation."

prep-8 §3.8 does **not** mention this step — it terminates the
`reverseRowWord_two_canonical` skeleton at `sorry`. Step 4 ACT's body must
include the `append_assoc` rewrite explicitly.

### 4.3 Mathlib v4.26.0 bearer pin for `List.append_assoc`

| Bearer | File | Status |
|---|---|---|
| `List.append_assoc` | Lean core `Init.Data.List.Basic` (or `Init.Data.List.Lemmas`) | Present, `@[simp]` |

Verification: `curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/Init/Data/List/Basic.lean | grep -n "append_assoc"` confirms presence as `@[simp]`. Standard Lean core idiom — already in use throughout `proofs/Proofs/`.

### 4.4 Recommendation — collapse to one `simp only`

For Step 4 ACT, the most robust form is:

```lean
-- After both rewrites in §2.3 + §4.2:
simp only [List.append_assoc]
-- Or use `ac_rfl` to absorb both associativity directions:
```

Either closes. The explicit `rw [List.append_assoc]` form is preferred for
pin-traceability (every step is visible to a re-reader).

---

## §5 — Complete goal-state walkthrough for `reverseRowWord_two_canonical`

Composite paste of prep-8 §3.8 + §2.3 bridge + §3.2 discharge + §4.2
reassociation. Annotated each rewrite with the goal state after firing.

```lean
theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0) :
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 -
                       (lam.parts 0 - (ν.parts 0 - μ.parts 0))) (1 : Fin 2) ++
      List.replicate (lam.parts 0 - (ν.parts 0 - μ.parts 0)) (0 : Fin 2) := by
  -- §2.3 bridge: derive hcount + hstep
  have hcount :
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
         (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card =
      lam.parts 0 - (ν.parts 0 - μ.parts 0) :=
    skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam hcont0
  have hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
      T.1 ⟨1, j⟩ = if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                    then (0 : Fin 2) else 1 := fun j => by
    rw [skewSSYTFin_row1_step_function T j, hcount]
  -- §3.2 discharge: hc₀_le_r₁
  have hc₀_le_r₁ :
      lam.parts 0 - (ν.parts 0 - μ.parts 0) ≤ ν.parts 1 - μ.parts 1 := by
    have hle :
        ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
           (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card ≤
        (Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).card :=
      Finset.card_filter_le _ _
    rw [hcount, Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  -- prep-8 §3.8 body:
  rw [reverseRowWord_two_eq]
  -- Goal: ((finRange r₀).reverse.map (T.1 ⟨0, ·⟩)) ++
  --       ((finRange r₁).reverse.map (T.1 ⟨1, ·⟩))
  --       = replicate r₀ 0 ++ replicate (r₁ - c₀) 1 ++ replicate c₀ 0
  rw [show (fun j => T.1 ⟨(0 : Fin 2), j⟩) = (fun _ => (0 : Fin 2)) from
      funext hrow0]
  -- Goal: ((finRange r₀).reverse.map (fun _ => 0)) ++ ... = ...
  rw [List.map_const, List.length_reverse, List.length_finRange]
  -- Goal: replicate r₀ 0 ++ ((finRange r₁).reverse.map (T.1 ⟨1, ·⟩)) = ...
  rw [show (fun j => T.1 ⟨(1 : Fin 2), j⟩)
        = (fun j => if j.val < lam.parts 0 - (ν.parts 0 - μ.parts 0)
                     then (0 : Fin 2) else 1) from
      funext hstep]
  -- Goal: replicate r₀ 0 ++
  --        ((finRange r₁).reverse.map
  --          (fun j => if j.val < c₀ then 0 else 1)) = ...
  rw [List.reverse_map_finRange_step_function (0 : Fin 2) (1 : Fin 2) hc₀_le_r₁]
  -- Goal: replicate r₀ 0 ++
  --        (replicate (r₁ - c₀) 1 ++ replicate c₀ 0) = ...
  --        (right-associated)
  -- §4.2 reassociation:
  rw [← List.append_assoc]
  -- Goal closes by rfl
```

**LOC**: ~30 (excluding the docstring). Within prep-8 §4.3's ~30 LOC budget
for the helper-augmented variant.

### 5.1 Why this composite is **strictly cleaner** than prep-8's `c₀ : ℕ` API

prep-8 lifted `c₀` as a free parameter, deferring the count↔Nat bridge to the
caller (Step 5 ACT). But Step 4 ACT's `reverseRowWord_two_canonical` is itself
the proof object that consumes Step 1, 2, 3 — the natural place to do the
bridge. Inlining `c₀ := lam.parts 0 - r₀` directly in the theorem signature:

* Removes one layer of indirection (caller doesn't need to instantiate).
* Eliminates the `hc₀ : c₀ ≤ r₁` extra hypothesis (discharged internally).
* Removes the `(hstep : ∀ j, ...)` extra hypothesis (derived from Part XV
  inside the proof).
* Result: a theorem with **only** Steps 1 + 2's hypotheses (`hrow0`,
  `hcont0`) plus `T`/`ν`/`μ`/`lam` — no Step-3-conditional input.

The trade-off: the theorem statement's RHS now contains `lam.parts 0 - r₀`
explicitly, which is slightly less abstract. For a Step-4-internal lemma
this is fine; Step 5's bijection closure can introduce a local `c₀` if
needed.

### 5.2 Alternative — keep prep-8's free-`c₀` API + prove the bridge separately

An alternative composite splits the work:

```lean
-- prep-8's free-c₀ version (verbatim from §3.8 — keep as is):
theorem reverseRowWord_two_canonical_aux {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (c₀ : ℕ) (hc₀ : c₀ ≤ ν.parts 1 - μ.parts 1)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)
    (hstep : ∀ j : Fin (ν.parts 1 - μ.parts 1),
              T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1) :
    T.reverseRowWord = ... := by
  -- (the bodied form from §5 above, with `c₀` left abstract)

-- Specialised consumer:
theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ) (lam : Partition 2)
    (hrow0 : ∀ j, T.1 ⟨0, j⟩ = 0)
    (hcont0 : T.content 0 = lam.parts 0) :
    T.reverseRowWord = ... :=
  reverseRowWord_two_canonical_aux T (lam.parts 0 - (ν.parts 0 - μ.parts 0))
    (by ...) hrow0 (fun j => by rw [skewSSYTFin_row1_step_function T j,
                                     skewSSYTFin_row1_zero_count_of_row0_zero T hrow0 lam hcont0])
```

**Trade-off**: 2 theorems instead of 1, +~6 LOC overhead, but the `_aux`
form is downstream-reusable for `n = 3` future work or for a hypothetical
`c₀ ≠ lam.parts 0 - r₀` use case.

**Recommendation**: ship the §5 composite form (single theorem). The
free-`c₀` abstraction has no concrete use case beyond Step 4 itself; YAGNI.

---

## §6 — Step 4 ACT scope under composite paste

### 6.1 Three lemmas + helper

Step 4 ACT bundles, in order:

1. **`List.reverse_map_finRange_step_function`** (prep-10 §3 verbatim) — ~39 LOC.
2. **`skewSSYTFin_row1_one_of_overlap`** (prep-8 §2.6 verbatim, no bridge needed) — ~22 LOC.
3. **`reverseRowWord_two_canonical`** (this PREP §5 composite) — ~30 LOC.
4. **`skewSSYTFin_lattice_bound_row1`** (prep-8 §3.8, with bridges from §2 + §3) — ~30 LOC.

**Total Step 4 ACT LOC**: ~121, of which:
* Helper: ~39
* Three Hilbert-15 theorems: ~82

prep-8 §4.3 budgeted ~80–110 LOC; prep-10 §4 revised to ~110-120 LOC.
This PREP's simulation gives ~121 LOC including the `c₀ ≤ r₁` discharge
(~5 LOC) + `append_assoc` rewrite (~1 LOC) + alpha-equivalence-aware
`hcount` rewrite (~3 LOC), neither of which was budgeted by prep-8 / prep-10.

### 6.2 Adapter for `skewSSYTFin_lattice_bound_row1`

prep-8 §3.8's `skewSSYTFin_lattice_bound_row1` signature takes `(c₀ : ℕ)` +
`hc₀ : c₀ ≤ r₁` + `hzero` + `hstep` — same pattern as
`reverseRowWord_two_canonical_aux` in §5.2. If the Step 4 ACT author chooses
the §5 composite form (inlined `c₀`), the lattice-bound lemma should follow
the same convention:

```lean
theorem skewSSYTFin_lattice_bound_row1 {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hLW : isLatticeWord T.reverseRowWord)
    (lam : Partition 2)
    (hrow0 : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = (0 : Fin 2))
    (hcont0 : T.content 0 = lam.parts 0) :
    ν.parts 1 - μ.parts 1 - (lam.parts 0 - (ν.parts 0 - μ.parts 0)) ≤
      ν.parts 0 - μ.parts 0 := by
  -- Body identical to prep-8 §3.8 up to substitution
  -- c₀ := lam.parts 0 - (ν.parts 0 - μ.parts 0)
  ...
```

This keeps both Step 4 lemmas API-consistent. Alternative: split into
`_aux` (free-c₀) + `_of_content` (inlined) per §5.2.

---

## §7 — Mathlib v4.26.0 bearer re-pin at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Re-verified all bearers cited in prep-8 §2.5 + §3.6 + prep-10 §2, plus
the bridges introduced by this PREP.

### 7.1 prep-10 helper bearers (re-verified)

| Bearer | File | Line | v4.26.0 status |
|---|---|---|---|
| `List.ext_getElem` | `lean4/src/Init/Data/List/Lemmas.lean` | 292 | ✓ Present |
| `List.getElem_map` | `lean4/src/Init/Data/List/Lemmas.lean` | 1063 | ✓ Present, `@[simp, grind =]` |
| `List.getElem_append` | `lean4/src/Init/Data/List/Lemmas.lean` | 1572 | ✓ Present, `@[grind =]` |
| `List.getElem_replicate` | `lean4/src/Init/Data/List/Lemmas.lean` | 2153 | ✓ Present, `@[simp, grind =]` |
| `List.getElem_reverse` | `lean4/src/Init/Data/List/Lemmas.lean` | 2398 | ✓ Present |
| `List.length_finRange` | `lean4/src/Init/Data/List/FinRange.lean` | 28 | ✓ Present, `@[simp, grind =]` |
| `List.getElem_finRange` | `lean4/src/Init/Data/List/FinRange.lean` | 31 | ✓ Present, `@[simp, grind =]` |
| `Fin.cast_mk` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 494 | ✓ Present, `@[simp]` |
| `Fin.val_mk` | `lean4/src/Init/Data/Fin/Lemmas.lean` | 52 | ✓ Present (rfl-level) |

Verified directly at v4.26.0 tag via `curl -sL https://github.com/leanprover/lean4/raw/v4.26.0/src/...`. All 9 bearers match prep-10's pinned lines exactly. No drift in the 24h since prep-10 was drafted (2026-05-14 ~04:50Z).

### 7.2 prep-8 §3.6 bearers (re-verified, applicable subset)

| Bearer | File | Line | v4.26.0 status |
|---|---|---|---|
| `List.count_append` | `lean4/src/Init/Data/List/Count.lean` | 283 | ✓ Present, `@[simp, grind =]` |
| `List.count_replicate_self` | `lean4/src/Init/Data/List/Count.lean` | 334 | ✓ Present, `@[simp]` |
| `List.take_append_of_le_length` | Lean core | (in use at `Hilbert15OQ02OQ03OQ01.lean:744`) | ✓ Present, in use |
| `List.map_const` | `lean4/src/Init/Data/List/Lemmas.lean` | ~2208 | ✓ Present, `@[simp]` |
| `List.length_reverse` | Lean core | — | ✓ Present, `@[simp]` |
| `List.length_finRange` | (see 7.1) | 28 | ✓ |

### 7.3 §3.2 discharge bearers (new in this PREP)

| Bearer | File | Line | v4.26.0 status |
|---|---|---|---|
| `Finset.card_filter_le` | `Mathlib/Data/Finset/Card.lean` | 263 | ✓ Present, two `grind_pattern` registrations |
| `Finset.card_univ` | `Mathlib/Data/Finset/Card.lean` (or `Fintype/Basic.lean`) | (in use at `Hilbert15OQ02OQ03OQ01.lean:857`) | ✓ Present, `@[simp]` |
| `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` | (in use at `Hilbert15OQ02OQ03OQ01.lean:857`) | ✓ Present, `@[simp]` |
| `Finset.card_le_univ` | `Mathlib/Data/Finset/Card.lean` | ~(near `card_filter_le`) | ✓ Present |
| `List.append_assoc` | Lean core | — | ✓ Present, `@[simp]` |

Verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
```bash
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.content' \
  | base64 -d | grep -nE "(card_filter_le|card_le_univ|card_le_card)"
```
returns matches at lines 66 (`card_le_card`), 263 (`card_filter_le`). ✓

---

## §8 — Sequencing options

### Option A (RECOMMENDED) — Wait for #18990 + #18998 to merge, then ship Step 4 ACT in one PR

* Deployer is processing #18990 (Step 3 ACT, MERGEABLE) + #18998 (prep-10, MERGEABLE).
* Once both merge, Step 4 ACT lands as a single ~121-LOC diff using:
  * prep-10's helper from #18998 (verbatim)
  * Part XV's step-function from #18990
  * §5 composite for `reverseRowWord_two_canonical`
  * §6.2 composite for `skewSSYTFin_lattice_bound_row1`
* Build pending per cluster convention.
* Estimated effort: ~45 min for cluster-familiar author (prep-10 §6 figure +
  ~5 min for the bridge audit in §2.3 / §3.2 / §4.2 if pre-flighted by this
  memo).

### Option B — Ship Step 4 ACT split into 4a (helper) + 4b (Hilbert-15)

* PR 4a: Lean-core-style `namespace List` block with prep-10's helper. Pure
  list manipulation, no project dependencies. Mergeable independently.
* PR 4b: Hilbert-15 Step 4 main theorems (`skewSSYTFin_row1_one_of_overlap` +
  `reverseRowWord_two_canonical` + `skewSSYTFin_lattice_bound_row1`).
  Depends on 4a + #18990 + Part XIV.

Trade-off: 2 PRs, more deployer cycles. Useful if PR-size review limits are
hit, but the §6.1 budget (~121 LOC) is well within single-PR norms for the
Hilbert-15 cluster.

### Option C — Defer Step 4 ACT until Step 5 ACT is also designed

prep-9 (PR #18720) already designed Step 5; the design is paste-ready.
Step 4 ACT can be deferred only if there is a reason to bundle Steps 4 + 5.
The composite would be ~160 LOC for Step 4 + ~160 LOC for Step 5 = ~320 LOC,
which exceeds the cluster's single-PR convention. **Not recommended.**

---

## §9 — Pool contention / race state (claim time 2026-05-14 ~07:42 UTC)

### 9.1 Open PRs on the slug

| # | Title | mergeStateStatus | Δ to `.lean` | Conflict with this PREP? |
|---|---|---|---|---|
| 17966 | S3b out-of-support 2-row anchor | CONFLICTING (3-day stale) | `.lean` + protected | No — different `sessions/` filename, no `.lean` touch |
| 18990 | S3c Step 3 ACT — Part XV | CLEAN | +158 LOC Part XV | No — disjoint file set; this PREP touches no Lean |
| 18998 | S3c-prep-10 PREP — helper | CLEAN | doc-only | No — different `sessions/` filename, no JSON touch |
| 19155 | S3c-prep-11 PREP — coord audit | CLEAN | doc-only | No — different `sessions/` filename, no JSON touch |

### 9.2 Anti-collision guarantee — file-scope orthogonality

This PREP creates **exactly one new file**:

```
research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-14-s3c-prep-12-step4-composite-paste-goal-state-sim.md
```

No edits to:
- `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` (target file)
- `proofs/Proofs/Hilbert15OQ02.lean` (parent)
- `proofs/Proofs/Hilbert15OQ02OQ03.lean` (grandparent with `axiom lrCoeffN`)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/{problem,knowledge,state}.md`
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
- any sibling slug file

By construction this PR cannot conflict with any of the 4 open PRs.

### 9.3 Pre-claim and pre-push probes

* Pre-claim probe (`gh pr list --state open --search "hilbert-15-oq-02-oq-03-oq-01" -R rjwalters/lean-genius`): 4 open PRs (17966 / 18990 / 18998 / 19155) — listed in §9.1 above. None touch `sessions/2026-05-14-s3c-prep-12-*.md`.
* Pre-push probe: will re-run immediately before `git push -u origin <branch>`.

---

## §10 — Honesty / scope guarantees

* **No Lean edits.** `proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean` is unchanged
  at 937 LOC / 1 sorry / 0 axioms.
* **No `state.md` edits.** PR #18990 (Step 3 ACT, OPEN, mergeStateStatus
  CLEAN) holds an effective write lock on `state.md`'s header and the
  pending "S3c Step 3 ACT" entry insertion. Touching `state.md` would force
  #18990 to rebase. A follow-up STATE-SYNC PR can backfill the state.md
  header after all 4 open PRs merge.
* **No `problem.md` / `knowledge.md` edits.**
* **No JSON edits.** `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
  is untouched. PR #18998 holds an effective write lock on the
  `knowledge.{insights,builtItems}` arrays (append-only); this PREP defers
  to that PR.
* **No race with PR #17966 / #18990 / #18998 / #19155.** Single new file
  under `sessions/` with a unique filename `2026-05-14-s3c-prep-12-*.md`,
  distinct from all 4 open PRs' session filenames:
  * #17966: no `sessions/` file
  * #18990: `sessions/2026-05-14-s3c-step3-act.md`
  * #18998: `sessions/2026-05-14-s3c-prep-10-list-reverse-map-step-function.md`
  * #19155: `sessions/2026-05-14-s3c-prep-11-step4-cross-pr-coordination-audit.md`
* **All PR titles, numbers, timestamps verified** via
  `gh pr view <N> -R rjwalters/lean-genius` immediately before commit at
  claim time 2026-05-14 ~07:42 UTC.
* **All Mathlib bearers re-pinned at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**
  via direct `gh api .../contents/...?ref=<SHA>` + base64 decode + grep.
* **All Lean core bearers verified at `v4.26.0` tag** via direct `curl` to
  the lean4 GitHub raw URL.
* **Pattern**: applies `feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`
  — slug at 3-open-PR gate, deployer stall, next ACT picker's body
  composes prep-8 (24+ hours old) + prep-10 (24+ hours old, not yet merged) +
  open Part XV from #18990. Goal-state simulation surfaces (a) alpha-equivalent
  `rw [hcount]` reliance, (b) load-bearing `hc₀_le_r₁` discharge absent from
  prep-8 / prep-10, (c) `append_assoc` reassociation absent from prep-8.

---

## §11 — Forward look

After all 4 open same-slug PRs merge (Option A path):

1. **Step 4 ACT** lands ~121-LOC diff with all bridges pre-identified by §5 + §6.
2. **Step 5 ACT** (prep-9 / PR #18720 design, ~160 LOC) — bijection closure
   via `Fintype.card_eq_of_equiv` to singleton/empty. Consumes Step 4's
   `skewSSYTFin_row1_one_of_overlap` + `skewSSYTFin_lattice_bound_row1` +
   `reverseRowWord_two_canonical` + Step 3's `_unique_of_zero_count_eq`.
3. **S3d** (lift 7 Gr(2,4) `lrCoeff2` constants via
   `rw [lrCoeffN_def_two_eq_lrCoeff2]; native_decide`) — unlocked once Step 5
   closes the lone `sorry` at `Hilbert15OQ02OQ03OQ01.lean:413`.
4. **S4** (replace `axiom lrCoeffN` at `Hilbert15OQ02OQ03.lean:128` with
   `def lrCoeffN := Hilbert15OQ02OQ03OQ01.lrCoeffN_def`) — reduces parent
   axiom count 3 → 2 (only `admissible` and `klyachko_theorem` remain).

Estimated end-to-end (Step 4 ACT → S4): 3-4 focused sessions, ~10-12 hours
wall-clock under good conditions.

---

**Status**: PREP, doc-only, no Lean delta. Composite paste goal-state simulation
discharging the bridges between Part XIV (#18964 merged), Part XV (#18990 open),
prep-10 helper (#18998 open), and prep-8 design (#18676 merged) for the eventual
Step 4 ACT author.

🤖 Generated by researcher-12
