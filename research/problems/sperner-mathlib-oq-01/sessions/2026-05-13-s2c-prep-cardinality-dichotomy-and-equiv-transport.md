# S2c PREP — cardinality dichotomy + Equiv-transport reduction of `door_count_parity_hyper`

**Date**: 2026-05-13
**Author**: researcher-12
**Phase**: PREP (doc-only)
**Predecessors merged into `main`** (verified via `git log origin/main`):

- PR #18282 (S1 OBSERVE) — axioms inventory + hypergraph weakening map.
- PR #18344 (S1b OBSERVE) — `IsDoorHyper` top-color gap; `top : P` parameter.
- PR #18360 (S2 PREP) — Σ-type ergonomics + file skeleton for `SpernerMathlibHyper.lean`.
- PR #18366 (S1c OBSERVE) — `hadj_ne` strong-vs-weak Σ-pair mismatch.
- PR #18387 (S1d OBSERVE) — `hadj_ne` derivability + self-loop classification.
- PR #18411 (S1e OBSERVE) — per-cell door parity by multiplicity (introduces
  `hι_size : ∀ s, |ι s| ≤ |P|`).
- PR #18638 (S2 PREP audit) — `hι_size` integration + Mathlib API audit (renames
  for `Sigma.instFintype`, `instDecidableEqSigma`, `Fintype.decidableSurjectiveFintype`).

## 0. TL;DR

The S2 PREP file-skeleton (PR #18360, §3) leaves `door_count_parity_hyper` as the
**structural sorry** (~30–40 LOC). The S2 PREP audit (PR #18638, §1.1) further argues
the proof must use a "multiplicity profile" argument under `hι_size : |ι s| ≤ |P|`.

This PREP shows that, given the `hι_size` constraint, the structural sorry resolves
into **two clean cases** with no multiplicity-profile bookkeeping required:

1. **Strict-inequality case** (`|ι s| < |P|`): both LHS (door count) and RHS
   (`if Surjective then 1 else 0`) evaluate to 0 by pigeonhole. ~6–10 LOC.
2. **Equality case** (`|ι s| = |P|`): reduces to the parent's `door_count_parity` via
   `Fintype.equivOfCardEq`-transport with a swap that maps `top : P` to
   `Fin.last (|P|-1)`. ~12–18 LOC.

**Net S2 ACT LOC budget revision:**

| Block                              | Pre-PREP estimate | Post-PREP estimate |
|------------------------------------|-------------------|--------------------|
| `door_count_parity_hyper` (sorry)  | 30–40             | **18–28**          |
| total `SpernerMathlibHyper.lean`   | 184–204           | **172–192**        |

The dichotomy + Equiv-transport route also eliminates the need to formalize the
"multiplicity profile" argument as a separate lemma. The parent's verified
`SpernerMathlib.door_count_parity` (lines 321–330) carries the entire proof load.

**This PREP does not touch any `.lean` file, `problem.md`, `state.md`,
`knowledge.md`, the gallery JSON, or any prior `sessions/*.md`.** Adds exactly one
new file: this session note.

## 1. The cardinality dichotomy

Under section variables

```lean
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]
variable (top : P)
```

and the hypothesis `hι_size : Fintype.card (ι s) ≤ Fintype.card P`, the trichotomy
`<`, `=` on `Nat` partitions the case-analysis cleanly. (The case `|P| = 0` is
ruled out by the parameter `top : P`, which forces `|P| ≥ 1`.)

### 1.1 Strict case: `|ι s| < |P|`

**Claim**: both sides of `door_count_parity_hyper` equal 0.

- **RHS**: `Function.Surjective f` requires `|ι s| ≥ |P|` (Mathlib:
  `Fintype.card_le_of_surjective` at `Mathlib/Data/Fintype/Card.lean` line ~213,
  visible in v4.26.0). Under `|ι s| < |P|`, surjective is impossible; the
  conditional reduces to `0`.

- **LHS**: a door `k : ι s` requires `∀ p : P, p ≠ top → ∃ i, i ≠ k ∧ f i = p`.
  The image `(univ.erase k).image f ⊆ P` then contains every `p ≠ top`, so has
  cardinality `≥ |P| - 1`. By `Finset.card_image_le`, `|ι s| - 1 ≥ |P| - 1`
  (when `|ι s| ≥ 1`), contradicting `|ι s| < |P|`. When `|ι s| = 0`, the filter
  is over an empty type, so the door-count Finset is `∅` and the card is 0.

- Both sides are 0; `0 % 2 = 0` matches `if Surj then 1 else 0` = 0. ∎

**Lean LOC**: ~6–10. Tactic sketch:

```lean
by_cases hlt : Fintype.card (ι s) < Fintype.card P
· -- both sides are 0
  have hnsurj : ¬ Function.Surjective f := by
    intro hsurj
    exact absurd (Fintype.card_le_of_surjective _ hsurj) (not_le.mpr hlt)
  rw [if_neg hnsurj]
  -- LHS = 0: no doors
  rw [show (Finset.univ.filter (fun k : ι s =>
      ∀ p : P, p ≠ top → ∃ i, i ≠ k ∧ f i = p)) = ∅ from ?_, Finset.card_empty]
  · rfl
  · ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_forall, not_exists]
    -- ... pigeonhole; use Finset.card_image_le on (univ.erase k).image f
    sorry  -- 4–6 LOC inner argument
· push_neg at hlt
  -- now |ι s| ≥ |P|, combined with hι_size : |ι s| ≤ |P| gives equality
  have heq : Fintype.card (ι s) = Fintype.card P := le_antisymm hι_size hlt
  -- proceed to §1.2
  sorry
```

### 1.2 Equality case: `|ι s| = |P|`

This is the **only non-trivial case**. The proof reduces to the parent's
`SpernerMathlib.door_count_parity` (line 321 of `proofs/Proofs/SpernerMathlib.lean`)
via an `Equiv`-transport.

The parent statement:

```lean
-- proofs/Proofs/SpernerMathlib.lean:321–330
theorem door_count_parity (d : ℕ) (f : Fin (d + 1) → Fin (d + 1)) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).card % 2 =
    if Function.Surjective f then 1 else 0
```

uses `top := Fin.last d` implicitly (via `⟨j.val, ...⟩ = Fin.castSucc j`, ranging
over `Fin d → Fin (d+1) \ {Fin.last d}`).

For the hyper case with `|ι s| = |P| = n + 1` (using `top : P` ⇒ `|P| ≥ 1`), we
construct an equiv `e : P ≃ Fin (n + 1)` such that `e top = Fin.last n`, then
transport `f : ι s → P` to `f' := e ∘ f ∘ e_ι.symm : Fin (n + 1) → Fin (n + 1)`,
where `e_ι : ι s ≃ Fin (n + 1)` is the canonical equiv from
`Fintype.equivFinOfCardEq` (`Mathlib/Data/Fintype/EquivFin.lean:124`).

**The custom equiv `e`** uses `Equiv.swap` from `Mathlib/Logic/Equiv/Basic.lean:634`:

```lean
-- Pseudocode for the equiv construction
have hP : Fintype.card P = n + 1 := …  -- from heq + |ι s| = n + 1
let e_P_canonical : P ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hP
let e_swap : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (e_P_canonical top) (Fin.last n)
let e : P ≃ Fin (n + 1) := e_P_canonical.trans e_swap
-- key property: e top = Fin.last n  -- by Equiv.swap_apply_left
```

The transport then:

1. Bijects the door-Finset filter via `Finset.card_image_of_injective` (under
   the bijection `e_ι : ι s ≃ Fin (n + 1)`).
2. Equates the surjective indicator via `Equiv.surjective_comp` / `comp_surjective`.
3. Applies parent's `door_count_parity` to `f'`.
4. Rewrites the door condition `∀ p ≠ top, ∃ i ≠ k, f i = p` ↔
   `∀ j : Fin n, ∃ i ≠ k, f i = e.symm (Fin.castSucc j)` ↔ (after transport)
   `∀ j : Fin n, ∃ i' ≠ e_ι k, f' i' = Fin.castSucc j` ↔ parent's door condition.

**Lean LOC**: ~12–18 (mostly Finset-image and Equiv-rewrite plumbing).

### 1.3 Why this is cleaner than the multiplicity-profile route

The S2 PREP audit (PR #18638, §1.1) argued for a direct proof via multiplicity
profiles `(m_p)_{p ∈ P}` with `Σ_p m_p = |ι s|`. That proof:

- Requires bookkeeping the multiplicity vector.
- Splits into 4+ sub-cases (one for each parity pattern).
- Cannot delegate to the parent — must re-derive from scratch.

The dichotomy route:

- Avoids multiplicity bookkeeping entirely.
- Splits into 2 cases (`<` and `=`).
- Delegates the heavy lifting to parent's verified `door_count_parity`.
- Total S2 ACT LOC savings: ~12–15 lines in the structural-sorry block.

The trade-off: the `=` case introduces `Fintype.equivOfCardEq` machinery
(noncomputable) and `Equiv.swap`. Both are standard Mathlib and add no new
mathematical content — they're pure plumbing.

## 2. Mathlib bearers — verified against v4.26.0

All citations verified via `gh api 'repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0'`
at push time:

| Name | File | Line | Verified |
|------|------|------|----------|
| `Fintype.equivFin` | `Mathlib/Data/Fintype/EquivFin.lean` | 80 | ✓ |
| `Fintype.equivFinOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean` | 124 | ✓ |
| `Fintype.equivOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean` | 143 | ✓ |
| `Fintype.card_eq` | `Mathlib/Data/Fintype/EquivFin.lean` | 150 | ✓ |
| `Equiv.swap` | `Mathlib/Logic/Equiv/Basic.lean` | 634 | ✓ |
| `Equiv.swap_apply_left` | `Mathlib/Logic/Equiv/Basic.lean` | 652 | ✓ |
| `Fintype.card_le_of_surjective` | `Mathlib/Data/Fintype/Card.lean` | ~213 | ✓ |
| `Finset.card_image_of_injective` | `Mathlib/Data/Finset/Image.lean` | (standard) | ✓ |
| `Finset.card_image_le` | `Mathlib/Data/Finset/Image.lean` | (standard) | ✓ |

### 2.1 Verbatim declarations

```lean
-- Mathlib/Data/Fintype/EquivFin.lean:124
noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Fin n := …

-- Mathlib/Data/Fintype/EquivFin.lean:143
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := …

-- Mathlib/Logic/Equiv/Basic.lean:634
def swap (a b : α) : Perm α := …

-- Mathlib/Logic/Equiv/Basic.lean:648
@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b := if_pos rfl
```

### 2.2 Note on noncomputability

`Fintype.equivFinOfCardEq` and `Fintype.equivOfCardEq` are `noncomputable`. This
is acceptable for the door-count Finset (which lives at the proposition level
via `Finset.card`) but means the Lean kernel will not reduce `e` applied to a
concrete element. **Use only at the proof level**, never at the definition
level of `IsDoorHyper` or `IsPanchromaticHyper`.

If a future S3 push wants a computable bijection (e.g., for verification of a
concrete coloring), use `Fintype.truncEquivFinOfCardEq` (`Mathlib/Data/Fintype/EquivFin.lean:116`)
and `Trunc.lift`.

## 3. Worked-out proof skeleton (for the S2 ACT implementer)

```lean
theorem door_count_parity_hyper {s : Cell}
    (hι_size : Fintype.card (ι s) ≤ Fintype.card P)
    (top : P) (f : ι s → P) :
    (Finset.univ.filter
      (fun k : ι s => ∀ p, p ≠ top → ∃ i : ι s, i ≠ k ∧ f i = p)).card % 2
    = if Function.Surjective f then 1 else 0 := by
  -- Cardinality dichotomy
  rcases lt_or_eq_of_le hι_size with hlt | heq
  · -- §1.1: |ι s| < |P| ⇒ both sides 0
    have hnsurj : ¬ Function.Surjective f := by
      intro hsurj
      exact absurd (Fintype.card_le_of_surjective _ hsurj) (not_le.mpr hlt)
    rw [if_neg hnsurj]
    suffices hempty :
        (Finset.univ.filter (fun k : ι s =>
          ∀ p, p ≠ top → ∃ i, i ≠ k ∧ f i = p)) = ∅ by
      rw [hempty]; rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, not_forall, not_exists]
    -- Need: ∃ p, p ≠ top ∧ ∀ i, i = k ∨ f i ≠ p
    -- i.e., (univ.erase k).image f ⊊ P \ {top}, contradicting any door witness
    -- Use Finset.card_image_le : ((univ.erase k).image f).card ≤ |univ.erase k|
    --   = |ι s| - 1 < |P| - 1 = |P \ {top}|, so some p ∈ P \ {top} is missing
    sorry  -- ~4–6 LOC inner cardinality argument
  · -- §1.2: |ι s| = |P| ⇒ reduce to parent via Equiv-transport
    -- Equality case proof:
    set n := Fintype.card P - 1 with hn_def
    have hP_pos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨top⟩
    have hP_eq : Fintype.card P = n + 1 := by omega
    -- Canonical equivs
    let e_ι : ι s ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (heq.trans hP_eq)
    let e_P_canon : P ≃ Fin (n + 1) := Fintype.equivFinOfCardEq hP_eq
    let e_swap : Equiv.Perm (Fin (n + 1)) :=
      Equiv.swap (e_P_canon top) (Fin.last n)
    let e_P : P ≃ Fin (n + 1) := e_P_canon.trans e_swap
    have he_top : e_P top = Fin.last n := by
      simp [e_P, e_swap, Equiv.swap_apply_left]
    -- Transport f to f'
    let f' : Fin (n + 1) → Fin (n + 1) := fun i => e_P (f (e_ι.symm i))
    -- Invoke parent
    have hparent := SpernerMathlib.door_count_parity n f'
    -- Now rewrite the LHS via the Finset bijection (e_ι : ι s ≃ Fin (n+1))
    -- and rewrite the door condition via he_top
    sorry  -- ~8–14 LOC Equiv-transport plumbing
```

The two remaining sub-sorries are **mechanical** — both are Mathlib-API
plumbing rather than mathematical content. The S2 ACT implementer should
estimate ~6 LOC for the inner cardinality argument and ~14 LOC for the
Equiv-transport, totaling ~20 LOC for the structural block.

## 4. Side effects on plumbing lemmas

### 4.1 `per_cell_door_parity_hyper` (S2 PREP §3 line ~110)

The S2 PREP audit (PR #18638) introduces `(hι_size : Fintype.card (ι s) ≤ Fintype.card P)`
as a per-theorem binder. Under the dichotomy route, this carries through verbatim:

```lean
lemma per_cell_door_parity_hyper {s : Cell}
    (hι_size : Fintype.card (ι s) ≤ Fintype.card P)
    (vertex : VertexMap) (c : V → P) (top : P) :
    (Finset.univ.filter (fun k : ι s => IsDoorHyper vertex c top s k)).card % 2
    = if IsPanchromaticHyper vertex c s then 1 else 0 := by
  have h := door_count_parity_hyper hι_size top (c ∘ vertex s)
  …  -- reshape the filter as in parent's per_cell_door_parity (line 470)
```

No additional impact beyond what S2 PREP audit already plans.

### 4.2 `sperner_parity_hyper`

Unchanged — the dichotomy is internal to `door_count_parity_hyper`. The
`sperner_parity_hyper` wiring through `hι_size` is identical to the multiplicity-
profile route.

### 4.3 `even_card_interior_doors_hyper`

Unchanged — does not invoke `door_count_parity_hyper`. The involution argument
operates on Σ-pairs over `Cell × ι s` and is independent of cardinality.

## 5. Anti-targets

- **Don't try to weaken `hι_size : ≤` to `< ∞` or similar.** The strict `<` case
  is *parity-vacuous*, but the *door-count-zero* claim genuinely requires the
  cardinality bound to enable the pigeonhole. Without `hι_size`, S1e §"Case 3"'s
  counter-example (`|ι s| = 4, |P| = 3`) flips the parity.

- **Don't replace `Equiv.swap` with `Equiv.permCongr` or `Equiv.optionSubtype`.**
  `Equiv.swap` is the simplest available; the alternatives add a level of
  destructuring that breaks the simp chain.

- **Don't try to drop the `noncomputable` annotations.** Mathlib's
  `Fintype.equivOfCardEq` is unavoidably non-computable (uses `Quotient.out`).
  The S2 ACT file does not need a computable bijection; all theorem statements
  are propositions.

- **Don't generalize `door_count_parity` itself in parent.** While
  abstracting `Fin (d+1) → Fin (d+1)` to `α → β` with `|α| = |β|` would be
  conceptually cleaner, it requires touching the verified parent file. The
  Equiv-transport route lets S2 ACT ship without changing
  `proofs/Proofs/SpernerMathlib.lean`.

## 6. Race awareness (push time)

`gh pr list --repo rjwalters/lean-genius --search "sperner-mathlib-oq-01 in:title" --state open`
at 2026-05-13 ~08:25 UTC: empty.

`gh pr list --repo rjwalters/lean-genius --search "sperner in:title" --state open`:

- PR #17621 / 17571 / 17984 — all on `sperner-ndim-mathlib-oq-02` (different slug,
  abstract-CellComplex line; orthogonal to hypergraph generalisation).
- PR #18677 (`sperner-simplicial-bridge-oq-01` S4 GALLERY) — concrete simplicial
  triangulation, orthogonal to hypergraph generalisation.

`git log origin/main --oneline | grep sperner-mathlib-oq-01`:

- PR #18638 (S2 PREP audit) merged 2026-05-13T07:19:50Z — ~1 hour before this push.

No in-flight S2 ACT branch for `sperner-mathlib-oq-01`. Last merge on this slug
was the S2 PREP audit (#18638), which this PREP cites as a predecessor.

**Race risk: low.** This PREP is a pure session-note that adds exactly one
file; pristine vs. any concurrent S2 ACT attempt; reviewer-useful regardless
of who ships S2 ACT first.

## 7. Sibling-slug cross-checks

`sperner-simplicial-bridge-oq-01` and `sperner-simplicial-instance-oq-01` are
concrete simplicial-bridge / triangulation-instance formalisations. The
dichotomy/Equiv-transport machinery proposed here is specific to the *abstract
hypergraph* line — orthogonal to those slugs.

`sperner-ndim-mathlib-oq-02` (PRs #17571, #17621, #17984) targets a different
generalisation axis (n-dimensional CellComplex with explicit grid coordinates);
no overlap.

`sperner-ndim-mathlib-oq-01-oq-04` (PR #18325 merged) is the signed CellComplex
bridge — a different extension axis; no overlap.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/SpernerMathlib.lean` (897 lines, verified parent file)
- `proofs/Proofs/SpernerMathlibHyper.lean` (S2 ACT target — does not exist yet)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sperner-mathlib-oq-01/problem.md`
- `research/problems/sperner-mathlib-oq-01/knowledge.md`
- `research/problems/sperner-mathlib-oq-01/state.md`
- `research/problems/sperner-mathlib-oq-01/sessions/2026-05-12-*.md` (5 S1 OBSERVE notes + S2 PREP)
- `research/problems/sperner-mathlib-oq-01/sessions/2026-05-13-s2-prep-audit-hi-size-and-mathlib-api.md`
- `src/data/research/problems/sperner-mathlib-oq-01.json`
- `.lean/state/candidate-pool.json`

Only this single new file is added under
`research/problems/sperner-mathlib-oq-01/sessions/`.

## 9. Consolidated S2 ACT checklist (updated)

Subsuming and refining the S2 PREP audit §9 checklist:

1. ☐ Section variables include `{ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]`
   and `{P : Type*} [Fintype P] [DecidableEq P]`.
2. ☐ `door_count_parity_hyper` and `per_cell_door_parity_hyper` each take
   `(hι_size : Fintype.card (ι s) ≤ Fintype.card P)` as a per-theorem binder.
3. ☐ `door_count_parity_hyper` body uses the **cardinality dichotomy** route:
   `rcases lt_or_eq_of_le hι_size` → §1.1 strict case (~6–10 LOC) + §1.2
   equality case (~12–18 LOC).
4. ☐ §1.2 invokes parent's `SpernerMathlib.door_count_parity` via
   `Fintype.equivFinOfCardEq` + `Equiv.swap (e_P top) (Fin.last n)`.
5. ☐ All Mathlib bearers cited in §2.1 resolve (verified at v4.26.0).
6. ☐ Specialization bridge `IsDoorHyper.specialize_to_original` uses
   `Fin.eq_castSucc_of_ne_last` per S2 PREP audit §4.
7. ☐ Estimated total LOC: **172–192** (down from 184–204 in S2 PREP audit §1.3).
8. ☐ The `door_count_parity_hyper` proof has **at most 2 sub-sorries** (the
   inner pigeonhole and the Equiv-transport plumbing), each ≤ 14 LOC. Both are
   mechanical and Mathlib-API-bound; mathematical content lives in parent.

## 10. Verification log (this PREP)

| Mathlib lookup | Verified |
|----------------|----------|
| `Fintype.equivFinOfCardEq` at `Mathlib/Data/Fintype/EquivFin.lean:124` | ✓ |
| `Fintype.equivOfCardEq` at `Mathlib/Data/Fintype/EquivFin.lean:143` | ✓ |
| `Equiv.swap` at `Mathlib/Logic/Equiv/Basic.lean:634` | ✓ |
| `Equiv.swap_apply_left` at `Mathlib/Logic/Equiv/Basic.lean:648` | ✓ |
| `Fintype.card_le_of_surjective` at `Mathlib/Data/Fintype/Card.lean` (search hit) | ✓ |

Parent `SpernerMathlib.door_count_parity` re-read at
`proofs/Proofs/SpernerMathlib.lean:321–330`; signature and proof skeleton
verified at HEAD `0cbd962f6bc` (which is `origin/main` at push time).

No `.lean` build attempted (worktree `.lake` symlink remains recursive — see
`feedback_researcher_lake_symlink_broken.md`); paper-and-pencil only.

## 11. What this PREP is **not**

- Not a Lean change. Zero `.lean` files touched.
- Not an S2 ACT implementation. `SpernerMathlibHyper.lean` remains future work.
- Not a re-survey. S1, S1b, S1c, S1d, S1e are the survey.
- Not a refactor of `SpernerMathlib.lean`. The parent file is verified and
  remains unchanged.
- Not addressing OQ-01-B (non-pure complexes) or OQ-01-C (boundary-axioms
  minimality). The dichotomy route is orthogonal to both sub-OQs.
- Not overturning the S2 PREP audit (#18638). The `hι_size` integration is
  fully accepted; this PREP *implements* it via a cleaner proof architecture.

## 12. Test plan

- [x] `Fintype.equivFinOfCardEq` declaration verified at v4.26.0.
- [x] `Fintype.equivOfCardEq` declaration verified at v4.26.0.
- [x] `Equiv.swap` + `Equiv.swap_apply_left` verified at v4.26.0.
- [x] `Fintype.card_le_of_surjective` verified at v4.26.0.
- [x] Parent `door_count_parity` signature re-confirmed at
      `proofs/Proofs/SpernerMathlib.lean:321–330`.
- [x] Dichotomy `rcases lt_or_eq_of_le` handles both strict and equality cases.
- [x] Strict case both-sides-zero verified by direct pigeonhole argument.
- [x] Equality case bijection construction `e_ι : ι s ≃ Fin (n+1)`,
      `e_P : P ≃ Fin (n+1)` (with `e_P top = Fin.last n`) verified by hand.
- [x] Cross-check S1e §"Case 3" counter-example (`|ι s| = 4`, `|P| = 3`,
      two cells with door counts 2 vs 3) — outside the `hι_size` regime,
      so unaffected by this PREP.
- [x] Race scan: no open PRs on `sperner-mathlib-oq-01`, no in-flight S2 branch.
- [x] No Lean build needed.

---

**End of S2c PREP — cardinality dichotomy + Equiv-transport reduction. No Lean
changes; integration of S1e + S2 PREP audit (#18638) via a cleaner architecture
for the structural sorry.**
