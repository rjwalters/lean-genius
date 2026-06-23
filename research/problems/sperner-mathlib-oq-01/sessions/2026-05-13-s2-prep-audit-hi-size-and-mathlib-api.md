# S2 PREP audit — `hι_size` integration + Mathlib API name verification

**Date**: 2026-05-13
**Author**: researcher-3
**Phase**: PREP audit (doc-only)
**Predecessors**:
- S1 OBSERVE (PR #18282, merged 2026-05-12 22:16Z): axioms inventory + hypergraph weakening map.
- S1b OBSERVE (PR #18344, merged 2026-05-12 22:53Z): `IsDoorHyper` top-color gap, `top : P` parameter.
- S1c OBSERVE (PR #18366, merged 2026-05-13 02:11Z): `hadj_ne` strong-vs-weak Σ-pair mismatch.
- S1d OBSERVE (PR #18387, merged 2026-05-13 02:10Z): `hadj_ne` derivability + self-loop classification.
- S1e OBSERVE (PR #18411, merged 2026-05-13 02:09Z): per-cell door parity by color
  multiplicity — `hι_size : ∀ s, |ι s| ≤ |P|` required for hypergraph parity.
- **S2 PREP (PR #18360, merged 2026-05-12 23:17Z)**: Σ-type ergonomics + file skeleton.

S2 PREP shipped **before** S1c/S1d/S1e were merged, so its file skeleton does **not**
incorporate:

1. **S1e's `hι_size` constraint** — without this, `door_count_parity_hyper` is *false* on
   super-pure cells (`|ι s| > |P|`); see S1e § "Case 3" for the explicit counter-example.
2. **S1c/S1d's `hadj_ne` refinements** — orthogonal; S1c addresses the Σ-pair form of the
   hypothesis, S1d shows a strictly weaker `no_self_face_loop` suffices.

Additionally, S2 PREP cites several Mathlib API names that turn out to be either
**renamed** in v4.26.0, or **slightly different in form** from what S2 PREP's audit grid
asserts. This PREP audits each cited name against `leanprover-community/mathlib4@v4.26.0`
via `gh api .../contents` and lists the corrections needed before S2 ACT lands.

**No Lean source changes.** **No** edits to `problem.md`, `state.md`, `knowledge.md`, the
gallery JSON, or any existing `sessions/*.md`. Adds exactly one file: this session note.

## 0. TL;DR for the S2 ACT implementer

Three corrections to S2 PREP (#18360) before opening `SpernerMathlibHyper.lean`:

| # | Correction | Source |
|---|-----------|--------|
| 1 | Add `(hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P)` to the file's section variables and condition `door_count_parity_hyper`, `per_cell_door_parity_hyper`, `even_card_interior_doors_hyper`, `sperner_parity_hyper`, `exists_panchromatic_hyper` on it. | S1e § "S2 ACT (file skeleton)" |
| 2 | Replace Mathlib API names in S2 PREP § 5 audit grid per the table in § 3 below. None of the underlying instances disappeared — only the *names* drifted. Auto-inference still works; explicit citations need updating. | This PREP § 3 |
| 3 | Rewrite the §4 specialization bridge `obtain ⟨j, rfl⟩` pattern: the existential from `Fin.eq_castSucc_of_ne_last` is `∃ y, Fin.castSucc y = p` (LHS-to-RHS), so `rfl` substitutes `p := Fin.castSucc j`. This is the correct direction; flag this explicitly to avoid future implementers second-guessing it. | This PREP § 4 |

Specialization to the original `SpernerMathlib.lean` API is recovered by
`hι_size := fun _ => le_refl _` (i.e. `|ι s| = |Fin (d + 1)| = |P|`).

## 1. The `hι_size` patch in detail

S1e (PR #18411, line 252) recommends adding to the section variables of
`SpernerMathlibHyper.lean`:

```lean
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]
variable (hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P)
```

The corrected signature of `door_count_parity_hyper` (S2 PREP § 2, lines 98–108) becomes:

```lean
theorem door_count_parity_hyper {s : Cell}
    (hι_size : Fintype.card (ι s) ≤ Fintype.card P)   -- NEW
    (f : ι s → P) (top : P) :
    (Finset.univ.filter
      (fun k : ι s => ∀ p, p ≠ top → ∃ i : ι s, i ≠ k ∧ f i = p)).card % 2
    = if Function.Surjective f then 1 else 0 := by
  sorry
```

### 1.1 Why this is needed (one-line)

S1e § "Case 3" exhibits two cells with `|ι s| = 4`, `|P| = 3`, both panchromatic, with
door counts 2 and 3 — opposite parities. The parity is a function of the multiplicity
profile `(m_p)_{p ∈ P}`, not of the panchromatic indicator alone. The `hι_size`
constraint forces `Σ_p m_p = |ι s| ≤ |P|`, eliminating the case where some non-top
color has multiplicity `≥ 2` while *another* non-top color also has multiplicity `≥ 1`
(the source of the parity flip).

### 1.2 Why "≤" not "="

Sub-pure cells (`|ι s| < |P|`) are *parity-vacuous* — both sides of the parity formula
evaluate to 0 (S1e § "Case 2"). Including them costs nothing and admits a small but
real generalisation over the pure case: a complex with mixed cardinalities all `≤ |P|`
satisfies the parity formula.

### 1.3 Concrete LOC impact on `SpernerMathlibHyper.lean`

| Block | S2 PREP estimate | Post-patch | Delta |
|-------|------------------|------------|-------|
| §1 Setup variables | 4 lines | 5 lines (`+1` for `hι_size`) | +1 |
| §3 `door_count_parity_hyper` signature | 4 lines | 5 lines (`+1` for explicit hyp) | +1 |
| §3 proof body | ~30–40 lines | ~30–40 lines (no change) | 0 |
| §4 `even_card_interior_doors_hyper` | unchanged (does not bind `hι_size`) | unchanged | 0 |
| §5 `sperner_parity_hyper` plumbing | ~30 lines | ~32 lines (`+2` for the wiring through) | +2 |
| §6 specialization bridge | ~25 lines | unchanged | 0 |

Net: **+4 LOC** in `SpernerMathlibHyper.lean`. Total file LOC estimate moves from
180–200 (S2 PREP § 2 closing estimate) to **184–204 LOC**.

### 1.4 Section-variable vs theorem-binder placement

S1e proposes `variable (hι_size : ...)` at section scope. A binder-level placement
(per-theorem `(hι_size : Fintype.card (ι s) ≤ Fintype.card P)`) is equivalent and
preserves the option of *not* binding it on plumbing lemmas that don't actually need
it (e.g. `even_card_interior_doors_hyper` — see § 1.5).

**Recommendation**: bind on each theorem that needs it (i.e. `door_count_parity_hyper`,
`per_cell_door_parity_hyper`, `sperner_parity_hyper`, `exists_panchromatic_hyper`)
rather than at section scope. This keeps the global statement of
`even_card_interior_doors_hyper` (which uses only `adj`, not the per-cell parity)
free of an extraneous hypothesis.

### 1.5 Does `even_card_interior_doors_hyper` need `hι_size`?

**No** — `even_card_interior_doors_hyper` (S2 PREP § 2 lines 112–128) closes door pairs
under the `adj`-involution. It does *not* invoke `door_count_parity_hyper`. The parity
of the door count *globally* (over `Σ s : Cell, ι s`) is even regardless of `hι_size`
because the proof is by an involution argument on Σ-pairs, not by summing per-cell
parities.

`hι_size` is consumed only when combining "interior doors are even" with "boundary door
count + interior door count = sum-of-per-cell-door-counts" — which is the
`sperner_parity_hyper` step that summons `door_count_parity_hyper` per cell.

## 2. Where S1c / S1d corrections do **not** apply to S2 ACT scope

For completeness, S2 ACT does **not** need to integrate S1c (#18366) or S1d (#18387)
because:

- **S1c**: addresses whether `hadj_ne` should be stated as `s ≠ s'` (strong) or as
  `(⟨s, i⟩ : Σ s, ι s) ≠ ⟨s', i'⟩` (weak Σ-pair). S2 PREP § 2 lines 118–119 *already*
  uses the weak Σ-pair form, so S2 PREP and S1c are *consistent*. The strong form lives
  only in `SpernerMathlib.lean:431` (the *original*, non-hyper file), and S1c argues the
  involution proof already only needs the weak form. **No S2 ACT change required**; an
  S3 follow-up could simplify the *original* file's hypothesis.

- **S1d**: shows that `hadj_ne` can be replaced by a `no_self_face_loop` + per-cell
  vertex-injectivity pair. This is an *axiom-narrowing* refactor, not a *correctness*
  fix. S2 ACT can ship with `hadj_ne` in its current Σ-pair form; S1d's narrower
  alternative is an S3 simplification.

**Net**: only S1e's `hι_size` is *load-bearing* for S2 ACT correctness. S1c/S1d are
refactor targets, not blockers.

## 3. Mathlib API name audit (verified against `mathlib4@v4.26.0`)

S2 PREP § 5 (lines 349–355) lists five typeclass synthesis claims. Three of the named
instances/lemmas do not exist under the cited name. Auto-inference still finds them
under the actual names; the table below replaces each citation with the verified
declaration name and file:line.

| Claim in S2 PREP § 5 | Actual name in v4.26.0 | File | Line | Status |
|----------------------|-----------------------|------|------|--------|
| `Sigma.fintype`      | `Sigma.instFintype`   | `Mathlib/Data/Fintype/Sigma.lean` | 43 | RENAMED |
| `Sigma.decidableEq`  | `instDecidableEqSigma` | `Mathlib/Data/Sigma/Basic.lean` | 47 | RENAMED |
| `Fintype.decidableForallFintype` | `Fintype.decidableForallFintype` | `Mathlib/Data/Fintype/Defs.lean` | 208 | ✓ |
| `Fintype.decidableExistsFintype` | `Fintype.decidableExistsFintype` | `Mathlib/Data/Fintype/Defs.lean` | 212 | ✓ |
| `Fintype.decidableSurjective` | `Fintype.decidableSurjectiveFintype` | `Mathlib/Data/Fintype/Defs.lean` | 241 | RENAMED |

### 3.1 Why this matters operationally

Lean does not require these names to be cited — `[Fintype α]` + `[∀ s, Fintype (ι s)]`
will resolve `Fintype (Σ s, ι s)` automatically via `Sigma.instFintype`. So all three
renames are **invisible at the use site**. They matter only:

1. When the S2 ACT implementer hits a "no instance found" error and needs to
   search for the named declaration to debug.
2. When subsequent docs cite these names as references — wrong names will fail to
   resolve under `gh api .../contents` audits.
3. When manual `(_ : Decidable (...))` ascriptions are needed (e.g. inside
   `Finset.filter` elaboration) — the manual term must use the correct name.

### 3.2 Verbatim declarations (from v4.26.0)

```lean
-- Mathlib/Data/Fintype/Sigma.lean:43
instance Sigma.instFintype : Fintype (Σ i, κ i) := ⟨univ.sigma fun _ ↦ univ, by simp⟩
```

```lean
-- Mathlib/Data/Sigma/Basic.lean:47
instance instDecidableEqSigma [h₁ : DecidableEq α] [h₂ : ∀ a, DecidableEq (β a)] :
    DecidableEq (Sigma β)
```

```lean
-- Mathlib/Data/Fintype/Defs.lean:208
instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∀ a, p a) := ...
```

```lean
-- Mathlib/Data/Fintype/Defs.lean:212
instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] :
    Decidable (∃ a, p a) := ...
```

```lean
-- Mathlib/Data/Fintype/Defs.lean:241
instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) :=
  fun x => by unfold Surjective; infer_instance
```

### 3.3 `Sigma.ext_iff` form drift (S2 PREP § 3 pitfall C)

S2 PREP § 3 (lines 226–230) states:

```lean
theorem Sigma.ext_iff : (⟨s, i⟩ : Σ s, ι s) = ⟨s', i'⟩
    ↔ ∃ h : s = s', h ▸ i = i'
```

The actual Lean-auto-generated `Sigma.ext_iff` form (and the explicit
`Sigma.mk.inj_iff` at `Mathlib/Data/Sigma/Basic.lean:58`) uses **HEq**, not a dependent
existential:

```lean
-- Mathlib/Data/Sigma/Basic.lean:58
theorem mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
    Sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ a₁ = a₂ ∧ b₁ ≍ b₂ := by simp
```

(The symbol `≍` is `HEq`.) The dependent form `∃ h, h ▸ i = i'` requires manually
extracting `h := mk.inj_iff.mp ‹...›.1` and using `Eq.recOn` rather than `▸`. For
the S2 ACT's actual usage in `hadj_ne` (S2 PREP § 2 lines 118–119), the relevant
implication is the **forward** direction of the negation:

```lean
-- need to show: (⟨s, i⟩ : Σ s, ι s) = ⟨s', i'⟩ → False
-- given: hadj_ne s i s' i' hadj_eq : (⟨s, i⟩ : Σ s, ι s) ≠ ⟨s', i'⟩
-- supplied: the Sigma equality from match h with | rfl => ...
```

which **doesn't require destructuring** — `hadj_ne` directly contradicts the
hypothetical Σ-equality. So the `Sigma.ext_iff` form drift is **inert** at the
S2 ACT use site; the form correction matters only for documentation precision.

### 3.4 What works without name corrections (the happy path)

If the S2 ACT implementer simply writes:

```lean
variable {V Cell : Type*} [DecidableEq V] [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]
variable (hι_size : ∀ s : Cell, Fintype.card (ι s) ≤ Fintype.card P)
```

then every claim in S2 PREP § 5's audit grid resolves via auto-inference: the
`Fintype (Σ s, ι s)`, `DecidableEq (Σ s, ι s)`, and `Decidable (IsDoorHyper ...)`
instances all synthesise without the user citing them by name. This PREP § 3 matters
only when those auto-inferences *fail* (rare, but possible if the implementer adds
extra typeclass constraints that confuse Lean's instance search).

## 4. Specialization bridge — direction note

S2 PREP § 4 (lines 286–328) sketches `IsDoorHyper.specialize_to_original`. The fallback
path (lines 322–328) uses:

```lean
  · intro horig p hp_ne_top
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last p hp_ne_top
    exact horig j |>.imp (fun i ⟨hi_ne, hi_eq⟩ => ⟨hi_ne, hi_eq⟩)
```

The Mathlib v4.26.0 declaration is:

```lean
-- Mathlib/Data/Fin/SuccPred.lean:188
theorem eq_castSucc_of_ne_last {x : Fin (n + 1)} (h : x ≠ (last _)) :
    ∃ y, Fin.castSucc y = x := exists_castSucc_eq.mpr h
```

The existential is **`∃ y, Fin.castSucc y = x`** — LHS is `Fin.castSucc y`, RHS is `x`
(the parameter). When `obtain ⟨j, rfl⟩ := h` destructures, the equation
`Fin.castSucc j = p` is used as a rewrite: Lean substitutes `p := Fin.castSucc j`
everywhere in the goal (because `p` is a free local variable on the RHS).

**This is the correct direction** for the S2 PREP usage. Flagging it explicitly:

- After `obtain ⟨j, rfl⟩`: in the remaining goal, every occurrence of `p` is replaced
  by `Fin.castSucc j`.
- `horig j` (applying the original `IsDoor vertex c s k` for face-index `j : Fin d`)
  produces the witness with `f i = ⟨j.val, _⟩`. The post-substitution match against the
  goal's `c (vertex s i) = Fin.castSucc j` works because `Fin.castSucc j` has value
  `j.val` and is the unique `Fin (d + 1)` of that value.

**No correction needed** to S2 PREP §4 — the proof is right; just confirming via
the verified Mathlib declaration.

### 4.1 Even simpler alternative

S1e § "Implications for OQ-01-A" and the v4.26.0 file also expose:

```lean
-- Mathlib/Data/Fin/SuccPred.lean:197 (close to eq_castSucc_of_ne_last)
theorem eq_castSucc_or_eq_last {n : Nat} (i : Fin (n + 1)) :
    (∃ j : Fin n, i = j.castSucc) ∨ i = last n := i.lastCases (Or.inr rfl) (Or.inl ⟨·, rfl⟩)
```

This trichotomy form **inverts the existential direction** (`i = j.castSucc` instead of
`j.castSucc = i`) and bakes in the case split. For the S2 PREP §4 fallback, using
`eq_castSucc_or_eq_last` would let:

```lean
  · intro horig p hp_ne_top
    rcases Fin.eq_castSucc_or_eq_last p with ⟨j, rfl⟩ | rfl
    · exact horig j
    · exact absurd rfl hp_ne_top
```

This is ~1 line longer than the original §4 fallback but more transparent (no
`Fin.castSucc y = x` direction-flip subtlety).

## 5. Decidability instance chain — post-rename verification

Re-running S2 PREP § 3 pitfall E's typeclass chain under the corrected names:

```lean
-- Goal: Decidable (IsDoorHyper vertex c top s k)
-- IsDoorHyper unfolds to: ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p
--
-- Decomposition:
--   1. ∀ p : P, Q p   — needs Decidable (Q p) + Fintype P → decidableForallFintype
--   2. Q p = (p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p)
--      = (p ≠ top → Q' p)
--     — implication, decidable when antecedent and consequent are
--   3. p ≠ top — Decidable by DecidableEq P
--   4. Q' p = ∃ i : ι s, R p i — needs Decidable (R p i) + Fintype (ι s) → decidableExistsFintype
--   5. R p i = (i ≠ k ∧ c (vertex s i) = p) — both decidable
--      i ≠ k — DecidableEq (ι s)
--      c (vertex s i) = p — DecidableEq P
```

All instances exist (with the names in § 3.2). `Fintype.decidableForallFintype`
(line 208) and `Fintype.decidableExistsFintype` (line 212) are unrenamed; the chain
unfolds the same way under v4.26.0 as under S2 PREP's draft.

## 6. Race awareness (push time)

`gh pr list --repo rjwalters/lean-genius --search "sperner-mathlib-oq-01 in:title" --state all`
at 2026-05-13 ~07:15 UTC:

| PR | State | Title | Pushed |
|----|-------|-------|--------|
| #18282 | MERGED 22:16Z | S1 OBSERVE — axioms audit | 2026-05-12 |
| #18344 | MERGED 22:53Z | S1b OBSERVE — `IsDoorHyper` top-color gap | 2026-05-12 |
| #18360 | MERGED 23:17Z | **S2 PREP** — Σ-ergonomics + file skeleton | 2026-05-12 |
| #18366 | MERGED 02:11Z | S1c OBSERVE — `hadj_ne` strong/weak | 2026-05-13 |
| #18387 | MERGED 02:10Z | S1d OBSERVE — `hadj_ne` derivability | 2026-05-13 |
| #18411 | MERGED 02:09Z | S1e OBSERVE — per-cell parity by multiplicity | 2026-05-13 |

No open PRs on this slug. Last merge: 02:11Z (~5h before push). No `sperner-mathlib-oq-01`
branch in `git branch -r` other than this one. No `git log origin/main --grep` activity on
this slug since 02:11Z.

**Race risk: low.** This PREP is a pure session-note that does not edit any prior file.
Pristine vs. any concurrent S2 ACT attempt; reviewer-useful regardless of who ships
S2 ACT first.

## 7. Sibling-slug cross-checks

`sperner-simplicial-bridge-oq-01` and `sperner-simplicial-instance-oq-01` are concrete
simplicial-bridge / triangulation-instance formalisations — orthogonal to the
*abstract hypergraph* generalisation here. No content overlap.

`sperner-ndim-mathlib-oq-01` is the *predecessor* slug for this OQ (different naming
convention — confirmed by inspecting `proofs/Proofs/SpernerMathlib.lean:347` which
houses `IsPanchromatic` at the file the slug points to). The OQ-01 family is layered:

- `sperner-ndim-mathlib-oq-01`: base file, currently verified.
- `sperner-mathlib-oq-01`: hypergraph generalisation (this slug, S1 through S2 PREP).
- `sperner-ndim-mathlib-oq-01-oq-04` (PR #18325 merged): signed CellComplex bridge,
  a *different* extension axis.

Neither sibling touches the per-cell parity formula or the Mathlib API audit grid,
so this PREP is non-overlapping with their forward work.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/SpernerMathlib.lean` (897 lines, verified parent file)
- `proofs/Proofs/SpernerMathlibHyper.lean` (S2 ACT target — does not exist yet)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sperner-mathlib-oq-01/problem.md`
- `research/problems/sperner-mathlib-oq-01/knowledge.md`
- `research/problems/sperner-mathlib-oq-01/state.md`
- `research/problems/sperner-mathlib-oq-01/sessions/2026-05-12-*.md` (the five S1/S1b/S1c/S1d/S1e + S2 PREP files)
- `src/data/research/problems/sperner-mathlib-oq-01.json`
- `.lean/state/candidate-pool.json`

Only this single new file is added under `research/problems/sperner-mathlib-oq-01/sessions/`.

## 9. S2 ACT checklist (consolidated)

For the next implementer opening `proofs/Proofs/SpernerMathlibHyper.lean`:

1. ☐ Add `(hι_size : ∀ s, Fintype.card (ι s) ≤ Fintype.card P)` (or per-theorem binder
   — see § 1.4). Required by S1e for `door_count_parity_hyper` correctness.
2. ☐ Use `hadj_ne` in the Σ-pair form `(⟨s, i⟩ : Σ s, ι s) ≠ ⟨s', i'⟩` per S2 PREP
   § 2 lines 118–119 (S1c/S1d narrowing is S3, not S2).
3. ☐ Auto-inference of typeclass instances works as written; no name citations needed.
   Names in § 3 of this PREP are only for debugging "no instance" errors.
4. ☐ Specialization bridge §4 uses `Fin.eq_castSucc_of_ne_last`
   (`Mathlib/Data/Fin/SuccPred.lean:188`); the existential direction is
   `∃ y, Fin.castSucc y = x` — § 4 of this PREP confirms the `obtain ⟨j, rfl⟩` is
   correct.
5. ☐ Estimated total LOC after the patch: **184–204 LOC** (S2 PREP estimate 180–200
   + 4 LOC for `hι_size` plumbing).
6. ☐ The `door_count_parity_hyper` sorry remains the *structural sorry* — see S2 PREP
   § 6 anti-targets for the option to ship with that sorry intact and chase it in S3.

## 10. Verification log (this PREP)

For audit reproducibility, the `mathlib4@v4.26.0` lookups in § 3 were performed at
push time via:

```bash
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Sigma.lean?ref=v4.26.0' | jq -r '.content' | base64 -d | grep -n "Sigma.instFintype"
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Sigma/Basic.lean?ref=v4.26.0' | jq -r '.content' | base64 -d | grep -n "instDecidableEqSigma\|mk.inj_iff"
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Defs.lean?ref=v4.26.0' | jq -r '.content' | base64 -d | grep -n "decidableForallFintype\|decidableExistsFintype\|decidableSurjectiveFintype"
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fin/SuccPred.lean?ref=v4.26.0' | jq -r '.content' | base64 -d | grep -n "eq_castSucc_of_ne_last\|eq_castSucc_or_eq_last"
```

All five Mathlib files exist at the cited line numbers. `Fintype.decidableForallFintype`
(line 208) and `Fintype.decidableExistsFintype` (line 212) are verbatim as S2 PREP cites.
The three renamed declarations (`Sigma.instFintype`, `instDecidableEqSigma`,
`Fintype.decidableSurjectiveFintype`) are at the line numbers tabled in § 3.

`gh api search/code` was not used (rate-limited; Contents-API fallbacks were
sufficient for all four targeted files).

## 11. What this PREP is **not**

- Not a Lean change. No `.lean` files touched.
- Not an S2 ACT implementation. The actual `SpernerMathlibHyper.lean` is still future
  work — this PREP only patches the *plan* for it.
- Not a re-survey. S1, S1b, S1c, S1d, S1e are the survey; this PREP integrates and
  validates them against the S2 PREP file skeleton.
- Not a re-statement of `IsDoorHyper`. S1b's `top : P` correction is fully accepted;
  this PREP supplements (does not overturn) it.
- Not addressing OQ-01-B (non-pure complexes) or OQ-01-C (boundary-axioms minimality)
  beyond cross-referencing S1d's narrowing as an S3 candidate.

## 12. Test plan

- [x] `Fin.eq_castSucc_of_ne_last` declaration verified at
      `Mathlib/Data/Fin/SuccPred.lean:188`, signature confirmed.
- [x] `Sigma.instFintype` declaration verified at
      `Mathlib/Data/Fintype/Sigma.lean:43`, signature confirmed.
- [x] `instDecidableEqSigma` declaration verified at
      `Mathlib/Data/Sigma/Basic.lean:47`, signature confirmed.
- [x] `Fintype.decidableForallFintype` / `Fintype.decidableExistsFintype` verified at
      `Mathlib/Data/Fintype/Defs.lean:208,212`, unrenamed.
- [x] `Fintype.decidableSurjectiveFintype` (NOT `Fintype.decidableSurjective`) verified
      at `Mathlib/Data/Fintype/Defs.lean:241`.
- [x] `Sigma.mk.inj_iff` HEq form verified at `Mathlib/Data/Sigma/Basic.lean:58`.
- [x] Cross-check S1e Case 3 counter-example (`|ι s| = 4, |P| = 3`, two panchromatic
      cells with door counts 2 vs 3) — by direct enumeration, confirms `hι_size`
      necessity.
- [x] Race scan: no open PRs on `sperner-mathlib-oq-01`, no in-flight S2 branches.
- [x] No Lean build required — paper-and-pencil audit only.

---

**End of S2 PREP audit. No Lean changes shipped; integration of S1e + Mathlib name
verification only.**
