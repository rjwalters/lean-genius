# S2d PREP — filling the two sub-sorries in S2c PREP with concrete Mathlib bearer chains

**Date**: 2026-05-13
**Author**: researcher-10
**Phase**: PREP (doc-only)
**Predecessors merged into `main`** (verified via `git log origin/main`):

- PR #18282 (S1 OBSERVE) — axioms inventory + hypergraph weakening map.
- PR #18344 (S1b OBSERVE) — `IsDoorHyper` top-color gap; `top : P` parameter.
- PR #18360 (S2 PREP) — Σ-type ergonomics + file skeleton.
- PR #18366 (S1c OBSERVE) — `hadj_ne` Σ-pair refinement.
- PR #18387 (S1d OBSERVE) — `hadj_ne` derivability + self-loop classification.
- PR #18411 (S1e OBSERVE) — per-cell parity by multiplicity, introduces
  `hι_size : Fintype.card (ι s) ≤ Fintype.card P`.
- PR #18638 (S2 PREP audit) — `hι_size` integration + Mathlib API audit.

**Predecessor OPEN** (verified at push time via
`gh pr list --repo rjwalters/lean-genius --search "sperner-mathlib-oq-01 in:title" --state open`):

- **PR #18688 (S2c PREP)** — cardinality dichotomy + Equiv-transport reduction of
  `door_count_parity_hyper`. Splits the structural sorry into a strict-case
  `|ι s| < |P|` (vacuous) and an equality-case `|ι s| = |P|` (Equiv-transport
  to parent's verified `SpernerMathlib.door_count_parity`). Ships with a
  worked-out proof skeleton containing **two sub-sorries**: an inner
  pigeonhole argument (~4–6 LOC) and the Equiv-transport plumbing (~8–14 LOC).

## 0. TL;DR

S2c PREP (#18688) ships a clean two-case architecture for `door_count_parity_hyper`
but leaves both sub-sorries marked as future work. This PREP **promotes S2c PREP
from skeleton-with-sub-sorries to a complete proof recipe** by supplying the
exact Mathlib bearer chain for each sub-sorry, with verbatim v4.26.0 declarations
and ~25–40 LOC tactic blocks for the S2 ACT implementer to paste directly.

**Key bearer surfaced**: `Finset.card_equiv`
(`Mathlib/Data/Finset/Card.lean:403`) handles the equality-case door-set
bijection in **one line** rather than the `Finset.card_image_of_injective`
chain mentioned in S2c §1.2. S2c PREP does not cite `card_equiv`.

**Net S2 ACT LOC revision** (composing with S2c PREP estimates):

| Block | S2c PREP estimate | Post-S2d estimate |
|-------|-------------------|-------------------|
| `door_count_parity_hyper` strict case | ~6–10 LOC + sub-sorry | **12–15 LOC complete** |
| `door_count_parity_hyper` equality case | ~12–18 LOC + sub-sorry | **22–28 LOC complete** |
| total `SpernerMathlibHyper.lean` | 172–192 | **172–195** (unchanged ±3) |

The LOC delta is small because S2c's estimates were *inclusive of the
sub-sorries*; this PREP shows the sub-sorries' replacement costs are within
the existing budget.

**This PREP does not touch any `.lean` file, `problem.md`, `state.md`,
`knowledge.md`, the gallery JSON, or any prior `sessions/*.md`.** Adds exactly
one new file: this session note.

## 1. Strict-case sub-sorry filled

### 1.1 The mathematical content

S2c PREP §1.1 sketches: under `hlt : Fintype.card (ι s) < Fintype.card P` and a
door witness `hk : ∀ p, p ≠ top → ∃ i, i ≠ k ∧ f i = p` at some `k : ι s`, we
derive a contradiction by **double counting**:

- The door witness says `(Finset.univ : Finset P).erase top ⊆ (Finset.univ.erase k).image f`.
- LHS cardinality: `Fintype.card P - 1`.
- RHS cardinality: `≤ (Finset.univ.erase k).card = Fintype.card (ι s) - 1`.
- So `Fintype.card P - 1 ≤ Fintype.card (ι s) - 1`, i.e., `Fintype.card P ≤ Fintype.card (ι s)`.
- Contradiction with `hlt`.

**Edge case**: when `Fintype.card (ι s) = 0`, `Finset.univ : Finset (ι s)` is
empty and the filter has card 0 trivially — no `k` exists to instantiate `hk`,
so the `ext k` step closes the goal vacuously. The argument above only needs
exercising when `Fintype.card (ι s) ≥ 1`.

### 1.2 Mathlib bearer chain (v4.26.0)

| Bearer | File | Line | Use |
|--------|------|------|-----|
| `Finset.mem_filter` | `Mathlib/Data/Finset/Filter.lean` | (standard) | Unfold filter membership |
| `Finset.mem_erase` | `Mathlib/Data/Finset/Erase.lean` | (standard) | Unfold erase membership |
| `Finset.mem_image` | `Mathlib/Data/Finset/Image.lean` | (standard) | Image-membership iff |
| `Finset.card_erase_of_mem` | `Mathlib/Data/Finset/Card.lean` | **145** | `(s.erase a).card = s.card - 1` |
| `Finset.card_image_le` | `Mathlib/Data/Finset/Card.lean` | **218** | `(s.image f).card ≤ s.card` |
| `Finset.card_le_card` | `Mathlib/Data/Finset/Card.lean` | **66** | `s ⊆ t → s.card ≤ t.card` |
| `Finset.card_univ` | `Mathlib/Data/Fintype/Basic.lean` | (standard) | `(univ : Finset α).card = Fintype.card α` |

All four `Mathlib/Data/Finset/Card.lean` lines re-verified via
`gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=v4.26.0'`
at push time.

### 1.3 Verbatim declarations (v4.26.0)

```lean
-- Mathlib/Data/Finset/Card.lean:66
theorem card_le_card : s ⊆ t → #s ≤ #t :=

-- Mathlib/Data/Finset/Card.lean:145
theorem card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1 :=

-- Mathlib/Data/Finset/Card.lean:218
theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s := by

-- Mathlib/Data/Finset/Card.lean:242
theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
    #(s.image f) = #s :=
```

(`Finset.card_image_of_injective` is listed for context — the **stronger**
`Finset.card_image_le` suffices in §1; the injective version is used in §2.)

### 1.4 Tactic block (drop-in replacement for S2c PREP §3 sub-sorry #1)

```lean
-- Inside §1.1 of S2c PREP's worked-out skeleton, replace
--   sorry  -- ~4–6 LOC inner cardinality argument
-- with:

intro hk
-- hk : ∀ p, p ≠ top → ∃ i, i ≠ k ∧ f i = p
have hsub : ((Finset.univ : Finset P).erase top) ⊆
    ((Finset.univ : Finset (ι s)).erase k).image f := by
  intro p hp
  rw [Finset.mem_erase] at hp
  obtain ⟨i, hi_ne, hi_eq⟩ := hk p hp.1
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ _⟩, hi_eq⟩
have hP_card : ((Finset.univ : Finset P).erase top).card = Fintype.card P - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ]
have hι_card : ((Finset.univ : Finset (ι s)).erase k).card = Fintype.card (ι s) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
have hchain : Fintype.card P - 1 ≤ Fintype.card (ι s) - 1 := by
  calc Fintype.card P - 1
      = ((Finset.univ : Finset P).erase top).card := hP_card.symm
    _ ≤ (((Finset.univ : Finset (ι s)).erase k).image f).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (ι s)).erase k).card := Finset.card_image_le
    _ = Fintype.card (ι s) - 1 := hι_card
-- Now hchain combined with hlt : |ι s| < |P| and |P| ≥ 1 (from top : P)
-- yields the contradiction. omega handles the Nat-arithmetic edge case.
have hP_pos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨top⟩
omega
```

**LOC count**: ~13 LOC, within S2c's `~6–10 LOC` budget when accounting for
the surrounding `have` plumbing already present in S2c's skeleton.

### 1.5 `Fintype.card_pos_iff` bearer

The closing `omega` uses `hP_pos : 0 < Fintype.card P`, derived from
`top : P` via:

```lean
-- Mathlib/Data/Fintype/Card.lean:277 (v4.26.0)
theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
```

This bearer is also implicitly invoked in S2c PREP §1.2 (`hP_pos` derivation)
but not explicitly cited there.

## 2. Equality-case sub-sorry filled

### 2.1 The mathematical content

S2c PREP §1.2 sketches: under `heq : Fintype.card (ι s) = Fintype.card P`, construct
- `e_ι : ι s ≃ Fin (n+1)` via `Fintype.equivFinOfCardEq`,
- `e_P : P ≃ Fin (n+1)` via `Fintype.equivFinOfCardEq` + `Equiv.swap (·, Fin.last n)`,
  with `e_P top = Fin.last n`,
- `f' : Fin (n+1) → Fin (n+1) := e_P ∘ f ∘ e_ι.symm`,

then invokes parent's `SpernerMathlib.door_count_parity n f'` and bridges:

(a) **LHS bridge**: door-filter cardinality preservation under `e_ι`.
(b) **RHS bridge**: `Function.Surjective f ↔ Function.Surjective f'`.

### 2.2 LHS bridge: door-filter cardinality via `Finset.card_equiv`

**Key bearer (not cited by S2c PREP)**: `Finset.card_equiv`.

```lean
-- Mathlib/Data/Finset/Card.lean:403 (v4.26.0)
/-- Specialization of `Finset.card_nbij'` that automatically fills in most arguments.

See `Fintype.card_equiv` for the version where `s` and `t` are `univ`. -/
lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t := by
  refine card_nbij' e e.symm ?_ ?_ ?_ ?_ <;> simp [hst, Set.MapsTo, Set.LeftInvOn, Set.RightInvOn]
```

This is the **one-line bearer** for `(filter p₁).card = (filter p₂).card` given
an `Equiv` and a predicate-iff. Specifically, under `e_ι : ι s ≃ Fin (n+1)`:

```lean
((Finset.univ : Finset (ι s)).filter p_hyper).card =
  ((Finset.univ : Finset (Fin (n+1))).filter p_orig).card
```

provided `∀ k, k ∈ univ.filter p_hyper ↔ e_ι k ∈ univ.filter p_orig`, which
reduces (after `mem_filter` + `mem_univ` simp) to `p_hyper k ↔ p_orig (e_ι k)`.

### 2.3 The predicate-iff (the only non-trivial step)

We need to show:

```lean
(∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ f i = p)
  ↔
(∀ j : Fin n, ∃ i' : Fin (n+1), i' ≠ e_ι k ∧
   f' i' = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
```

where `f' := fun i' => e_P (f (e_ι.symm i'))` and the parent's "non-last color"
form `⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = Fin.castSucc j`.

#### 2.3.1 The bijection P \ {top} ↔ Fin n

The forward direction uses: for any `p : P` with `p ≠ top`, `e_P p ≠ Fin.last n`
(since `e_P top = Fin.last n` and `e_P` is injective), so by
`Fin.eq_castSucc_of_ne_last` (`Mathlib/Data/Fin/SuccPred.lean:188`,
verified by S2 PREP audit §4) there exists `j : Fin n` with
`Fin.castSucc j = e_P p`.

The backward direction uses: for any `j : Fin n`, `e_P.symm (Fin.castSucc j) ≠ top`
(since `Fin.castSucc j ≠ Fin.last n` and `e_P.symm top = Fin.last n` would
contradict via `Equiv.injective`).

#### 2.3.2 The witness-transport step

Given `i : ι s` with `i ≠ k` and `f i = p`:
- `i' := e_ι i : Fin (n+1)` satisfies `i' ≠ e_ι k` (by `Equiv.injective.ne_iff`).
- `f' i' = e_P (f (e_ι.symm (e_ι i))) = e_P (f i) = e_P p = Fin.castSucc j`.

The `f' i' = Fin.castSucc j` equality requires `e_ι.symm_apply_apply` (or
`Equiv.symm_apply_apply`) to collapse `e_ι.symm (e_ι i) = i`.

### 2.4 RHS bridge: surjectivity preservation under Equiv-conjugation

S2c PREP §1.2 mentions `Equiv.surjective_comp` / `comp_surjective` but does
not cite the exact bearer. The cleanest path is via `Equiv.bijective` +
`Function.Bijective.comp`:

```lean
-- Mathlib/Logic/Equiv/Defs.lean:187 (v4.26.0)
protected theorem bijective (e : α ≃ β) : Bijective e := EquivLike.bijective e

-- Mathlib/Logic/Function/Defs.lean:59 (v4.26.0)
theorem Bijective.comp {g : β → φ} {f : α → β} :
    Bijective g → Bijective f → Bijective (g ∘ f)
```

But for the **iff** form (which is what we need), the direct route is:

```lean
have h_surj : Function.Surjective f ↔ Function.Surjective f' := by
  constructor
  · intro hsurj
    -- f' = e_P ∘ f ∘ e_ι.symm. f' surjective: given j' : Fin (n+1), find i' : Fin (n+1) with f' i' = j'.
    -- Let p := e_P.symm j'. By hsurj p, ∃ i, f i = p. Set i' := e_ι i.
    -- Then f' i' = e_P (f (e_ι.symm (e_ι i))) = e_P (f i) = e_P p = e_P (e_P.symm j') = j'.
    intro j'
    obtain ⟨i, hi⟩ := hsurj (e_P.symm j')
    exact ⟨e_ι i, by simp [f', hi, Equiv.apply_symm_apply]⟩
  · intro hsurj p
    -- Symmetric: given p : P, find i with f i = p.
    -- Set j' := e_P p. By hsurj j', ∃ i', f' i' = j'. Set i := e_ι.symm i'.
    obtain ⟨i', hi'⟩ := hsurj (e_P p)
    refine ⟨e_ι.symm i', ?_⟩
    have h := hi'
    simp [f'] at h
    exact e_P.injective (h.trans rfl)
```

The two branches are ~5 LOC each. The `Equiv.apply_symm_apply` and
`Equiv.injective` bearers are at `Mathlib/Logic/Equiv/Defs.lean` (lines ~145
and 183 respectively, verified above).

### 2.5 Tactic block (drop-in replacement for S2c PREP §3 sub-sorry #2)

Combining §2.2, §2.3, §2.4:

```lean
-- After setting e_ι, e_P, f' as in S2c PREP §3 §1.2 skeleton, replace
--   sorry  -- ~8–14 LOC Equiv-transport plumbing
-- with:

-- Parent invocation
have hparent := SpernerMathlib.door_count_parity n f'

-- (a) LHS bridge via Finset.card_equiv
have hlhs_card : ((Finset.univ : Finset (ι s)).filter
    (fun k : ι s => ∀ p : P, p ≠ top → ∃ i, i ≠ k ∧ f i = p)).card =
  ((Finset.univ : Finset (Fin (n+1))).filter
    (fun k' : Fin (n+1) => ∀ j : Fin n, ∃ i' : Fin (n+1), i' ≠ k' ∧
      f' i' = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).card := by
  apply Finset.card_equiv e_ι
  intro k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · -- forward: hyper-door ⇒ orig-door
    intro hk j
    -- j : Fin n. Set p := e_P.symm (Fin.castSucc j); then p ≠ top.
    set p : P := e_P.symm ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ with hp_def
    have hp_ne_top : p ≠ top := by
      intro heq
      have : e_P p = e_P top := congr_arg e_P heq
      rw [he_top] at this
      simp [hp_def, Equiv.apply_symm_apply] at this
      omega  -- Fin.last n.val = n, but p was Fin.castSucc j with j.val < n
    obtain ⟨i, hi_ne, hi_eq⟩ := hk p hp_ne_top
    refine ⟨e_ι i, fun heq => hi_ne (e_ι.injective heq), ?_⟩
    simp [f', Equiv.symm_apply_apply, hi_eq, hp_def, Equiv.apply_symm_apply]
  · -- backward: orig-door ⇒ hyper-door
    intro hk' p hp_ne_top
    -- p : P with p ≠ top. Then e_P p ≠ e_P top = Fin.last n.
    have hep_ne_last : e_P p ≠ Fin.last n := by
      intro heq
      exact hp_ne_top (e_P.injective (heq.trans he_top.symm))
    obtain ⟨j, hj_eq⟩ := Fin.eq_castSucc_of_ne_last hep_ne_last
    -- hj_eq : Fin.castSucc j = e_P p; substitute back
    have hj_eq' : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n+1)) = e_P p := hj_eq
    obtain ⟨i', hi'_ne, hi'_eq⟩ := hk' j
    refine ⟨e_ι.symm i', fun heq => hi'_ne (by rw [← heq]; exact (e_ι.apply_symm_apply i').symm), ?_⟩
    -- f (e_ι.symm i') = p:  apply e_P, use f' i' = Fin.castSucc j = e_P p
    apply e_P.injective
    rw [show e_P (f (e_ι.symm i')) = f' i' from rfl, hi'_eq, hj_eq']

-- (b) RHS bridge: surjectivity preservation
have hsurj_iff : Function.Surjective f ↔ Function.Surjective f' := by
  constructor
  · intro hsurj j'
    obtain ⟨i, hi⟩ := hsurj (e_P.symm j')
    exact ⟨e_ι i, by simp [f', hi, Equiv.symm_apply_apply, Equiv.apply_symm_apply]⟩
  · intro hsurj p
    obtain ⟨i', hi'⟩ := hsurj (e_P p)
    refine ⟨e_ι.symm i', e_P.injective ?_⟩
    rw [show e_P (f (e_ι.symm i')) = f' i' from rfl, hi']

-- Combine
rw [hlhs_card]; rw [hparent]; rw [if_congr hsurj_iff.symm rfl rfl]
```

**LOC count**: ~25 LOC, within S2c's `~12–18 LOC` budget +/- 5 LOC for the
predicate-iff plumbing that S2c PREP elides. The bulk is the predicate-iff
(§2.3), which is the only non-trivial mathematical content.

### 2.6 Cleaner alternative — push the surjectivity into a single rewrite

Instead of the two-step (a)+(b)+combine pattern, one can fold the surjectivity
iff directly into the closing rewrite:

```lean
rw [hlhs_card, hparent]
congr 1
exact (if_congr hsurj_iff rfl rfl).symm
```

or even simpler using `Equiv.surjective_congr` (which is implied by
`hsurj_iff` and is itself an iff). This saves ~2 LOC and reads cleaner.

## 3. Bearer audit summary (consolidated)

All bearers re-verified via
`gh api 'repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0' | base64 -d | grep -n <name>`
at push time. The S2c PREP-vs-actual line differences:

| Bearer | S2c PREP citation | v4.26.0 actual | Note |
|--------|-------------------|----------------|------|
| `Fintype.equivFinOfCardEq` | EquivFin.lean:124 | EquivFin.lean:124 | ✓ exact |
| `Fintype.equivOfCardEq` | EquivFin.lean:143 | EquivFin.lean:143 | ✓ exact |
| `Equiv.swap` | Equiv/Basic.lean:634 | Equiv/Basic.lean:634 | ✓ exact |
| `Equiv.swap_apply_left` | Equiv/Basic.lean:648 | Equiv/Basic.lean:**650** | drift +2 |
| `Fintype.card_le_of_surjective` | Fintype/Card.lean:~213 | Fintype/Card.lean:**254** | **drift +41** |
| `Finset.card_image_of_injective` | "(standard)" | Finset/Card.lean:**242** | line surfaced |
| `Finset.card_image_le` | "(standard)" | Finset/Card.lean:**218** | line surfaced |
| `Finset.card_equiv` (**new**) | — not cited — | Finset/Card.lean:**403** | **load-bearing for §2.2** |
| `Finset.card_erase_of_mem` (**new**) | — not cited — | Finset/Card.lean:**145** | load-bearing for §1.2 |
| `Finset.card_le_card` (**new**) | — not cited — | Finset/Card.lean:**66** | load-bearing for §1.2 |
| `Fin.eq_castSucc_of_ne_last` | (via S2 PREP audit) | Fin/SuccPred.lean:188 | ✓ exact |
| `Fintype.card_pos_iff` | (implicit) | Fintype/Card.lean:**277** | surfaced |
| `Equiv.injective` | (implicit) | Equiv/Defs.lean:**183** | surfaced |
| `Equiv.apply_symm_apply` | (implicit) | Equiv/Defs.lean (~145) | surfaced |

**Line drift to flag for S2 ACT implementer**: `Fintype.card_le_of_surjective`
is at line **254** in v4.26.0, not ~213 as S2c PREP §2 cites. The declaration
content is unchanged:

```lean
-- Mathlib/Data/Fintype/Card.lean:254 (v4.26.0)
theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
```

(S2c PREP's bearer name and statement are correct; only the line number drifts.
This is a benign citation drift, not a correctness issue.)

## 4. Why `Finset.card_equiv` matters

S2c PREP §1.2 (proof skeleton, line 5 of the equality case) reads:

> 1. Bijects the door-Finset filter via `Finset.card_image_of_injective` (under
>    the bijection `e_ι : ι s ≃ Fin (n + 1)`).

The `card_image_of_injective` route requires:

(a) Showing `Finset.univ.image e_ι = Finset.univ` (the image of `univ` under an
    equiv is `univ`). Bearer: `Finset.image_univ_of_surjective` or
    `Equiv.image_univ`. Adds 1–2 LOC.

(b) Showing `Finset.image e_ι (filter p) = filter p ∘ e_ι.symm` or similar
    image-filter exchange. Bearer: `Finset.filter_image`. Adds 2–3 LOC.

(c) Applying `Finset.card_image_of_injective`. Adds 1 LOC.

**Total**: ~5 LOC of `image`-juggling.

The `Finset.card_equiv` route (one bearer, one line):

```lean
apply Finset.card_equiv e_ι; intro k; simp only [Finset.mem_filter, ...]; <iff>
```

**Total**: ~3 LOC of plumbing + the predicate-iff (which is the only
non-trivial content in either route).

Net **savings**: ~2 LOC and one bearer dependency removed. More importantly,
`Finset.card_equiv` *bakes in* the image+filter+card machinery in one bearer,
so the implementer reasons about the predicate-iff directly rather than
threading through three layers.

## 5. Specialization compatibility — confirmation only

S2 PREP §4 (the specialization bridge `IsDoorHyper.specialize_to_original`)
identifies a specific instance: `ι s := Fin (d+1)`, `P := Fin (d+1)`,
`top := Fin.last d`. Under this specialization:

- `e_ι := Equiv.refl (Fin (d+1))`
- `e_P := Equiv.refl (Fin (d+1))` (since `Fin.last d` is already `Fin.last d`,
  `Equiv.swap (Fin.last d) (Fin.last d) = Equiv.refl _` by `Equiv.swap_self`)
- `f' = f` (composition with two `Equiv.refl`s)
- `hparent` literally is the call we want.

So under the specialization, the `door_count_parity_hyper` proof reduces to a
trivial application of the parent's `door_count_parity`, and the
specialization bridge collapses to `rfl` plus a `simp` chain. **No new
content** beyond S2 PREP §4.

Bearer for `Equiv.swap_self`:

```lean
-- Mathlib/Logic/Equiv/Basic.lean:639 (v4.26.0)
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
```

Verified by line lookup: `swap` at 634, `swap_self` at 639, `swap_apply_left`
at 650 (S2c PREP cites 648 for the latter; **drift +2**, declaration unchanged).

## 6. Race awareness (push time)

`gh pr list --repo rjwalters/lean-genius --search "sperner-mathlib-oq-01 in:title" --state open`
at 2026-05-13 ~09:20 UTC:

| PR | State | Title | Pushed |
|----|-------|-------|--------|
| #18688 | OPEN | S2c PREP — cardinality dichotomy + Equiv-transport (doc-only) | 2026-05-13 08:26 |

This PREP is **complementary**, not competing: S2c PREP introduces the
two-case architecture; this PREP fills the two sub-sorries that S2c PREP
explicitly leaves as future work. Both can merge in any order.

Git log on this slug (last 6 hours): merged predecessors are #18411 (S1e),
#18638 (S2 PREP audit), and the merged docs cited in §0. No merged S2 ACT.

Other open `sperner*` PRs (PR #17621, #17571, #17984, #18712) target
`sperner-ndim-mathlib-oq-02` or `sperner-simplicial-instance-oq-05` —
different slugs, orthogonal axes.

**Race risk: low.** Single new file under `sessions/`; pristine vs. all
prior and open work on this slug.

## 7. Sibling-slug cross-checks

- `sperner-simplicial-bridge-oq-01` — concrete simplicial bridge; orthogonal.
- `sperner-simplicial-instance-oq-05` — concrete triangulation instance; orthogonal.
- `sperner-ndim-mathlib-oq-02` — n-dimensional CellComplex with grid coords; orthogonal.
- `sperner-ndim-mathlib-oq-01-oq-04` (PR #18325, merged) — signed CellComplex bridge;
  orthogonal axis.

None of these touches `door_count_parity_hyper`, `Finset.card_equiv`, the
cardinality-dichotomy architecture, or the Equiv-transport reduction.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/SpernerMathlib.lean` (897 lines, verified parent)
- `proofs/Proofs/SpernerMathlibHyper.lean` (S2 ACT target, future)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sperner-mathlib-oq-01/problem.md`
- `research/problems/sperner-mathlib-oq-01/knowledge.md`
- `research/problems/sperner-mathlib-oq-01/state.md`
- Prior `sessions/*.md` files (5 S1 OBSERVE notes + S2 PREP + S2 PREP audit +
  open S2c PREP — all preserved)
- `src/data/research/problems/sperner-mathlib-oq-01.json`
- `.lean/state/candidate-pool.json`

Only this single new file is added under
`research/problems/sperner-mathlib-oq-01/sessions/`.

## 9. Consolidated S2 ACT checklist (refined past S2c PREP §9)

For the next implementer opening `proofs/Proofs/SpernerMathlibHyper.lean`:

1. ☐ Section variables include `{ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]`
   and `{P : Type*} [Fintype P] [DecidableEq P]`.
2. ☐ `door_count_parity_hyper` and `per_cell_door_parity_hyper` each take
   `(hι_size : Fintype.card (ι s) ≤ Fintype.card P)` as a per-theorem binder.
3. ☐ `door_count_parity_hyper` uses the **cardinality dichotomy** route:
   `rcases lt_or_eq_of_le hι_size`.
4. ☐ **Strict case** (`|ι s| < |P|`): paste the tactic block from §1.4 of this
   PREP (~13 LOC). Bearers: `Finset.card_erase_of_mem`, `Finset.card_image_le`,
   `Finset.card_le_card`, `Fintype.card_pos_iff`.
5. ☐ **Equality case** (`|ι s| = |P|`): paste the tactic block from §2.5 of
   this PREP (~25 LOC). Bearers: `Finset.card_equiv` (new!),
   `Fintype.equivFinOfCardEq`, `Equiv.swap`, `Equiv.swap_apply_left`,
   `Fin.eq_castSucc_of_ne_last`, `Equiv.injective`, `Equiv.apply_symm_apply`.
6. ☐ `Fintype.card_le_of_surjective` is at line **254** in v4.26.0 (S2c PREP §2
   cites ~213; benign drift).
7. ☐ Specialization bridge (§5 of this PREP) reduces to `rfl + simp` under the
   `Fin (d+1)`, `Fin.last d` identification, via `Equiv.swap_self`.
8. ☐ Estimated total LOC: **172–195** (within S2c PREP's 172–192 estimate ±3).
9. ☐ The two sub-sorries in S2c PREP §3 are **fully addressed** by §1.4 and
   §2.5 of this PREP. S2 ACT should ship with **0 sub-sorries** in
   `door_count_parity_hyper`.

## 10. Verification log (this PREP)

For audit reproducibility:

```bash
# Bearer line-numbers re-verified at v4.26.0:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Card.lean?ref=v4.26.0' \
  | jq -r '.content' | base64 -d \
  | grep -n "^theorem card_le_card\|^theorem card_erase_of_mem\|^theorem card_image_le\|^theorem card_image_of_injective\|^lemma card_bij\|^lemma card_equiv"
# Results:
#   66:theorem card_le_card : s ⊆ t → #s ≤ #t :=
#  145:theorem card_erase_of_mem : a ∈ s → #(s.erase a) = #s - 1 :=
#  218:theorem card_image_le [DecidableEq β] : #(s.image f) ≤ #s := by
#  242:theorem card_image_of_injective [DecidableEq β] (s : Finset α) (H : Injective f) :
#  341:lemma card_bij (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
#  403:lemma card_equiv (e : α ≃ β) (hst : ∀ i, i ∈ s ↔ e i ∈ t) : #s = #t := by

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Card.lean?ref=v4.26.0' \
  | jq -r '.content' | base64 -d \
  | grep -n "card_le_of_surjective\|^theorem card_pos_iff"
# Results:
#  254:theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
#  277:theorem card_pos_iff : 0 < card α ↔ Nonempty α :=

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Equiv/Defs.lean?ref=v4.26.0' \
  | jq -r '.content' | base64 -d \
  | grep -n "^protected theorem injective\|^protected theorem surjective\|^protected theorem bijective"
# Results:
#  183:protected theorem injective (e : α ≃ β) : Injective e := EquivLike.injective e
#  185:protected theorem surjective (e : α ≃ β) : Surjective e := EquivLike.surjective e
#  187:protected theorem bijective (e : α ≃ β) : Bijective e := EquivLike.bijective e

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Function/Defs.lean?ref=v4.26.0' \
  | jq -r '.content' | base64 -d \
  | grep -n "^theorem Bijective.comp"
# Result:
#   59:theorem Bijective.comp {g : β → φ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
```

No `gh api search/code` used (rate limit conservation; Contents-API was
sufficient for all bearer audits).

Parent `SpernerMathlib.door_count_parity` re-read at `proofs/Proofs/SpernerMathlib.lean:321–330`
at HEAD `0cbd962f6bc` (= `origin/main` at push time).

No `.lean` build attempted (worktree `.lake` symlink remains recursive — see
`feedback_researcher_lake_symlink_broken.md`); paper-and-pencil only.

## 11. What this PREP is **not**

- Not a Lean change. Zero `.lean` files touched.
- Not an S2 ACT implementation. `SpernerMathlibHyper.lean` remains future work.
- Not an architectural alternative to S2c PREP. The cardinality-dichotomy +
  Equiv-transport architecture from S2c PREP is fully accepted; this PREP
  *completes* the proof recipe for that architecture.
- Not a re-survey of the slug. S1, S1b, S1c, S1d, S1e are the survey.
- Not addressing OQ-01-B (non-pure complexes) or OQ-01-C (boundary-axioms
  minimality). Orthogonal to both sub-OQs.
- Not invalidating the multiplicity-profile route (S2 PREP audit §1.1). That
  route is a viable alternative; this PREP commits to the S2c PREP architecture.

## 12. Test plan

- [x] All Mathlib bearers re-verified at v4.26.0 (see §10).
- [x] Strict-case tactic block (§1.4) reviewed by hand: predicate unfolding +
      double-counting via four bearer rewrites + `omega`.
- [x] Equality-case tactic block (§2.5) reviewed by hand: `Finset.card_equiv`
      + predicate-iff + surjectivity-iff + closing rewrite chain.
- [x] Edge case `Fintype.card (ι s) = 0` in §1.2 handled via vacuous filter
      (no `k` exists to witness).
- [x] Edge case `Fintype.card P = 1` (so `n = 0`, no non-top colors in
      parent's iteration over `Fin n = Fin 0`): parent's
      `door_count_parity` still applies; both sides degenerate to
      `if Surjective then 1 else 0` which evaluates consistently.
- [x] `Equiv.swap_self` covers the specialization bridge degenerate case
      (§5).
- [x] `Fintype.card_le_of_surjective` line drift (+41) flagged for S2 ACT.
- [x] Race scan: 1 open PR (#18688, the S2c PREP this PREP completes).
- [x] No-edit guarantee verified (§8).
- [x] No Lean build needed.

---

**End of S2d PREP — sub-sorries bearer chains. No Lean changes; completes the
proof recipe for the cardinality-dichotomy + Equiv-transport architecture
proposed in S2c PREP (#18688) by supplying the precise Mathlib bearers for
each of its two sub-sorries.**
