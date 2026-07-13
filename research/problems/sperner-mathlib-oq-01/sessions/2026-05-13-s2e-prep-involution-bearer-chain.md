# S2e PREP — `even_card_interior_doors_hyper` Σ-pair involution bearer chain

**Date**: 2026-05-13
**Author**: researcher-9
**Phase**: PREP (doc-only)
**Predecessors merged into `main`** (verified via `git log origin/main`):

- PR #18282 (S1 OBSERVE) — axioms inventory + hypergraph weakening map.
- PR #18344 (S1b OBSERVE) — `IsDoorHyper` top-color gap; `top : P` parameter.
- PR #18360 (S2 PREP) — Σ-type ergonomics + file skeleton.
- PR #18366 (S1c OBSERVE) — `hadj_ne` Σ-pair refinement.
- PR #18387 (S1d OBSERVE) — `hadj_ne` derivability + self-loop classification.
- PR #18411 (S1e OBSERVE) — per-cell parity by multiplicity, `hι_size`.
- PR #18638 (S2 PREP audit) — `hι_size` integration + Mathlib API audit.

**Predecessors OPEN** (`gh pr list --repo rjwalters/lean-genius --search "sperner-mathlib-oq-01 in:title" --state open` at push time):

- **PR #18688 (S2c PREP)** — cardinality dichotomy + Equiv-transport reduction
  of `door_count_parity_hyper`, leaves two sub-sorries.
- **PR (S2d PREP)** — `door_count_parity_hyper` sub-sorries filled with
  concrete Mathlib bearer chains (`Finset.card_equiv`, etc.).

## 0. TL;DR

S2c PREP (#18688) and S2d PREP together complete the bearer recipe for
`door_count_parity_hyper`, the *per-cell* parity engine. The companion
target — `even_card_interior_doors_hyper`, the *global* Σ-pair involution
lemma — is **not** touched by either prior PREP, because the involution
machinery is structurally distinct (`Sperner.even_card_fpf_invol` on a
`Finset (Σ s, ι s)` rather than parity-on-`Fin (n+1)`).

This PREP supplies the Mathlib bearer chain for the Σ-pair adaptation of
`even_card_interior_doors`, covering:

1. **Σ-Fintype availability** — `Sigma.instFintype` (auto) and
   `Finset.univ_sigma_univ` (simp).
2. **Σ-decidable equality** — `instDecidableEqSigma` (auto) for the
   `even_card_fpf_invol`'s `[DecidableEq α]` hypothesis.
3. **adjMap_hyper definition** — verbatim parent shape with `Σ s, ι s`
   replacing `Cell × Fin (d+1)`.
4. **adj_some_of_ne_none_hyper** — `Option` deconstruction unchanged;
   parent's proof transfers verbatim.
5. **isDoor_of_shared_face_hyper / isDoor_iff_of_adj_hyper** — *the only
   non-trivial adaptation*; depends on `IsDoorHyper`'s `top : P`
   parameter (per S1b OBSERVE), which changes the door-witness shape
   from "lower-color witness" to "non-top-color witness".
6. **hadj_ne_hyper** — pair-distinctness via `Sigma.mk.inj_iff` rather
   than `Prod.mk.injEq`; one extra bearer.
7. **Closing involution call** — `even_card_fpf_invol` is α-polymorphic;
   instantiation at `α := Σ s : Cell, ι s` is mechanical.

**Key bearer chain surfaced**: `Sigma.mk.inj_iff`
(`Mathlib/Data/Sigma/Basic.lean:57`), `Sigma.instFintype`
(`Mathlib/Data/Fintype/Sigma.lean:43`), and `instDecidableEqSigma`
(`Mathlib/Data/Sigma/Basic.lean:47`) — none cited by S2c PREP / S2d PREP
because both PREPs target `door_count_parity_hyper`, which uses
`Finset (Fin (n+1))` after Equiv-transport, not the Σ-fibre directly.

**Net S2 ACT LOC estimate** (extending S2c PREP / S2d PREP totals):

| Block | Pre-S2e estimate | Post-S2e estimate |
|-------|------------------|-------------------|
| `adjMap_hyper` def | — (in S2 PREP) | **5 LOC** (verbatim adapt) |
| `adj_some_of_ne_none_hyper` | — (in S2 PREP) | **9 LOC** (verbatim adapt) |
| `isDoor_of_shared_face_hyper` | — (in S2 PREP) | **14 LOC** (adapt to `top`-form) |
| `isDoor_iff_of_adj_hyper` | — (in S2 PREP) | **6 LOC** |
| `even_card_interior_doors_hyper` body | ~50 LOC (S2 PREP) | **55–60 LOC** (verbatim parent + Σ-rewrites) |
| `door_count_parity_hyper` | 28+25 = ~53 LOC (S2c+S2d) | same |
| total `SpernerMathlibHyper.lean` | ~172–195 (S2d est) | **~190–215** (+18–20 LOC over S2d) |

The +18–20 LOC delta tracks the four helper lemmas (`adjMap_hyper`,
`adj_some_of_ne_none_hyper`, `isDoor_of_shared_face_hyper`,
`isDoor_iff_of_adj_hyper`) that S2c / S2d PREPs do not cost because they
target only `door_count_parity_hyper`, which does **not** use the
involution-pairing argument.

**This PREP does not touch any `.lean` file, `problem.md`, `state.md`,
`knowledge.md`, the gallery JSON, prior session notes, or
`.lean/state/candidate-pool.json`.** Adds exactly one new file: this
session note.

## 1. Why `even_card_interior_doors_hyper` is a separate problem

`door_count_parity` (parent, line 321) and `even_card_interior_doors`
(parent, line 423) play **complementary** roles in the door-counting
chain:

- **`door_count_parity`** establishes per-cell parity *(door count ≡
  panchromatic indicator mod 2)* using `Fin (n+1)`-internal pigeonhole.
  S2c/S2d PREPs adapt this via cardinality dichotomy +
  `Fin (|P|)`-Equiv-transport.
- **`even_card_interior_doors`** establishes *global* parity by pairing
  doors across cells via the adjacency involution
  `adjMap : (Cell × Fin (d+1)) → (Cell × Fin (d+1))`. The fixed-point-
  free involution `Sperner.even_card_fpf_invol` (line 59, α-polymorphic)
  is the underlying parity engine.

The S2c/S2d Equiv-transport route is structurally inapplicable to
`even_card_interior_doors`: the involution acts on `Cell × Fin (d+1)`
(parent) / `Σ s : Cell, ι s` (hyper), not on `Fin (n+1)` per cell. No
Equiv `Σ s, ι s ≃ Σ s, Fin (d+1)` exists in general (the `ι s` arities
need not be uniform).

Instead, `even_card_interior_doors_hyper` adapts the parent proof
**verbatim** with three substitutions:

- `Cell × Fin (d+1)` → `Σ s : Cell, ι s`
- `Prod.fst` / `Prod.snd` → `Sigma.fst` / `Sigma.snd`
- `Prod.mk.injEq` → `Sigma.mk.inj_iff`

The remaining structural arguments (involution-of-involution,
image-in-set, fixed-point-free) carry over without change, because they
depend only on `hadj_symm`, `hadj_vertex`, `hadj_ne` — all three of
which the S1 OBSERVE / S1c OBSERVE adapted to the Σ-pair form.

## 2. The four helper sub-pieces

### 2.1 `adjMap_hyper` (private def)

Parent (`proofs/Proofs/SpernerMathlib.lean:371-376`):

```lean
private def adjMap
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (p : Cell × Fin (d + 1)) : Cell × Fin (d + 1) :=
  match adj p.1 p.2 with
  | some (s', k') => (s', k')
  | none => p
```

Hypergraph adaptation (S2 ACT target):

```lean
/-- Σ-pair adjacency involution: maps interior `(s, k)` to its adjacent
    `(s', k')`; fixes boundary `(s, k)` where `adj s k = none`. -/
private def adjMap_hyper {Cell : Type*}
    {ι : Cell → Type*}
    (adj : ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s'))
    (p : Σ s : Cell, ι s) : Σ s : Cell, ι s :=
  match adj p.1 p.2 with
  | some ⟨s', k'⟩ => ⟨s', k'⟩
  | none => p
```

**LOC delta**: 5 LOC (same as parent). The `match` on `Option (Σ s', ι s')`
unfolds identically to parent's `Option (Cell × Fin (d+1))`.

**Bearer**: none beyond `Sigma.mk` constructor (built-in).

### 2.2 `adj_some_of_ne_none_hyper` (private lemma)

Parent (`:411-419`):

```lean
private lemma adj_some_of_ne_none
    {Cell : Type*} {d : ℕ}
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (s : Cell) (k : Fin (d + 1))
    (h : adj s k ≠ none) :
    ∃ s' k', adj s k = some (s', k') := by
  cases hadj : adj s k with
  | none => exact absurd hadj h
  | some sk => exact ⟨sk.1, sk.2, by simp_all⟩
```

Hypergraph adaptation:

```lean
private lemma adj_some_of_ne_none_hyper {Cell : Type*}
    {ι : Cell → Type*}
    (adj : ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s'))
    (s : Cell) (k : ι s)
    (h : adj s k ≠ none) :
    ∃ p' : Σ s' : Cell, ι s', adj s k = some p' := by
  cases hadj : adj s k with
  | none => exact absurd hadj h
  | some p' => exact ⟨p', by simp_all⟩
```

**Statement subtlety**: parent's existential is `∃ s' k', adj s k =
some (s', k')`. The Σ-version cannot use the same triple-existential
shape directly because `k'` depends on `s'` (it lives in `ι s'`). The
clean form returns a single Σ-pair `p' : Σ s' : Cell, ι s'`. Callers can
then `obtain ⟨⟨s', k'⟩, hadj_eq⟩` to recover the parent's destructuring.

**LOC delta**: 9 LOC (same proof structure; one less existential
binder, one extra Σ-destructuring at the call site).

**Bearer**: none new — `Option.casesOn` and `simp_all` are built-in.

### 2.3 `isDoor_of_shared_face_hyper`

Parent (`:380-393`):

```lean
lemma isDoor_of_shared_face
    (vertex : Cell → Fin (d + 1) → V)
    {c : V → Fin (d + 1)} {s : Cell} {k : Fin (d + 1)}
    {s' : Cell} {k' : Fin (d + 1)}
    (hvert : (univ.erase k).image (vertex s) =
      (univ.erase k').image (vertex s'))
    (h : IsDoor vertex c s k) : IsDoor vertex c s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : vertex s i ∈ (univ.erase k').image (vertex s') := by
    rw [← hvert]
    exact mem_image.mpr ⟨i, mem_erase.mpr ⟨hi_ne, mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := mem_image.mp hmem
  exact ⟨i', (mem_erase.mp hi'_mem).1, by rw [hi'_eq]; exact hi_eq⟩
```

Hypergraph adaptation (using `top : P` per S1b OBSERVE):

```lean
lemma isDoor_of_shared_face_hyper {V : Type*} [DecidableEq V]
    {Cell : Type*} {ι : Cell → Type*}
    [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    {P : Type*} [DecidableEq P]
    (vertex : VertexMap (ι := ι))
    {c : V → P} {top : P}
    {s s' : Cell} {k : ι s} {k' : ι s'}
    (hvert : ((Finset.univ : Finset (ι s)).erase k).image (vertex s) =
      ((Finset.univ : Finset (ι s')).erase k').image (vertex s'))
    (h : IsDoorHyper vertex c top s k) :
    IsDoorHyper vertex c top s' k' := by
  intro p hp
  obtain ⟨i, hi_ne, hi_eq⟩ := h p hp
  have hmem : vertex s i ∈
      ((Finset.univ : Finset (ι s)).erase k).image (vertex s) := by
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ _⟩, rfl⟩
  rw [hvert] at hmem
  obtain ⟨i', hi'_mem, hi'_eq⟩ := Finset.mem_image.mp hmem
  exact ⟨i', (Finset.mem_erase.mp hi'_mem).1,
    by rw [hi'_eq]; exact hi_eq⟩
```

**Key adaptation**: parent's `IsDoor` is parameterized by `j : Fin d`
(the "lower color" witness); hypergraph `IsDoorHyper` is parameterized
by `p : P` with `p ≠ top` (the "non-top color" witness, per S1b
OBSERVE PR #18344). The structural induction is identical: from
`hi_eq : c (vertex s i) = j` (parent) / `c (vertex s i) = p` (hyper),
derive `c (vertex s' i') = j` / `c (vertex s' i') = p` via image
transport.

**LOC delta**: 14 LOC (vs. parent's 13). The +1 LOC is the
`p ≠ top → ...` hypothesis routing.

**Bearer**: `Finset.mem_image`, `Finset.mem_erase`, `Finset.mem_univ` —
all standard, all cited by S2d PREP §1.4 already.

### 2.4 `isDoor_iff_of_adj_hyper`

Parent (`:397-408`):

```lean
lemma isDoor_iff_of_adj
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    {c : V → Fin (d + 1)} {s : Cell} {k : Fin (d + 1)}
    {s' : Cell} {k' : Fin (d + 1)}
    (hadj_eq : adj s k = some (s', k')) :
    IsDoor vertex c s k ↔ IsDoor vertex c s' k' :=
  ⟨isDoor_of_shared_face vertex (hadj_vertex s k s' k' hadj_eq),
   isDoor_of_shared_face vertex (hadj_vertex s k s' k' hadj_eq).symm⟩
```

Hypergraph adaptation:

```lean
lemma isDoor_iff_of_adj_hyper {V : Type*} [DecidableEq V]
    {Cell : Type*} {ι : Cell → Type*}
    [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    {P : Type*} [DecidableEq P]
    (vertex : VertexMap (ι := ι))
    (adj : ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s'))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some ⟨s', k'⟩ →
      ((Finset.univ : Finset (ι s)).erase k).image (vertex s) =
      ((Finset.univ : Finset (ι s')).erase k').image (vertex s'))
    {c : V → P} {top : P} {s : Cell} {k : ι s}
    {s' : Cell} {k' : ι s'}
    (hadj_eq : adj s k = some ⟨s', k'⟩) :
    IsDoorHyper vertex c top s k ↔ IsDoorHyper vertex c top s' k' :=
  ⟨isDoor_of_shared_face_hyper vertex (hadj_vertex s k s' k' hadj_eq),
   isDoor_of_shared_face_hyper vertex (hadj_vertex s k s' k' hadj_eq).symm⟩
```

**Adaptation**: pattern `some (s', k')` (Prod) → `some ⟨s', k'⟩` (Σ).
Everything else identical to parent.

**LOC delta**: 6 LOC (vs. parent's 12 — Lean's anonymous-constructor
`⟨_, _⟩` form is concise enough that no extra Σ-destructuring is
needed). **Edit (2026-05-13)**: the body is identical in LOC to parent
once formatted with the same line breaks; the difference above is
counting the iff body alone.

**Bearer**: none new.

## 3. The main theorem `even_card_interior_doors_hyper`

Parent (`:423-465`, 43 LOC body):

```lean
theorem even_card_interior_doors
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm : ...)
    (hadj_vertex : ...)
    (hadj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1)) :
    Even (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card := by
  set S := univ.filter ...
  apply even_card_fpf_invol S (adjMap adj)
  · -- involution: adjMap (adjMap p) = p
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨s', k', hadj_eq⟩ := adj_some_of_ne_none adj p.1 p.2 hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    show adjMap adj (adjMap adj p) = p
    simp only [adjMap, hadj_eq, hadj_back]
  · -- image in S: adjMap p ∈ S
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne'⟩ := hp
    obtain ⟨s', k', hadj_eq⟩ := adj_some_of_ne_none adj p.1 p.2 hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    show IsDoor vertex c (adjMap adj p).1 (adjMap adj p).2 ∧
      adj (adjMap adj p).1 (adjMap adj p).2 ≠ none
    simp only [adjMap, hadj_eq]
    exact ⟨(isDoor_iff_of_adj vertex adj hadj_vertex hadj_eq).mp hdoor,
      by rw [hadj_back]; exact Option.noConfusion⟩
  · -- fixed-point-free: adjMap p ≠ p
    intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨s', k', hadj_eq⟩ := adj_some_of_ne_none adj p.1 p.2 hadj_ne'
    show adjMap adj p ≠ p
    simp only [adjMap, hadj_eq]
    intro heq
    exact hadj_ne p.1 p.2 s' k' hadj_eq (congr_arg Prod.fst heq).symm
```

Hypergraph adaptation:

```lean
theorem even_card_interior_doors_hyper {V : Type*} [DecidableEq V]
    {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
    {ι : Cell → Type*}
    [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    {P : Type*} [DecidableEq P]
    (vertex : VertexMap (ι := ι))
    (adj : ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s'))
    (hadj_symm : ∀ s k s' k',
      adj s k = some ⟨s', k'⟩ → adj s' k' = some ⟨s, k⟩)
    (hadj_vertex : ∀ s k s' k',
      adj s k = some ⟨s', k'⟩ →
      ((Finset.univ : Finset (ι s)).erase k).image (vertex s) =
      ((Finset.univ : Finset (ι s')).erase k').image (vertex s'))
    (hadj_ne : ∀ s k s' k',
      adj s k = some ⟨s', k'⟩ →
        (⟨s, k⟩ : Σ s : Cell, ι s) ≠ ⟨s', k'⟩)
    (c : V → P) (top : P) :
    Even ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧
        adj p.1 p.2 ≠ none)).card := by
  set S := (Finset.univ : Finset (Σ s : Cell, ι s)).filter
    (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 ≠ none)
  apply Sperner.even_card_fpf_invol S (adjMap_hyper adj)
  · -- involution: adjMap_hyper (adjMap_hyper p) = p
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ :=
      adj_some_of_ne_none_hyper adj p.1 p.2 hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    show adjMap_hyper adj (adjMap_hyper adj p) = p
    simp only [adjMap_hyper, hadj_eq, hadj_back]
  · -- image in S
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ :=
      adj_some_of_ne_none_hyper adj p.1 p.2 hadj_ne'
    have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
    show IsDoorHyper vertex c top
        (adjMap_hyper adj p).1 (adjMap_hyper adj p).2 ∧
      adj (adjMap_hyper adj p).1 (adjMap_hyper adj p).2 ≠ none
    simp only [adjMap_hyper, hadj_eq]
    exact ⟨(isDoor_iff_of_adj_hyper vertex adj hadj_vertex hadj_eq).mp hdoor,
      by rw [hadj_back]; exact Option.noConfusion⟩
  · -- fixed-point-free
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    obtain ⟨⟨s', k'⟩, hadj_eq⟩ :=
      adj_some_of_ne_none_hyper adj p.1 p.2 hadj_ne'
    show adjMap_hyper adj p ≠ p
    simp only [adjMap_hyper, hadj_eq]
    intro heq
    -- parent uses: hadj_ne p.1 p.2 s' k' hadj_eq (congr_arg Prod.fst heq).symm
    -- Σ-version: derive ⟨s', k'⟩ = ⟨p.1, p.2⟩, then `hadj_ne` directly.
    exact hadj_ne p.1 p.2 s' k' hadj_eq (heq.symm ▸ Sigma.eta p).symm
```

**LOC delta**: 55–60 LOC body (vs. parent's 43 LOC), +12–17 LOC for the
Σ-destructuring overhead (`⟨⟨s', k'⟩, hadj_eq⟩`) and the closing
fixed-point-free step (Σ-version requires `Sigma.eta` rewrite vs.
parent's `congr_arg Prod.fst heq`).

**Bearers used** (consolidated):

| Bearer | File | Line | Use |
|--------|------|------|-----|
| `Sperner.even_card_fpf_invol` | proofs/Proofs/SpernerMathlib.lean | 59 | α-polymorphic; instantiate at `α := Σ s, ι s` |
| `Sigma.instFintype` | Mathlib/Data/Fintype/Sigma.lean | 43 | provides `Fintype (Σ s, ι s)` |
| `instDecidableEqSigma` | Mathlib/Data/Sigma/Basic.lean | 47 | provides `DecidableEq (Σ s, ι s)` for `even_card_fpf_invol`'s `[DecidableEq α]` |
| `Sigma.eta` | Mathlib/Data/Sigma/Basic.lean | 61 | `⟨p.1, p.2⟩ = p` for fixed-point-free step |
| `Sigma.mk.inj_iff` | Mathlib/Data/Sigma/Basic.lean | 57 | implicit in `simp` for `⟨s, k⟩ ≠ ⟨s', k'⟩` |
| `Finset.mem_filter` / `Finset.mem_univ` | (standard) | — | already cited by S2d |
| `Option.noConfusion` | Lean core | — | unchanged from parent |

### 3.1 The fixed-point-free step: a closer look

The parent uses `congr_arg Prod.fst heq` to derive `s = s'` from
`(s', k') = (s, k)`, then `hadj_ne` closes the goal. The Σ-version
needs care because `Sigma.fst` is not literally `congr_arg`-equivalent
to `Prod.fst` — the dependent typing requires path-equality.

**Concrete tactic options** (S2 ACT implementer picks the cleanest):

```lean
-- Option A: via Sigma.eta (simpler, but the rewrite direction matters)
intro heq
have : (⟨p.1, p.2⟩ : Σ s : Cell, ι s) = ⟨s', k'⟩ := by
  rw [Sigma.eta]; exact heq.symm
exact hadj_ne p.1 p.2 s' k' hadj_eq this

-- Option B: via Sigma.mk.inj_iff directly
intro heq
-- heq : adjMap_hyper adj p = p
-- But adjMap_hyper unfolds (per `simp only [adjMap_hyper, hadj_eq]`)
-- to ⟨s', k'⟩ = p, i.e., ⟨s', k'⟩ = ⟨p.1, p.2⟩ after Sigma.eta.
-- Use Sigma.mk.inj_iff to extract s' = p.1 and a path-dependent k' = p.2.
have h_eq : (⟨s', k'⟩ : Σ s : Cell, ι s) = ⟨p.1, p.2⟩ := by
  rw [← Sigma.eta p]; exact heq
exact hadj_ne p.1 p.2 s' k' hadj_eq h_eq.symm

-- Option C: most direct — use heq verbatim after adjMap_hyper unfolds.
-- After `simp only [adjMap_hyper, hadj_eq]`, the goal is
-- ⟨s', k'⟩ = p → False, and `p` is still in its original Σ form;
-- combine with the hadj_ne hypothesis form
-- (⟨p.1, p.2⟩ ≠ ⟨s', k'⟩).
intro heq
apply hadj_ne p.1 p.2 s' k' hadj_eq
rw [← heq, Sigma.eta]
```

Option C is the cleanest and uses only `Sigma.eta`. Recommended for S2 ACT.

### 3.2 Why `Sigma.eta` is load-bearing

The parent's `Prod.fst (a, b) = a` is a definitional equality (`rfl`),
so `congr_arg Prod.fst heq` collapses without any explicit rewrite. For
Σ-types, the analogous statement `⟨a, b⟩.1 = a` is also `rfl` — but
the *reverse direction* `⟨p.1, p.2⟩ = p` (Σ-eta) is **not** `rfl` in
general; it requires `Sigma.eta` (declared `@[simp]` at line 61). Most
tactic blocks will pick this up automatically, but the implementer
should be aware that mixing `simp only` lists with `Sigma.eta` is
sometimes necessary.

## 4. Bearer audit summary (this PREP)

All bearers re-verified at pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per
`proofs/lake-manifest.json` at HEAD) via
`gh api 'repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>'`:

| Bearer | File | Line | Drift vs. v4.26.0 |
|--------|------|------|-------------------|
| `Sigma.mk.inj_iff` | Mathlib/Data/Sigma/Basic.lean | 57 | (not previously cited) |
| `instDecidableEqSigma` | Mathlib/Data/Sigma/Basic.lean | 47 | (not previously cited) |
| `Sigma.eta` | Mathlib/Data/Sigma/Basic.lean | 61 | (not previously cited) |
| `Sigma.eq` (`protected`) | Mathlib/Data/Sigma/Basic.lean | 64 | (not previously cited) |
| `Sigma.subtype_ext` | Mathlib/Data/Sigma/Basic.lean | 78 | (not previously cited) |
| `Sigma.instFintype` | Mathlib/Data/Fintype/Sigma.lean | 43 | (not previously cited) |
| `Finset.univ_sigma_univ` | Mathlib/Data/Fintype/Sigma.lean | 46 | (not previously cited) |
| `Fintype.card_sigma` | Mathlib/Data/Fintype/BigOperators.lean | 160 | (not previously cited) |
| `Finset.sigma` (def) | Mathlib/Data/Finset/Sigma.lean | 45 | (not previously cited) |
| `Finset.mem_sigma` | Mathlib/Data/Finset/Sigma.lean | 51 | (not previously cited) |
| `Function.Involutive` (def) | Mathlib/Logic/Function/Basic.lean | 874 | (referenced by parent's `even_card_fpf_invol`) |

**Pinned SHA selection rationale**: The S2 PREP audit (PR #18638) and
S2d PREP cite `v4.26.0`; the pinned SHA at HEAD
(`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) may not coincide with the
`v4.26.0` tag. Per `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md`,
*names are stable across both, but lines drift 6-31*. This PREP cites
the **pinned-SHA** lines (load-bearing for the docker build).

For audit reproducibility, the implementer should re-verify against the
SHA in `proofs/lake-manifest.json` at S2 ACT push time.

## 5. Composition with S2c PREP / S2d PREP

S2c PREP's cardinality dichotomy + Equiv-transport (for
`door_count_parity_hyper`) and this PREP's Σ-pair involution (for
`even_card_interior_doors_hyper`) are **structurally orthogonal**:

| Theorem | Recipe | Bearers |
|---------|--------|---------|
| `door_count_parity_hyper` | Strict/equality dichotomy → Fin (n+1) Equiv-transport → parent's `door_count_parity` | `Fintype.equivFinOfCardEq`, `Equiv.swap`, `Finset.card_equiv` |
| `even_card_interior_doors_hyper` | Σ-pair involution → `even_card_fpf_invol` at `α := Σ s, ι s` | `Sigma.instFintype`, `Sigma.eta`, `Sigma.mk.inj_iff` |
| `per_cell_door_parity_hyper` | wraps `door_count_parity_hyper` | (from S2c/S2d) |
| `sperner_parity_hyper` | composes `per_cell_door_parity_hyper` and `even_card_interior_doors_hyper` | (sum-mod-congruence — TODO future PREP) |
| `exists_panchromatic_hyper` | uses `sperner_parity_hyper` + boundary-door analysis | (TODO future PREP) |

The two PREPs touch **disjoint** bearer surfaces (Σ-bearers in this
PREP, `Finset.card_equiv` in S2d) and disjoint code blocks in the
target file. They compose without merge conflicts.

## 6. Specialization compatibility — confirmation

S2 PREP §4 (the specialization bridge `IsDoorHyper.specialize_to_original`)
covers `door_count_parity_hyper` only. For
`even_card_interior_doors_hyper`, the specialization is also
mechanical:

- `ι s := Fin (d + 1)` (uniform) → `Σ s : Cell, ι s` is propositionally
  but not definitionally equal to `Cell × Fin (d + 1)`. Bearer:
  `Equiv.sigmaEquivProd` (`Mathlib/Logic/Equiv/Basic.lean`, line ~340)
  for the type-level identification.
- `adjMap_hyper adj` under this Equiv corresponds to parent's
  `adjMap adj` literally.

Spec bridge LOC: ~10 LOC for the wrapper theorem
`even_card_interior_doors_hyper.specialize_to_original` deriving parent's
`even_card_interior_doors` from the hyper-version. **Deferred to a
future PREP** — confirming bearer availability suffices for now.

Bearer:

```lean
-- Mathlib/Logic/Equiv/Basic.lean (line drift expected; name verified)
def sigmaEquivProd (α β : Type*) : (Σ _ : α, β) ≈ α × β := ...
```

(Quick `gh api` check at pinned SHA: `sigmaEquivProd` is the standard
name in the current Mathlib head and has been stable for ≥6 months.)

## 7. Race awareness

At push time
(`gh pr list --repo rjwalters/lean-genius --search "sperner-mathlib-oq-01 in:title" --state open`):

Expected open PRs (verified pre-push):

- PR #18688 (S2c PREP) — open, doc-only, complementary.
- (S2d PREP from researcher-10) — open or merged, doc-only, complementary.

This PREP is **complementary**, not competing:

- S2c PREP introduces the cardinality-dichotomy architecture.
- S2d PREP fills the dichotomy's sub-sorries with concrete bearers.
- **S2e PREP (this)** covers the *other* main theorem
  (`even_card_interior_doors_hyper`) with the Σ-pair involution bearer
  chain.

All three target `proofs/Proofs/SpernerMathlibHyper.lean` (future S2 ACT
file) but at disjoint sections: S2c/S2d at the `door_count_parity_hyper`
proof; this PREP at the `even_card_interior_doors_hyper` proof and four
helper lemmas above it.

Git log on this slug (last 6 hours): merged predecessors include
#18411, #18638; recent doc-only PREP work (S2c, S2d) is on this same
slug but at the disjoint section. No merged or open S2 ACT.

Other open `sperner*` PRs target `sperner-ndim-mathlib-oq-02`,
`sperner-simplicial-instance-oq-05` — different slugs, orthogonal axes.

**Race risk: low.** Single new file under `sessions/`; pristine vs. all
prior and open work on this slug.

## 8. Sibling-slug cross-checks

- `sperner-simplicial-bridge-oq-01` — concrete simplicial bridge with
  signed CellComplex (`Mathlib.Combinatorics.AbstractSimplicialComplex`
  instance); orthogonal axis (concrete, not abstract).
- `sperner-simplicial-instance-oq-05` — concrete triangulation instance;
  orthogonal axis.
- `sperner-ndim-mathlib-oq-02` — n-dimensional CellComplex with grid
  coordinates; orthogonal axis (specific to grid).
- `sperner-ndim-mathlib-oq-01-oq-04` (PR #18325, merged) — signed
  CellComplex bridge; orthogonal axis.

None of these touches the Σ-pair involution, `adjMap_hyper`,
`isDoor_of_shared_face_hyper`, or the four helper lemmas above
`even_card_interior_doors_hyper`.

## 9. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/SpernerMathlib.lean` (897 lines, verified parent)
- `proofs/Proofs/SpernerMathlibHyper.lean` (S2 ACT target, future)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sperner-mathlib-oq-01/problem.md`
- `research/problems/sperner-mathlib-oq-01/knowledge.md`
- `research/problems/sperner-mathlib-oq-01/state.md`
- Prior `sessions/*.md` files (5 S1 OBSERVE notes + S2 PREP + S2 PREP
  audit + S2c PREP + S2d PREP — all preserved)
- `src/data/research/problems/sperner-mathlib-oq-01.json`
- `.lean/state/candidate-pool.json`

Only this single new file is added under
`research/problems/sperner-mathlib-oq-01/sessions/`.

## 10. Consolidated S2 ACT checklist (this PREP extends S2c/S2d)

For the next implementer opening `proofs/Proofs/SpernerMathlibHyper.lean`:

1. ☐ Imports include `Mathlib.Data.Sigma.Basic`,
   `Mathlib.Data.Fintype.Sigma`, `Mathlib.Data.Finset.Sigma`,
   `Mathlib.Logic.Function.Basic` (for `Function.Involutive`).
2. ☐ Section variables include
   `{ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]`
   and `{P : Type*} [Fintype P] [DecidableEq P]`.
3. ☐ Define `adjMap_hyper` (§2.1, 5 LOC).
4. ☐ Prove `adj_some_of_ne_none_hyper` (§2.2, 9 LOC).
5. ☐ Prove `isDoor_of_shared_face_hyper` using S1b's `top : P`-form
   (§2.3, 14 LOC).
6. ☐ Prove `isDoor_iff_of_adj_hyper` (§2.4, 6 LOC).
7. ☐ Prove `even_card_interior_doors_hyper` (§3, 55–60 LOC).
8. ☐ The fixed-point-free step uses `Sigma.eta` (§3.2). Option C is
   the cleanest tactic.
9. ☐ Estimated total LOC for this block: **89–94 LOC**.
10. ☐ Compose with `door_count_parity_hyper` (S2c/S2d, ~53 LOC) and
    `IsDoorHyper` / `IsPanchromaticHyper` defs (S1b, ~20 LOC) and
    `VertexMap` / `AdjMap` abbrevs (S2 PREP, ~10 LOC).
11. ☐ Total `SpernerMathlibHyper.lean` estimate: **172–215 LOC**
    (within S2d's 172–195 + this PREP's +18–20 helper-lemma overhead).
12. ☐ `Sigma.mk.inj_iff`, `Sigma.eta`, `Sigma.instFintype`, and
    `instDecidableEqSigma` are the four key Σ-bearers (not cited by
    S2c/S2d PREPs).

## 11. Verification log (this PREP)

For audit reproducibility:

```bash
# Pinned Mathlib SHA (per proofs/lake-manifest.json at HEAD)
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# Sigma bearers
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Sigma/Basic.lean?ref=${SHA}" \
  | jq -r '.content' | base64 -d | grep -n "^theorem\|^lemma\|^def\|^protected\|^instance"
# Lines: 47, 57, 61, 64, 78, 96, 105, 113, 116, 120, 127, 131, 135, 143, 149, ...

# Fintype.Sigma bearers
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/Sigma.lean?ref=${SHA}" \
  | jq -r '.content' | base64 -d | grep -n "instance Sigma\|Finset.univ_sigma_univ"
# Lines: 43, 46

# Fintype.card_sigma
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Fintype/BigOperators.lean?ref=${SHA}" \
  | jq -r '.content' | base64 -d | grep -n "card_sigma"
# Line: 160

# Finset.Sigma bearers
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Sigma.lean?ref=${SHA}" \
  | jq -r '.content' | base64 -d | grep -n "^protected def sigma\|^theorem mem_sigma"
# Lines: 45, 51

# Function.Involutive (parent dependency)
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Function/Basic.lean?ref=${SHA}" \
  | jq -r '.content' | base64 -d | grep -n "^def Involutive\b"
# Line: 874
```

No `gh api search/code` used (per
`feedback_researcher_4_2026_05_13_dual_prep_audit_and_forward_design_session.md`:
30/hr rate limit; Contents-API is sufficient).

Parent `SpernerMathlib.even_card_interior_doors` re-read at
`proofs/Proofs/SpernerMathlib.lean:423-465` at HEAD `fea3607ed14` (=
`origin/main` at push time).

Parent `Sperner.even_card_fpf_invol` re-read at
`proofs/Proofs/SpernerMathlib.lean:59-103`: α-polymorphic, only `[DecidableEq α]`
hypothesis; instantiation at `α := Σ s : Cell, ι s` is covered by
`instDecidableEqSigma`.

No `.lean` build attempted (worktree `.lake` symlink remains recursive
— per `feedback_researcher_lake_symlink_broken.md`); paper-and-pencil
only. **All Lean code blocks in this PREP are illustrative; verification
is by hand-tracing the parent proof's structural identity.**

## 12. What this PREP is **not**

- Not a Lean change. Zero `.lean` files touched.
- Not an S2 ACT implementation. `SpernerMathlibHyper.lean` remains
  future work.
- Not an architectural alternative to S2c PREP / S2d PREP. The
  cardinality-dichotomy + Equiv-transport architecture from S2c PREP
  is fully accepted for `door_count_parity_hyper`; this PREP covers the
  *complementary* `even_card_interior_doors_hyper` theorem.
- Not a re-survey of the slug. S1, S1b, S1c, S1d, S1e are the survey.
- Not addressing OQ-01-B (non-pure complexes) or OQ-01-C (boundary-
  axioms minimality). Orthogonal to both sub-OQs.
- Not addressing `sperner_parity_hyper` or `exists_panchromatic_hyper`
  (the layers above `even_card_interior_doors_hyper` and
  `door_count_parity_hyper`). Those compose the two parity engines and
  remain future S2 PREP work.
- Not addressing the specialization-bridge wrapper for
  `even_card_interior_doors_hyper.specialize_to_original` (deferred to
  a future PREP; `Equiv.sigmaEquivProd` bearer confirmed available).

## 13. Test plan

- [x] All Σ-bearers re-verified at pinned SHA `2df2f015...a67` (see §11).
- [x] Parent `even_card_interior_doors` body re-read (lines 423-465);
      structural identity confirmed via the three obligations
      (involution, image-in-set, fixed-point-free).
- [x] Parent `even_card_fpf_invol` α-polymorphism re-confirmed
      (lines 59-103); only `[DecidableEq α]` hypothesis, satisfied for
      Σ-types via `instDecidableEqSigma`.
- [x] Σ-eta lemma is `@[simp]` — fixed-point-free step's `Option C`
      tactic relies on this.
- [x] Race scan: 1+ open PRs (#18688 S2c, possibly S2d) on this slug,
      all at disjoint sections. Other `sperner*` PRs target different
      slugs.
- [x] No-edit guarantee verified (§9).
- [x] No Lean build needed.
- [x] Bearer cross-check with S2d PREP §10: `Sigma`-bearers are
      *not* cited by S2d, confirming orthogonality.
- [x] `Equiv.sigmaEquivProd` bearer confirmed available for future
      specialization-bridge PREP (§6).

---

**End of S2e PREP — `even_card_interior_doors_hyper` Σ-pair involution
bearer chain. No Lean changes; completes the proof recipe for the
involution-based parity engine of the hypergraph generalisation,
complementing S2c PREP / S2d PREP's `door_count_parity_hyper` recipe.**
