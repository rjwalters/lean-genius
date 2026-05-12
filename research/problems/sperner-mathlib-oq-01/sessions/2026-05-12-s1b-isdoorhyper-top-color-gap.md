# sperner-mathlib-oq-01 — S1b OBSERVE: `IsDoorHyper` top-color gap

**Date**: 2026-05-12
**Author**: researcher-8
**Scope**: doc-only follow-up to S1 OBSERVE (PR #18282) — identifies a load-bearing definition gap in `knowledge.md` § 4.1's proposed `IsDoorHyper` that would break the parity argument at S2 ACT time.
**No Lean source changes**, no `meta.json` / `problem.md` / `state.md` / `knowledge.md` edits. Adds one file: this session note.

## The gap

`knowledge.md` § 4.1 (lines 188–191) proposes the hypergraph generalization of `IsDoor` as:

```lean
def IsDoorHyper (vertex : VertexMap (ι := ι)) (c : V → P)
    (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ (c ∘ vertex s) k → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p
```

That is: a face `(s, k)` is a "hyper-door" if, after removing vertex `k`, the remaining vertices realize every palette color *except possibly the one at `k`*.

This is **not** the right generalization of the original `IsDoor` (line 354 of `Proofs/SpernerMathlib.lean`):

```lean
def IsDoor (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) (s : Cell) (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ c (vertex s i) = Fin.castSucc j
```

The original excludes a *fixed* palette element — the top color `Fin.last d`, captured by the restriction of the universal quantifier to `Fin.castSucc j` for `j : Fin d` (which ranges over `{0, …, d−1}`, never hitting `Fin.last d`). The proposed hyper-version replaces "fixed top color" with "color of the removed vertex", which changes the count.

### Concrete divergence (bijective case, `d = 1`)

Take `Cell := PUnit`, `ι := fun _ => Fin 2`, `P := Fin 2`, `vertex := fun _ => id`, `c := id` (so `c ∘ vertex _ = id : Fin 2 → Fin 2`, a bijection).

**Original `IsDoor`**: For each `k : Fin 2`, the condition is `∀ j : Fin 1, ∃ i : Fin 2, i ≠ k ∧ c (vertex _ i) = Fin.castSucc j = 0`.
- `k = 0`: need `i ≠ 0` with `c i = 0`. The only `i ≠ 0` is `i = 1`, but `c 1 = 1 ≠ 0`. **Not a door.**
- `k = 1`: need `i ≠ 1` with `c i = 0`. Take `i = 0`: `c 0 = 0`. ✓ **Door.**

Door count = 1. Bijective, surjective, so the parity prediction (door count mod 2 = surj indicator = 1) is **correct**.

**Proposed `IsDoorHyper`**: For each `k : Fin 2`, the condition is `∀ p ∈ Fin 2, p ≠ c k → ∃ i ≠ k, c i = p`.
- `k = 0`: `c 0 = 0`, so we need `∀ p ≠ 0, ∃ i ≠ 0, c i = p`. Only `p = 1` to check; need `i ≠ 0` with `c i = 1`. Take `i = 1`: ✓. **Door.**
- `k = 1`: `c 1 = 1`, so we need `∀ p ≠ 1, ∃ i ≠ 1, c i = p`. Only `p = 0` to check; need `i ≠ 1` with `c i = 0`. Take `i = 0`: ✓. **Door.**

Door count = 2. Parity = 0. Surj = true. **`door_count_parity_hyper` would predict 1, but the count is 0 — the parity argument is broken.**

This is a fatal failure for `d = 1`. For higher `d` with `|ι s| = |P| = d + 1`, the same calculation gives door count = `d + 1` (every `k` is a door for a bijection), parity = `(d + 1) mod 2`. The parity oscillates with `d`, so no clean Sperner-style statement holds.

### Why the divergence

The original `IsDoor` predicate is asymmetric in palette colors: the top color `Fin.last d` is privileged (excluded from the universal quantifier). This asymmetry is what makes the door count *small* (≤ 1 for bijections) — only the unique vertex mapping to `Fin.last d` is a door.

The proposed hyper-version is symmetric: every palette color is "excludable" depending on which vertex is removed. This symmetry inflates the door count proportionally to `|ι s|`.

For Sperner-style parity, asymmetry is **load-bearing**.

## Correct generalization

The hyper `IsDoor` must be parametrized by a distinguished palette element `top : P`:

```lean
def IsDoorHyper {ι : Cell → Type*} (vertex : ∀ s, ι s → V) (c : V → P)
    (top : P) (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p
```

This specializes to the original by setting `top := Fin.last d` and observing that `{p : Fin (d + 1) | p ≠ Fin.last d}` is in bijection with `Fin d` via `Fin.castSucc`.

### Bijective recount with the correct definition

Re-run `d = 1` with `IsDoorHyper top := 1` (taking `top := Fin.last 1 = 1`):
- `k = 0`: need `∀ p ≠ 1, ∃ i ≠ 0, c i = p`. Only `p = 0`; need `i ≠ 0` with `c i = 0`. `i = 1` gives `c 1 = 1 ≠ 0`. **Not a door.**
- `k = 1`: need `∀ p ≠ 1, ∃ i ≠ 1, c i = p`. Only `p = 0`; need `i ≠ 1` with `c i = 0`. `i = 0` gives `c 0 = 0`. ✓ **Door.**

Door count = 1, matches the original. Parity = 1 = surj indicator. ✓

The same calculation matches the original for all `d`: there is exactly one `k₀` with `c(vertex s k₀) = top`, and that `k₀` is the unique door under bijection.

### Compatibility lemma (would belong in `SpernerMathlibHyper.lean` §3)

```lean
/-- Specialization: the original `IsDoor` is the hyper-version with `top := Fin.last d`. -/
theorem IsDoorHyper.specialize_to_original {d : ℕ}
    (vertex : Cell → Fin (d + 1) → V) (c : V → Fin (d + 1))
    (s : Cell) (k : Fin (d + 1)) :
    IsDoorHyper vertex c (Fin.last d) s k ↔ IsDoor vertex c s k := by
  simp only [IsDoorHyper, IsDoor]
  constructor
  · intro hhyp j
    have hne : (Fin.castSucc j : Fin (d + 1)) ≠ Fin.last d := Fin.castSucc_lt_last j |>.ne
    exact hhyp _ hne
  · intro horig p hp
    have hp_lt : p.val < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp p.isLt) (Fin.val_ne_iff.mpr hp)
    obtain ⟨i, hi_ne, hi_eq⟩ := horig ⟨p.val, hp_lt⟩
    refine ⟨i, hi_ne, ?_⟩
    rw [hi_eq]; exact Fin.ext rfl
```

This lemma is mechanical (~10 lines) but load-bearing: it lets `even_card_interior_doors` and `sperner_parity` be reused as corollaries of their hyper-versions, rather than re-proved.

## Implications for S2 ACT

The "locked S2 scope" in `state.md` (lines 33–48) calls for a mechanical adaptation of the existing API. With the proposed (broken) `IsDoorHyper`:

1. `even_card_interior_doors_hyper` would still be proveable (the involution argument doesn't care about top color), but
2. `door_count_parity_hyper` would *fail* (as shown above), and
3. `sperner_parity_hyper` and `exists_panchromatic_hyper` would have no parity statement to chain from.

**Required `state.md` revision (deferred to S2 ACT)**: change § 4.1's `IsDoorHyper` signature to add a `top : P` parameter. This is a one-line change to `knowledge.md` (line 189) and adds one variable to the `S2 ACT` scope.

**Required `SpernerMathlibHyper.lean` API (revised)**:

```lean
section HypergraphDoor

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]

abbrev VertexMap := ∀ s : Cell, ι s → V
abbrev AdjMap := ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s')

/-- Palette-relative panchromaticity. -/
def IsPanchromaticHyper (vertex : VertexMap (ι := ι)) (c : V → P)
    (s : Cell) : Prop :=
  Function.Surjective (c ∘ vertex s)

/-- Palette-relative door, with distinguished palette element `top`. -/
def IsDoorHyper (vertex : VertexMap (ι := ι)) (c : V → P)
    (top : P) (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p

/-- Interior-doors parity, hypergraph version. The `top : P` parameter
    must match the one in `IsDoorHyper`. -/
theorem even_card_interior_doors_hyper
    (vertex : VertexMap (ι := ι)) (adj : AdjMap (ι := ι))
    (hadj_symm : ∀ s i s' i', adj s i = some ⟨s', i'⟩ → adj s' i' = some ⟨s, i⟩)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    (hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
    (top : P) (c : V → P) :
    Even ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card := …

/-- Per-cell door parity, hypergraph version. -/
theorem door_count_parity_hyper
    (f : ι s → P) (top : P) [Fintype (ι s)] [DecidableEq P] :
    (Finset.univ.filter
      (fun k : ι s => ∀ p ≠ top, ∃ i : ι s, i ≠ k ∧ f i = p)).card % 2 =
    if Function.Surjective f then 1 else 0 := …

theorem sperner_parity_hyper
    (vertex : VertexMap (ι := ι)) (adj : AdjMap (ι := ι))
    (hadj_symm hadj_vertex hadj_ne : …) (top : P) (c : V → P) :
    (Finset.univ.filter (IsPanchromaticHyper vertex c)).card % 2 =
    (Finset.univ.filter
      (fun p : Σ s : Cell, ι s => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card % 2 := …

theorem exists_panchromatic_hyper
    (vertex : VertexMap (ι := ι)) (adj : AdjMap (ι := ι))
    (hadj_symm hadj_vertex hadj_ne : …) (top : P) (c : V → P)
    (hbdry_odd : Odd ((Finset.univ.filter
      (fun p : Σ s : Cell, ι s => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card)) :
    ∃ s : Cell, IsPanchromaticHyper vertex c s := …

end HypergraphDoor
```

The `top : P` parameter appears in `IsDoorHyper`, `even_card_interior_doors_hyper`, `door_count_parity_hyper`, `sperner_parity_hyper`, and `exists_panchromatic_hyper`. This is **5 signature changes** vs. the original `knowledge.md` § 4.1 — small surface area, but every theorem affected.

## Why `top` doesn't reduce flexibility

A reader might object: "by parametrizing by a distinguished palette element, we lose abstraction — the original Sperner is *about* `Fin (d + 1)`, where `Fin.last d` is canonical."

Three responses:

1. **The original is also parametrized by a top color**, hidden inside `Fin.castSucc`. The hyper version just makes this dependency explicit.

2. **The S2 ACT consumer always has a natural `top`**. In hypergraph applications (e.g., Tucker's lemma, the Brouwer fixed-point applications listed in `problem.md`), the palette `P` comes with a natural distinguished element (e.g., a fixed point, a "trivial" coloring, etc.).

3. **For applications where no top is canonical**, one can quantify over `top : P` and take the `Finset.image`/`Finset.sum` of door counts over the choice of `top` — but this is a downstream concern, not a definition-level constraint.

## Anti-targets (do not pick up these in S1b)

- **Editing `knowledge.md` directly**: PR #18282 (S1 OBSERVE) is recently merged; editing its product files (rather than adding a session note) would convolute the history. The 1-line `knowledge.md` fix should be bundled with S2 ACT.

- **Editing `state.md`**: same reason; S2 ACT will own state.md updates.

- **Editing `proofs/Proofs/SpernerMathlib.lean`**: out of scope; the original definition is correct as-is.

- **Adding `SpernerMathlibHyper.lean`**: that's S2 ACT, not S1b OBSERVE. This session note is forward-planning only.

- **Adding `loom:review-requested`**: math-agent policy (CLAUDE.md axiom-integrity).

## Honest scope

This file is a **doc-only S1b extension** of PR #18282's S1 OBSERVE. It does NOT discharge any sorry, modify any Lean source, change any `meta.json` count, or edit any other research file. The single new file is this session note.

The finding is mathematically substantive: the proposed `IsDoorHyper` signature in `knowledge.md` § 4.1 lacks a parameter needed for the parity argument to chain through `door_count_parity_hyper`. A counter-example at `d = 1` demonstrates the failure concretely.

S2 ACT should:
1. Use the corrected `IsDoorHyper` signature with `top : P`.
2. Update `knowledge.md` § 4.1 (one-line addition: `top : P` parameter) as part of the S2 PR.
3. Include the `IsDoorHyper.specialize_to_original` compatibility lemma so that `even_card_interior_doors`, `sperner_parity`, etc. become corollaries of their hyper-versions (avoiding duplicate proof work).

## Differentiation from PR #18282

PR #18282 (researcher-1, merged 2026-05-12 ~20:48 UTC) shipped the axiomatic audit and proposed the S2 scope. This session note refines the S2 signature locked in by that PR: adds the `top : P` parameter to `IsDoorHyper` (and 4 downstream theorems), justified by the `d = 1` bijective counter-example. This is a non-trivial S1 correction that should be addressed before any S2 ACT begins.

**Recommendation**: any researcher claiming this slug for S2 ACT should adopt the corrected signatures here. The total signature surface change is ~5 lines (adding `top : P` as a parameter to 5 definitions/theorems); the proof side is unaffected (the door-counting argument carries through identically with the fixed `top`).
