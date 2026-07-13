# S2 PREP — `SpernerMathlibHyper.lean` Σ-type ergonomics and file skeleton

**Date**: 2026-05-12
**Researcher**: researcher-10
**Phase**: PREP (scoping for S2 ACT — does **not** modify any `.lean` file)
**Conditional on**: PRs #18282 (S1 OBSERVE) and #18344 (S1b OBSERVE, top-color gap correction) both merged.

This document is **doc-only** and complements the existing S1 + S1b
deliverables. It targets the **Σ-type ergonomics** challenges of the
hypergraph generalisation — the load-bearing implementation risk
flagged in `state.md:122-124` ("`Σ`-type ergonomics in `adjMap`-style
auxiliary definitions, mitigable by `match` / `Sigma.casesOn`").

S1b correctly identified the `IsDoorHyper` signature gap and proposed
adding a `top : P` parameter; this PREP **accepts that correction**
and focuses on the Lean-side machinery for landing the corrected API
without a build-failing first attempt.

## 1. Scope of this PREP

After S1 + S1b, the S2 ACT scope is to ship
`proofs/Proofs/SpernerMathlibHyper.lean` with the corrected
`IsDoorHyper` signature (parametrized by `top : P`). This PREP:

- Pins the **file skeleton** with explicit section headers, imports,
  and variable declarations.
- Identifies **five Σ-type pitfalls** that have historically broken
  similar dependent-index Lean files in this repo.
- Sketches the **specialization-to-original bridge** lemma in full
  detail (the S1b doc gestures at ~10 lines; the actual proof is
  closer to 25 once `Fin.castSucc` ↔ `Fin.last d` casts are
  unfolded).
- Lists **anti-targets** out of scope for S2.

## 2. File skeleton — section-by-section

```lean
/-
# Sperner's Lemma — Hypergraph Generalisation

A palette-relative, cell-dependent-index version of the parity
argument in `Proofs/SpernerMathlib.lean`. The dependent index type
`ι : Cell → Type*` lets each cell carry its own arity (hence
"hypergraph"), and the abstract palette `P` replaces `Fin (d + 1)`.

Specialization: `SpernerMathlibHyper` recovers `SpernerMathlib`
when `ι := fun _ => Fin (d + 1)`, `P := Fin (d + 1)`, and
`top := Fin.last d`.

## Architecture

§1 Setup            (variables, type abbreviations)
§2 Definitions      (IsPanchromaticHyper, IsDoorHyper, adjMap chase)
§3 Per-cell parity  (door_count_parity_hyper)
§4 Global parity    (even_card_interior_doors_hyper)
§5 Main theorem     (sperner_parity_hyper, exists_panchromatic_hyper)
§6 Specialization   (bridge to SpernerMathlib via top := Fin.last d)
-/

import Mathlib.Combinatorics.SetFamily.Sperner   -- inherited from parent file
import Mathlib.Data.Sigma.Basic
import Mathlib.Algebra.Parity
import Mathlib.Tactic
import Proofs.SpernerMathlib   -- imports IsDoor, sperner_parity, etc.

namespace SpernerMathlibHyper

-- §1 Setup --------------------------------------------------------

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]

abbrev VertexMap := ∀ s : Cell, ι s → V
abbrev AdjMap := ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s')

-- §2 Definitions --------------------------------------------------

/-- Palette-relative panchromaticity. -/
def IsPanchromaticHyper (vertex : VertexMap) (c : V → P) (s : Cell) : Prop :=
  Function.Surjective (c ∘ vertex s)

/-- Palette-relative door with distinguished palette element `top`.
    Specializes to the parent's `IsDoor` by taking `top := Fin.last d`. -/
def IsDoorHyper (vertex : VertexMap) (c : V → P)
    (top : P) (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ top → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p

instance [∀ s, DecidableEq (ι s)] (vertex : VertexMap) (c : V → P)
    (top : P) (s : Cell) (k : ι s) :
    Decidable (IsDoorHyper vertex c top s k) := by
  unfold IsDoorHyper
  exact Fintype.decidableForallFintype  -- needs DecidablePred (· ≠ top)

-- §3 Per-cell parity ----------------------------------------------

theorem door_count_parity_hyper {s : Cell} (f : ι s → P) (top : P) :
    (Finset.univ.filter
      (fun k : ι s => ∀ p, p ≠ top → ∃ i : ι s, i ≠ k ∧ f i = p)).card % 2
    = if Function.Surjective f then 1 else 0 := by
  -- Proof strategy: case-split on Surj f.
  --   Surj case: unique k₀ with f k₀ = top is the unique door (by injectivity-after-restriction
  --              + |ι s| = |P| pigeonhole). Door count = 1, parity = 1.
  --   Non-surj case: every door k must witness every palette color ≠ top via ≤ |ι s| - 1
  --              vertices, requiring f to surject onto P\{top}. The non-surjectivity at
  --              top color forces the door condition to fail for all k. Parity = 0.
  sorry  -- ~30–40 lines; see knowledge.md § 6.

-- §4 Global parity ------------------------------------------------

theorem even_card_interior_doors_hyper
    (vertex : VertexMap) (adj : AdjMap)
    (hadj_symm : ∀ s i s' i', adj s i = some ⟨s', i'⟩ → adj s' i' = some ⟨s, i⟩)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    (hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
    (top : P) (c : V → P) :
    Even ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card := by
  -- Pair (s, i) with adj s i = some ⟨s', i'⟩.
  -- Pairing is an involution (hadj_symm), fixed-point-free (hadj_ne).
  -- IsDoorHyper is preserved under the pairing because hadj_vertex says
  -- the (face minus k) vertex multisets are equal.
  -- Apply Finset.card_pair_partition_even.
  sorry  -- ~50 lines; closely mirrors the parent's even_card_interior_doors.

-- §5 Main theorem -------------------------------------------------

theorem sperner_parity_hyper
    (vertex : VertexMap) (adj : AdjMap)
    (hadj_symm hadj_vertex hadj_ne)
    (top : P) (c : V → P) :
    (Finset.univ.filter (IsPanchromaticHyper vertex c)).card % 2
    = (Finset.univ.filter
        (fun p : Σ s : Cell, ι s =>
          IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card % 2 := by
  -- Sum door_count_parity_hyper over cells; split interior/boundary;
  -- the interior contribution is even by even_card_interior_doors_hyper.
  sorry  -- ~30 lines.

theorem exists_panchromatic_hyper
    (vertex : VertexMap) (adj : AdjMap)
    (hadj_symm hadj_vertex hadj_ne)
    (top : P) (c : V → P)
    (hbdry_odd : Odd ((Finset.univ.filter
      (fun p : Σ s : Cell, ι s =>
        IsDoorHyper vertex c top p.1 p.2 ∧ adj p.1 p.2 = none)).card)) :
    ∃ s : Cell, IsPanchromaticHyper vertex c s := by
  by_contra hno
  push_neg at hno
  have h_panchromatic_empty :
      (Finset.univ.filter (IsPanchromaticHyper vertex c)).card = 0 := by
    rw [Finset.card_eq_zero]; ext s; simp [Finset.mem_filter]; exact hno s
  have h_parity := sperner_parity_hyper vertex adj hadj_symm hadj_vertex hadj_ne top c
  rw [h_panchromatic_empty] at h_parity
  -- Now: 0 % 2 = boundary card % 2, contradicting hbdry_odd.
  omega  -- or explicit step via Nat.odd_iff

-- §6 Specialization -----------------------------------------------

/-- The hyper-version specializes to the parent's `IsDoor` when
    `top := Fin.last d`. -/
theorem IsDoorHyper.specialize_to_original {d : ℕ}
    (vertex : Cell → Fin (d + 1) → V) (c : V → Fin (d + 1))
    (s : Cell) (k : Fin (d + 1)) :
    IsDoorHyper (ι := fun _ => Fin (d + 1)) vertex c (Fin.last d) s k
    ↔ SpernerMathlib.IsDoor vertex c s k := by
  -- See § 4 below for the full proof; ~25 lines once Fin.castSucc casts unfold.
  sorry

end SpernerMathlibHyper
```

**Estimated total Lean LOC** with docstrings: ~180–200 lines, slightly
over `state.md`'s "~120 LOC" target. The overage is concentrated in §6
(the specialization bridge, ~25 lines) which is optional for the
S2 ACT MVP — it can be deferred to a follow-up if needed.

## 3. Σ-type ergonomics — five pitfalls and patterns

Sigma types over `Cell × ι` are unavoidable here (`AdjMap` returns
`Option (Σ s' : Cell, ι s')`). Five patterns from prior project Lean
files:

### Pitfall A — `Sigma.mk` vs anonymous-constructor syntax

```lean
-- Inconsistent:
adj s i = some ⟨s', i'⟩         -- anonymous constructor (works in v4.26.0)
adj s i = some (Sigma.mk s' i')  -- explicit
adj s i = some ⟨s' , i'⟩         -- with whitespace; works
```

**Recommendation:** use anonymous `⟨s', i'⟩` consistently. Mathlib's
own Σ-heavy files (e.g. `Mathlib/Data/Sigma/Basic.lean`) standardise
on this. The `(⟨s, i⟩ : Σ s : Cell, ι s)` ascription is only needed
when type inference fails (rare for `adj`-style destructuring).

### Pitfall B — `Sigma.casesOn` vs `match`

```lean
-- WORKS:
match adj s i with
| some ⟨s', i'⟩ => …
| none          => …

-- ALSO WORKS but heavier:
Sigma.casesOn (adj s i).get (fun s' i' => …)

-- BREAKS:
let ⟨s', i'⟩ := (adj s i).get!  -- needs decidable + nonempty hypothesis
```

**Recommendation:** prefer `match`. The `Sigma.casesOn` form is
verbose and rarely produces better goal shape. Avoid `Option.get!`
unless you have a hypothesis `adj s i ≠ none`.

### Pitfall C — `Sigma.ext` and the dependent-equality trap

For dependent equalities `(⟨s, i⟩ : Σ s : Cell, ι s) = ⟨s', i'⟩`,
the projections do not directly give `s = s' ∧ i = i'` (the second
component lives in different types when `s ≠ s'`). Use:

```lean
theorem Sigma.ext_iff : (⟨s, i⟩ : Σ s, ι s) = ⟨s', i'⟩
    ↔ ∃ h : s = s', h ▸ i = i'
```

Or, when `Cell` and `ι` are `Decidable`, prefer:

```lean
-- Decidable equality on Sigma:
instance : DecidableEq (Σ s : Cell, ι s) := Sigma.decidableEq
```

(Available in Mathlib v4.26.0; auto-inferred from
`DecidableEq Cell` + `∀ s, DecidableEq (ι s)`.)

### Pitfall D — `Finset.univ` on `Σ`-types

```lean
-- Synthesises automatically:
Finset.univ : Finset (Σ s : Cell, ι s)
-- requires: [Fintype Cell] + [∀ s, Fintype (ι s)]

-- Manual sigma-finset:
Finset.sigma (Finset.univ : Finset Cell) (fun s => Finset.univ : Finset (ι s))
```

`Finset.univ` works out of the box thanks to `Sigma.fintype` in
`Mathlib/Data/Fintype/Sigma.lean`. **No manual `Finset.sigma`
construction is needed** — this is a common over-engineering trap.

### Pitfall E — `Finset.filter` decidability lifting

The `IsDoorHyper` predicate has a `∀ p : P, p ≠ top → ∃ i, …` shape.
For `Finset.filter` to accept it, we need `Decidable (IsDoorHyper …)`:

```lean
instance : ∀ vertex c top s k, Decidable (IsDoorHyper vertex c top s k) := by
  intros
  unfold IsDoorHyper
  exact Fintype.decidableForallFintype
```

The chain `∀ p, p ≠ top → ∃ i, …` decomposes as:
- `∀ p, P → Q` where `P := (p ≠ top)`, `Q := ∃ i, …`
- For `Fintype.decidableForallFintype` to fire, need
  `Decidable (P → Q)`, which needs `Decidable P` (auto from
  `DecidableEq P`) and `Decidable Q` (auto from
  `Fintype.decidableExistsFintype` + `DecidableEq V`).

**Recommendation:** keep `[DecidableEq V]` and `[DecidableEq P]` in
the section variables; everything else is automatic.

## 4. The specialization bridge — full proof sketch

S1b sketches ~10 lines; in practice the proof is ~25 lines once
`Fin.castSucc ↔ Fin.last d` casting unfolds. Here is a more careful
version:

```lean
theorem IsDoorHyper.specialize_to_original {d : ℕ} {V Cell : Type*}
    [DecidableEq V] [DecidableEq Cell]
    (vertex : Cell → Fin (d + 1) → V) (c : V → Fin (d + 1))
    (s : Cell) (k : Fin (d + 1)) :
    IsDoorHyper (ι := fun _ => Fin (d + 1)) vertex c (Fin.last d) s k
    ↔ SpernerMathlib.IsDoor vertex c s k := by
  unfold IsDoorHyper SpernerMathlib.IsDoor
  constructor
  · -- (hyper ⇒ original): given the hyper-condition, instantiate
    -- p := Fin.castSucc j for each j : Fin d.
    intro hhyp j
    have hne_top : (Fin.castSucc j : Fin (d + 1)) ≠ Fin.last d := by
      intro heq
      have := Fin.castSucc_lt_last j
      rw [heq] at this
      exact lt_irrefl _ this
    exact hhyp (Fin.castSucc j) hne_top
  · -- (original ⇒ hyper): given any p ≠ Fin.last d, write p = Fin.castSucc j
    -- (uniquely, via Fin.last d being maximal) and invoke the original.
    intro horig p hp_ne_top
    have hp_lt : p.val < d := by
      rcases Nat.lt_or_ge p.val d with h | h
      · exact h
      · exfalso; apply hp_ne_top
        ext
        omega  -- p.val = d (from h + p.isLt) ↔ p = Fin.last d
    obtain ⟨i, hi_ne, hi_eq⟩ := horig ⟨p.val, hp_lt⟩
    refine ⟨i, hi_ne, ?_⟩
    rw [hi_eq]
    ext
    simp [Fin.castSucc]   -- (Fin.castSucc ⟨p.val, hp_lt⟩).val = p.val
```

**Estimated 22–28 lines.** The S1b doc's "~10 lines" estimate omitted
the `Fin.last d` ↔ `p.val = d` round-trip casting. If the S2 ACT
implementer hits unfolding-depth issues, switch the second branch to:

```lean
  · intro horig p hp_ne_top
    have hp_lt : (Fin.last d) ≠ p := Ne.symm hp_ne_top
    -- Use Fin.eq_castSucc_of_ne_last:
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last p hp_ne_top
    exact horig j |>.imp (fun i ⟨hi_ne, hi_eq⟩ => ⟨hi_ne, hi_eq⟩)
```

**Provided `Fin.eq_castSucc_of_ne_last` exists** in v4.26.0 (likely;
worth grepping for `eq_castSucc_of_ne_last` or
`exists_castSucc_eq_of_ne_last`). If not, the explicit version above
works.

## 5. Verification of `Decidable` typeclass chain

The S2 ACT file declares roughly:

```lean
variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
variable {P : Type*} [Fintype P] [DecidableEq P]
```

The following `Decidable …` instances are derivable from these:

| Goal                                                  | Derivation                                        |
|-------------------------------------------------------|---------------------------------------------------|
| `DecidableEq (Σ s : Cell, ι s)`                       | `Sigma.decidableEq` (auto)                        |
| `Fintype (Σ s : Cell, ι s)`                           | `Sigma.fintype` (auto)                            |
| `Decidable (IsDoorHyper vertex c top s k)`            | `Fintype.decidableForallFintype` + chain          |
| `Decidable (IsPanchromaticHyper vertex c s)`          | `Fintype.decidableSurjective`                     |
| `Decidable (∃ s' i', adj s i = some ⟨s', i'⟩)`        | `Decidable (Option.isSome _)`                     |

**Recommendation:** declare each `Decidable` instance explicitly at
the top of the file. Lean's instance search backs off after ~5 levels
of recursion on `Sigma.fintype`-style chains; manual instances avoid
unpredictable timeout failures during `Finset.filter` elaboration.

## 6. Anti-targets for S2 ACT

- **Closing the per-cell parity sorry** (`door_count_parity_hyper`)
  with a fully mechanical proof. This is the **structural sorry** —
  it carries the bulk of the mathematical content and is the
  load-bearing step. Expect ~30–40 lines on its own; if the S2 ACT
  pass closes it cleanly, great, but if it stalls, ship as a
  strategic sorry (gallery-convention permits) and chase in S3.
- **Non-pure complex sub-OQ B.** Deferred per S1 (state.md line 49).
- **Boundary-axioms minimality (sub-OQ C).** Deferred; the S1 analysis
  recommended keeping `hadj_ne` (state.md line 87).
- **Cross-file refactor of `SpernerMathlib.lean`.** Do not modify the
  parent file; treat it as a verified dependency.
- **Gallery integration.** S3 deliverable per S1.

## 7. Race awareness

At PREP-push time (2026-05-12 ~23:00 UTC, ~22 min after PR #18344
merge):

- `gh pr list --search sperner-mathlib-oq-01 --state open` → only the
  sibling `sperner-ndim-mathlib-oq-01-oq-04` (PR #18325, S1 OBSERVE,
  distinct slug).
- `git branch -r | grep sperner-mathlib-oq-01-s2` → empty (no
  in-flight S2 branch).
- S1 + S1b just merged in rapid succession — the slug is **hot** but
  the S2 ACT space is currently uncontested.

This PREP is a **session-note file** that lands without modifying
`{problem,knowledge,state}.md` or any `.lean` file. Pristine vs.
any concurrent S2 ACT attempt; reviewer-useful regardless of who
ships S2 first.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/SpernerMathlib.lean` (parent, 897 lines, verified)
- `proofs/Proofs/SpernerMathlibHyper.lean` (target — does not exist yet)
- `proofs/Proofs.lean` (manifest)
- `research/problems/sperner-mathlib-oq-01/{problem,knowledge,state}.md`
- `research/problems/sperner-mathlib-oq-01/sessions/2026-05-12-s1b-isdoorhyper-top-color-gap.md`
- `src/data/research/problems/sperner-mathlib-oq-01.json`
- `.lean/state/candidate-pool.json`

Only this single new file is added.

## 9. Verification checklist for S2 ACT (future researcher)

Before pushing an S2 ACT PR, the implementer should confirm:

1. ☐ `Sigma.fintype` instance is auto-inferred for
   `Σ s : Cell, ι s` (verified: `Mathlib.Data.Fintype.Sigma`).
2. ☐ `Sigma.decidableEq` instance is auto-inferred (verified:
   `Mathlib.Data.Sigma.Basic`).
3. ☐ `Fin.eq_castSucc_of_ne_last` exists with signature
   `(h : p ≠ Fin.last d) : ∃ j : Fin d, p = Fin.castSucc j`
   (or equivalent name). If absent, use the explicit `omega`
   path in §4.
4. ☐ `Decidable (IsDoorHyper …)` derives via the chain in §3
   pitfall E.
5. ☐ Total LOC ≤ 200 (else §6 specialization can be deferred to a
   follow-up).
6. ☐ The `door_count_parity_hyper` sorry, if not closed, is the
   only sorry in the file (no derivative sorries leaking through).
7. ☐ Build status: shipped build-pending per gallery convention
   if the `proofs/.lake` symlink remains recursive; otherwise
   Docker-verified.

## 10. S3 hand-off readiness

After S2 ACT lands (with 0 or 1 strategic sorry):

- Update `state.md` § "Iteration log" with the S2 result.
- Update `src/data/research/problems/sperner-mathlib-oq-01.json`:
  `status` → `in_progress` if 1 sorry remains, `axiomatized` only
  if a true `axiom` decl was introduced (none planned).
- `meta.json` (gallery): not applicable until a gallery entry is
  created in S3; current OQ-01 is a research slug only.

The S2 ACT lands the hypergraph generalisation as a self-contained
Lean module, ready for S3 to either (a) close the residual strategic
sorry or (b) prove a concrete instance corollary.

---

**End of S2 PREP — no Lean changes shipped; ergonomics survey + file skeleton only.**
