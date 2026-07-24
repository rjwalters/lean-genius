# S22a (2026-07-24, researcher-3) — finite Lindenbaum layer: FMP groundwork

## Goal

First slice of the mapped S22 stage (full GL decidability via the finite
model property / Segerberg canonical finite model). This session builds the
world-construction layer every canonical-model session needs, with no
speculative scaffolding beyond it.

## Shipped

`proofs/Proofs/GodelSecondIncompletenessOQ02Lindenbaum.lean` — Mathlib-free
(imports GLSyntax + GLFour + Kalmar only), docker green (5 jobs),
**0 sorries, 0 axiom declarations** (footprint: foundational
`Classical.choice`/`propext` only, via `Classical.byContradiction` and the
scoped `Classical.propDecidable` inside `extend`).

1. **Consistency calculus** over S19's `PDeriv`: `Consistent Γ := ¬ PDeriv Γ ⊥`,
   antitonicity, `deriv_neg_of_inconsistent` (deduction-theorem bridge),
   classical splitting `consistent_cons_or`, `consistent_cons_of_deriv`.
2. **Subformula closure**: `subf` list, `self_mem_subf`, transitivity
   `subf_closed`.
3. **Finite Lindenbaum lemma** (`lindenbaum`): one-pass classical sweep
   `extend` over the closure list; maximality holds because a skipped
   formula was skipped against a subset of the final context (weakening
   transports the inconsistency forward). No Zorn.
4. **Maximal-set toolkit** (`MaximalIn`): derivability closure
   (`mem_of_deriv`, `deriv_iff_mem`), closure-relative negation
   completeness (`neg_deriv_of_not_mem` / `not_mem_of_neg_deriv`),
   `falsum_not_mem`, and `impl_mem_iff` — the `→`-case of the future truth
   lemma, discharged here once and for all.
5. **Root world** (`exists_root_world`): `GL ⊬ φ` ⇒ some maximal
   consistent `Δ ⊆ subf (¬φ)` with `¬φ ∈ Δ`.

## Key observations

- `PDeriv` needs **no extension** for the canonical model: modal
  completeness never uses necessitation under hypotheses, and
  `PDeriv.thm` already imports arbitrary modal GL theorems.
- Lean gotcha: a doc comment cannot precede `open Classical in` — the
  `open ... in` must come first.

## Next (S22b)

Canonical finite model over `MaximalIn` worlds (Boolos Ch. 5):
- list-conjunction machinery (`conjList` + derivation lemmas + box
  distribution via K and S18 `four`);
- accessibility `w R v` iff (∀ □ψ ∈ w: ψ, □ψ ∈ v) ∧ (∃ □ψ ∈ v \ w);
- the box-case consistency lemma (the Löb trick);
- truth lemma (only atom/falsum/box cases remain) → Segerberg
  completeness → FMP; then S22c: full decidability.

Arithmetic Htaut/Hk/Hlob route unchanged (blocked on Σ₁ Provable rebuild).
