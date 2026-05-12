# godel-second-incompleteness-oq02-oq-02 — Solovay's Arithmetical Completeness for GL

## Question

> **Solovay's Arithmetical Completeness Theorem (1976).** The propositional modal logic GL (Gödel-Löb) is sound and complete for the provability interpretation in PA. Formally:
>
> `GL ⊢ φ ⟺ ∀ * : PropAtom → Formula_PA, PA ⊢ φ*`
>
> where `*` is any "arithmetical realization" sending propositional atoms to PA-formulas and the modality `□` to the Gödel provability predicate `Prov`.

The OQ asks for a Lean 4 formalization of this theorem in the framework of `Proofs/GodelSecondIncompletenessOQ02.lean` (and its parent `GodelIncompleteness.lean`). The goal is the **completeness direction** (Solovay's hard result); the soundness direction reduces to the HBL derivability conditions D1–D3 already axiomatized in the parent file.

## Why it matters

1. **Definitive answer to the provability question.** Hilbert-Bernays-Löb conditions tell us *which* provability facts hold; Solovay's theorem tells us *exactly* which propositional modal facts hold for the provability predicate. It is the conceptual analogue of Gödel completeness for first-order logic — bounding the propositional theory of provability.

2. **GL is decidable.** Unlike PA itself, GL has a decision procedure (in fact GL is in PSPACE). Solovay's theorem therefore gives a *decidable* characterization of the propositional fragment of PA-provability.

3. **Bridges modal logic and arithmetic.** The theorem is the canonical bridge between two large mathematical fields (modal logic / Kripke semantics on one side, formal arithmetic / Hilbert-style derivability on the other). A Lean formalization unlocks downstream applications to provability-logic refinements (GLP, GLS, polymodal extensions).

4. **Wiedijk's 100-theorems list (#56 "Gödel's incompleteness theorems").** The current `GodelIncompleteness` file proves the first and second incompleteness theorems; Solovay's theorem is the canonical "third pillar" of the provability-logic story and a natural next-step extension.

## Scope of S1 OBSERVE

Documentation only — no Lean code changes. We catalogue:

1. The precise statement of GL (axioms + rules) and the arithmetical translation operation `*`.
2. The four pieces of the soundness direction (already half-axiomatized in `GodelSecondIncompletenessOQ02.lean`).
3. The structure of Solovay's completeness proof (Kripke-frame construction over the arithmetical theory).
4. Existing Mathlib / gallery infrastructure that can be reused.
5. A graded S2/S3 plan splitting the work into proportionate milestones — soundness first, then easier fragments of completeness.

## Anchoring file references

- `Proofs/GodelIncompleteness.lean` — base layer: `Formula`, `Provable`, `godelNum`, HBL conditions, first incompleteness.
- `Proofs/GodelSecondIncompletenessOQ02.lean:65–84` — `falsum`, `Con` (consistency formula in object language).
- `Proofs/GodelSecondIncompletenessOQ02.lean:120–153` — `con_implies_G` axiom (the formalized first-incompleteness step that mediates the second-incompleteness proof).
- `Proofs/GodelSecondIncompletenessOQ02.lean:186` — `second_incompleteness` (consistent F ⊬ Con(F)).
- `Proofs/GodelSecondIncompletenessOQ02.lean:213` — informal statement of Löb's theorem (the modal axiom that distinguishes GL from K4).
