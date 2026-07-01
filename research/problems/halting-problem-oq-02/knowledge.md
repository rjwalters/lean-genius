# Knowledge Base: halting-problem-oq-02 (Totality Problem Undecidability)

## Problem Understanding

Target (from problem.md sketch): prove the **totality problem** is undecidable —
`¬ ComputablePred (fun c => c ∈ TotalCodes)` where
`TotalCodes = {c | ∀ n, (eval c n).Dom}`. A direct Rice's-theorem instance on a
concrete extensional, nontrivial code-class. Category: extension of parent
`halting-problem`.

## Result (07-01, researcher-1) — SHIPPED, VERIFIED 0-axiom, 0 sorries

New file `proofs/Proofs/HaltingProblemOQ02.lean` (144 lines, 9 thm / 3 def).
`#print axioms` on the three headline theorems: `[propext, Classical.choice,
Quot.sound]` only — no `sorryAx`, no `Lean.ofReduceBool`. Compiled with
`lake env lean` against pinned Mathlib v4.26.0.

Works inside Mathlib's real computation model `Nat.Partrec.Code` (universal
evaluator `eval : Code → ℕ →. ℕ`), so this is the GENUINE computation-theoretic
undecidability — the parent `halting-problem` gallery entry explicitly states its
abstract-oracle model does NOT establish this and points to `Nat.Partrec /
ComputablePred` as the needed route. This file supplies exactly that.

Declarations:
- `totalFns := {f : ℕ →. ℕ | ∀ n, (f n).Dom}`; nontriviality witnesses
  `some_mem_totalFns` (identity total), `none_notMem_totalFns` (divergent not total).
- `totality_not_computable` — MAIN, via `ComputablePred.rice totalFns h
  Nat.Partrec.some Nat.Partrec.none some_mem_totalFns` then apply to `0`.
- `TotalCodes := {c | ∀ n, (eval c n).Dom}`; `totalCodes_extensional` (simp with
  eval-equality), `totalCodes_nontrivial` (pull witnesses back through `exists_code`).
- `totality_not_computable_of_codes` — code-level, via `ComputablePred.rice₂`
  (computable extensional code-sets = exactly ∅ / univ; TotalCodes is neither).
- Dual: `emptyFns`, `emptiness_not_computable` (halts-on-no-input, swap witnesses).

Gallery data added: `src/data/proofs/halting-problem-oq-02/{meta.json,annotations.json}`
(status verified, badge verified, parentId halting-problem, openQuestionId oq-02).

## Gotchas / lessons

- `rice` / `rice₂` live in namespace `ComputablePred` (NOT bare `rice`). Use
  `ComputablePred.rice` / `ComputablePred.rice₂`.
- `rice` signature: `(C) (h : ComputablePred fun c => eval c ∈ C) {f g}
  (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C`. It only takes
  the `f ∈ C` witness; the contradiction comes from `g ∈ C` being false.
- `Nat.Partrec.some : Partrec Part.some` (total identity), `Nat.Partrec.none :
  Partrec fun _ => Part.none`. `(Part.none).Dom` reduces definitionally to `False`.
- `open Nat.Partrec (Code)` + `open Nat.Partrec.Code` exposes `eval`, `exists_code`.
- BUILD/INFRA: `/private/tmp` worktrees get REAPED mid-session (Lean file + research/
  + src/data/research vanished, .git severed). Use a durable path under
  `/Users/rwalters/GitHub/lean-genius-wt/` instead.

## Scope / open

Proves NOT computable. Totality is Π₂-complete (hence not c.e., not co-c.e.); the
sharper arithmetical classification is NOT done — Mathlib v4.26.0 lacks the
arithmetical hierarchy. Left as the open follow-up.

## Status: COMPLETED (0-sorry, 0-axiom, gallery entry created).
