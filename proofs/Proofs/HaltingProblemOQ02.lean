import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic

/-
# The Totality Problem is Undecidable (a Rice's-Theorem instance)

## Open Question (halting-problem-oq-02)
"Undecidability of the Totality Problem (Rice's Theorem instance): is the set of
(indices of) programs that halt on *every* input decidable?"

## Answer
No. The **totality problem** `TOT = { c | ∀ n, program c halts on input n }` is not
computable. This is the archetypal application of Rice's theorem: totality is a
*semantic* (extensional) property of the partial function `eval c` — it depends only
on the function computed, not on the code — and it is *nontrivial* (some programs are
total, some are not). Every such property is undecidable.

We work in Mathlib's standard model of computation: `Nat.Partrec.Code`, with
`Code.eval : Code → ℕ →. ℕ` the universal evaluator. "`c` halts on input `n`" is
`(eval c n).Dom`, so totality of `c` is `∀ n, (eval c n).Dom`.

## What is proved (all VERIFIED, 0 sorries, 0 axioms beyond Mathlib's foundational core)

* `totalFns` / `TotalCodes` — the totality property, as a set of partial functions
  (`ℕ →. ℕ`) and, extensionally, as a set of codes.
* `some_mem_totalFns` / `none_notMem_totalFns` — the two witnesses that make totality
  **nontrivial**: the identity function is total, the empty (everywhere-divergent)
  function is not. Nontriviality is exactly the hypothesis Rice's theorem needs.
* `totality_not_computable` — **the main result**: `TOT` is not computable, via
  Mathlib's `rice`.
* `totality_not_computable_of_codes` — the same on the level of `Set Code`, via
  `rice₂` (which characterises the computable extensional code-sets as exactly `∅`
  and `univ`); totality is neither.
* `emptiness_not_computable` — the *dual* Rice instance: the "emptiness" problem
  `{ c | ∀ n, program c diverges on n }` (never halts) is also undecidable.

## Scope / honesty
This proves totality is **not computable**. Totality is in fact `Π₂` (`∀ n, ∃ s`, the
computation halts within `s` steps) and is `Π₂`-complete, hence neither computably
enumerable nor co-c.e.; those sharper classifications are *not* established here.
The result is a faithful, index-based companion to the abstract diagonalization in
`HaltingProblem.lean` (which uses a bespoke oracle model rather than `Code`).

## References
- Rice, H. G. (1953). "Classes of recursively enumerable sets and their decision
  problems." Trans. Amer. Math. Soc. 74, 358–366.
- Rogers, H. (1967). Theory of Recursive Functions and Effective Computability, §14.8.
- Soare, R. (2016). Turing Computability, Springer, §II.4 (the arithmetical hierarchy).
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace TotalityProblem

/-! ## Section 1: The totality property -/

/-- The **totality** property, as a set of partial functions: `f` is total when it
    halts (is defined) on every input. -/
def totalFns : Set (ℕ →. ℕ) := { f | ∀ n, (f n).Dom }

/-- The identity function `n ↦ n` (Mathlib's `Part.some`) is total. It is the witness
    that the totality property is *satisfiable* — the first half of nontriviality. -/
theorem some_mem_totalFns : (fun n => Part.some n) ∈ totalFns := fun _ => trivial

/-- The everywhere-divergent function `n ↦ ⊥` is **not** total: it halts nowhere. This
    is the second half of nontriviality (the property is not universally true). -/
theorem none_notMem_totalFns : (fun _ => (Part.none : Part ℕ)) ∉ totalFns := by
  intro h; exact (h 0)

/-! ## Section 2: The totality problem is undecidable -/

/-- **The Totality Problem is undecidable.** There is no algorithm deciding, from a
    code `c`, whether `eval c` is total (halts on every input).

    This is Rice's theorem applied to the totality property: totality is a semantic
    property of `eval c` and is nontrivial (`some_mem_totalFns`, `none_notMem_totalFns`),
    so it cannot be computable. Concretely, `rice` says a computable semantic property
    that holds of *some* function must hold of *every* function; feeding it the
    everywhere-divergent function forces the false conclusion that it is total. -/
theorem totality_not_computable :
    ¬ ComputablePred (fun c : Code => eval c ∈ totalFns)
  | h => none_notMem_totalFns (ComputablePred.rice totalFns h Nat.Partrec.some Nat.Partrec.none
      some_mem_totalFns)

/-! ## Section 3: The code-level formulation via `rice₂` -/

/-- The set of **total codes**: codes whose evaluated partial function is total. -/
def TotalCodes : Set Code := { c | ∀ n, (eval c n).Dom }

/-- `TotalCodes` is an **extensional** (index-invariant) set of codes: whether a code
    is total depends only on the function it computes. This is the hypothesis of
    `rice₂`. -/
theorem totalCodes_extensional :
    ∀ cf cg : Code, eval cf = eval cg → (cf ∈ TotalCodes ↔ cg ∈ TotalCodes) := by
  intro cf cg he
  simp only [TotalCodes, Set.mem_setOf_eq, he]

/-- `TotalCodes` is **nontrivial**: it is neither empty (some code is total) nor
    everything (some code is not). We exhibit a total code and a non-total code by
    pulling back the two function-level witnesses through `exists_code`. -/
theorem totalCodes_nontrivial : TotalCodes ≠ ∅ ∧ TotalCodes ≠ Set.univ := by
  obtain ⟨ct, hct⟩ := exists_code.mp Nat.Partrec.some
  obtain ⟨cn, hcn⟩ := exists_code.mp Nat.Partrec.none
  constructor
  · intro hempty
    have : ct ∈ TotalCodes := by
      simp only [TotalCodes, Set.mem_setOf_eq, hct]; exact fun _ => trivial
    rw [hempty] at this; exact this
  · intro huniv
    have hcnmem : cn ∈ TotalCodes := huniv ▸ Set.mem_univ cn
    simp only [TotalCodes, Set.mem_setOf_eq, hcn] at hcnmem
    exact (hcnmem 0)

/-- **Code-level totality is undecidable**, via `rice₂`: the computable extensional
    code-sets are exactly `∅` and `Set.univ`, and `TotalCodes` is neither. -/
theorem totality_not_computable_of_codes :
    ¬ ComputablePred (fun c : Code => c ∈ TotalCodes) := by
  intro h
  rcases (ComputablePred.rice₂ TotalCodes totalCodes_extensional).mp h with h0 | h1
  · exact totalCodes_nontrivial.1 h0
  · exact totalCodes_nontrivial.2 h1

/-! ## Section 4: The dual — the emptiness (never-halts) problem -/

/-- The **emptiness** property: `f` diverges on every input (halts nowhere). -/
def emptyFns : Set (ℕ →. ℕ) := { f | ∀ n, ¬ (f n).Dom }

/-- The everywhere-divergent function witnesses that emptiness is satisfiable. -/
theorem none_mem_emptyFns : (fun _ => (Part.none : Part ℕ)) ∈ emptyFns := fun _ h => h

/-- The identity function is **not** empty: it halts (indeed everywhere). -/
theorem some_notMem_emptyFns : (fun n => Part.some n) ∉ emptyFns := by
  intro h; exact (h 0) trivial

/-- **The Emptiness Problem is undecidable.** Deciding whether a program halts on *no*
    input is impossible — the dual Rice instance to totality. -/
theorem emptiness_not_computable :
    ¬ ComputablePred (fun c : Code => eval c ∈ emptyFns)
  | h => some_notMem_emptyFns (ComputablePred.rice emptyFns h Nat.Partrec.none Nat.Partrec.some
      none_mem_emptyFns)

end TotalityProblem
