/-
# Relativized Halting — the iterated jump and the strict degree hierarchy (OQ-03b)

**Research entry: halting-problem-oq-03, Session S12.**

Parent question (OQ-03 of `halting-problem`): "Can interactive systems
(human + machine) solve undecidable problems?" Session S10 built the
OracleCode bridge (`Proofs/RelativizedHaltingCodes.lean`): a Gödel-numbered
machine model matching Mathlib's `Nat.RecursiveIn`, the Turing jump
`jumpSet o`, and Post's 1944 theorem in both halves — the jump escapes its
oracle (`jump_not_recursiveIn`, S10) and the oracle is computable from its
jump (`oracleFun_recursiveIn_jumpCharFun`, S11), packaged as
`oracle_lt_jump : o <ᵀ o′`.

This file climbs: it **iterates** the jump and proves the resulting tower
is strictly increasing at every level, for every base oracle. This is the
engine of the arithmetical hierarchy (OQ-03b): the sets Σ⁰ₙ are, by Post's
hierarchy theorem, exactly the sets enumerable from the (n−1)-st jump of ∅,
and strictness of the jump tower is exactly the strictness Σ⁰ₙ ⊊ Σ⁰ₙ₊₁ in
degree form.

## What is proved

1. `jumpChar o : ℕ → Bool` — the jump repackaged as a Bool-valued oracle
   (classically), with the bridge `oracleFun_jumpChar :
   oracleFun (jumpChar o) = jumpCharFun o` that lets the jump be fed back
   into itself.
2. `jumpIterChar o n` — the `n`-fold iterated jump `o⁽ⁿ⁾`:
   `o⁽⁰⁾ = o`, `o⁽ⁿ⁺¹⁾ = (o⁽ⁿ⁾)′`.
3. **Strict hierarchy** (`jump_hierarchy_strict`): for every base oracle
   `o` and all `m < n`, `o⁽ᵐ⁾ ≤ᵀ o⁽ⁿ⁾` and `¬ o⁽ⁿ⁾ ≤ᵀ o⁽ᵐ⁾`. One
   application of Post strictness per level, glued by transitivity of `≤ᵀ`.
4. **Degree form**: `jumpDegree o : ℕ → TuringDegree` is strictly monotone
   (`jumpDegree_strictMono`), hence ℕ order-embeds into the Turing degrees
   (`jumpOrderEmbedding : ℕ ↪o TuringDegree`).
5. **`Infinite TuringDegree`** — an instance Mathlib does not yet have:
   its `Mathlib.Computability.TuringDegree` (Duve–Roth, 2025) stops at the
   partial order. The classical tower over the computable base oracle
   `fun _ => false` (i.e. ∅ <ᵀ ∅′ <ᵀ ∅″ <ᵀ ⋯, `classical_jump_tower_strict`,
   base computable by `oracleFun_false_partrec`) exhibits infinitely many
   pairwise distinct degrees.

## Proof economy

All the recursion-theoretic content was paid for in S10/S11; this file is
pure order-theoretic glue — but glue that only becomes available once the
jump is Bool-valued (`jumpChar`), because `jumpSet : Set ℕ` and
`jumpCharFun : ℕ →. ℕ` cannot be fed back into `evalO`'s oracle slot.
The bridge lemma `oracleFun_jumpChar` is where the classical `decide`
meets the classical `if`: both sides are `Part.some` of the same
case-split on jump membership.

## References

* Post, E.L. (1944). *Recursively enumerable sets of positive integers and
  their decision problems.* Bull. AMS 50(5). (The jump and its strictness.)
* Kleene, S.C., Post, E.L. (1954). *The upper semi-lattice of degrees of
  recursive unsolvability.* Ann. Math. 59. (The degree hierarchy.)
* Soare, R.I. (1987). *Recursively Enumerable Sets and Degrees*, ch. III–IV.
* Odifreddi, P. (1989). *Classical Recursion Theory*, ch. II–IV.
* Mathlib: `Mathlib.Computability.RecursiveIn`,
  `Mathlib.Computability.TuringDegree` (Duve–Roth, 2025).

0 axioms, 0 sorries.
-/

import Mathlib.Computability.RecursiveIn
import Mathlib.Computability.TuringDegree
import Mathlib.Order.Hom.Basic
import Proofs.RelativizedHaltingCodes

namespace RelativizedHaltingHierarchy

open RelativizedHaltingCodes
open scoped Computability

/-! ### Section 1. The Bool-valued jump

`jumpSet o : Set ℕ` and `jumpCharFun o : ℕ →. ℕ` (S10/S11) describe the jump
but cannot serve as the oracle of a further machine — `evalO` wants
`ℕ → Bool`. Classically repackage. -/

open Classical in
/-- The characteristic function of the Turing jump, as a Bool-valued oracle:
`jumpChar o e = true` iff the `e`-th machine with oracle `o` halts on its own
index. This is the form that can be fed back into `evalO`/`oracleFun`, making
iteration possible. -/
noncomputable def jumpChar (o : ℕ → Bool) : ℕ → Bool :=
  fun e => decide (e ∈ jumpSet o)

open Classical in
/-- The bridge: packaging `jumpChar o` as a partial-function oracle gives
exactly the `jumpCharFun o` of S11. Both sides are `Part.some` of the same
classical case split on jump membership. -/
theorem oracleFun_jumpChar (o : ℕ → Bool) :
    oracleFun (jumpChar o) = jumpCharFun o := by
  funext e
  show Part.some (cond (decide (e ∈ jumpSet o)) 1 0)
      = Part.some (if e ∈ jumpSet o then 1 else 0)
  by_cases h : e ∈ jumpSet o
  · rw [decide_eq_true h, if_pos h]; rfl
  · rw [decide_eq_false h, if_neg h]; rfl

/-! ### Section 2. The iterated jump -/

/-- The `n`-fold iterated jump `o⁽ⁿ⁾`: `jumpIterChar o 0 = o` and
`jumpIterChar o (n + 1) = jumpChar (jumpIterChar o n)`. -/
noncomputable def jumpIterChar (o : ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => o
  | n + 1 => jumpChar (jumpIterChar o n)

@[simp]
theorem jumpIterChar_zero (o : ℕ → Bool) : jumpIterChar o 0 = o := rfl

theorem jumpIterChar_succ (o : ℕ → Bool) (n : ℕ) :
    jumpIterChar o (n + 1) = jumpChar (jumpIterChar o n) := rfl

/-- The `(n+1)`-st level, packaged as a partial-function oracle, is the
`jumpCharFun` of the `n`-th level — the handle on which S11's
`oracle_lt_jump` applies. -/
theorem oracleFun_jumpIterChar_succ (o : ℕ → Bool) (n : ℕ) :
    oracleFun (jumpIterChar o (n + 1)) = jumpCharFun (jumpIterChar o n) :=
  oracleFun_jumpChar (jumpIterChar o n)

/-! ### Section 3. Strictness at every level

One application of Post's strictness (`oracle_lt_jump`, S10+S11) per level,
glued along the tower by reflexivity and transitivity of `≤ᵀ`. -/

/-- Each level of the tower sits strictly below the next:
`o⁽ⁿ⁾ <ᵀ o⁽ⁿ⁺¹⁾`. Immediate from Post strictness at the `n`-th level. -/
theorem jumpIter_lt_succ (o : ℕ → Bool) (n : ℕ) :
    oracleFun (jumpIterChar o n) ≤ᵀ oracleFun (jumpIterChar o (n + 1)) ∧
      ¬ oracleFun (jumpIterChar o (n + 1)) ≤ᵀ oracleFun (jumpIterChar o n) := by
  rw [oracleFun_jumpIterChar_succ]
  exact oracle_lt_jump (jumpIterChar o n)

/-- Monotonicity along the tower: `m ≤ n → o⁽ᵐ⁾ ≤ᵀ o⁽ⁿ⁾`. -/
theorem jumpIter_mono (o : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    oracleFun (jumpIterChar o m) ≤ᵀ oracleFun (jumpIterChar o n) := by
  induction h with
  | refl => exact TuringReducible.refl _
  | step _ ih => exact ih.trans (jumpIter_lt_succ o _).1

/-- No level computes any strictly higher level: `m < n → ¬ o⁽ⁿ⁾ ≤ᵀ o⁽ᵐ⁾`.
If it did, then `o⁽ᵐ⁺¹⁾ ≤ᵀ o⁽ⁿ⁾ ≤ᵀ o⁽ᵐ⁾` would collapse the `m`-th step,
contradicting Post strictness there. -/
theorem not_jumpIter_le_of_lt (o : ℕ → Bool) {m n : ℕ} (h : m < n) :
    ¬ oracleFun (jumpIterChar o n) ≤ᵀ oracleFun (jumpIterChar o m) :=
  fun hred => (jumpIter_lt_succ o m).2 ((jumpIter_mono o h).trans hred)

/-- **The jump hierarchy is strict** (OQ-03b, degree engine): for every base
oracle `o` and all `m < n`, the `m`-th iterated jump is computable from the
`n`-th but not conversely — `o⁽ᵐ⁾ <ᵀ o⁽ⁿ⁾`. -/
theorem jump_hierarchy_strict (o : ℕ → Bool) {m n : ℕ} (h : m < n) :
    oracleFun (jumpIterChar o m) ≤ᵀ oracleFun (jumpIterChar o n) ∧
      ¬ oracleFun (jumpIterChar o n) ≤ᵀ oracleFun (jumpIterChar o m) :=
  ⟨jumpIter_mono o (Nat.le_of_lt h), not_jumpIter_le_of_lt o h⟩

/-! ### Section 4. The tower in the Turing degrees

Mathlib's `TuringDegree` (the antisymmetrization of `≤ᵀ`) currently carries
only its partial order. The tower gives it structure: ℕ order-embeds, so
there are infinitely many Turing degrees. -/

/-- The Turing degree of the `n`-th iterated jump of `o`. -/
noncomputable def jumpDegree (o : ℕ → Bool) (n : ℕ) : TuringDegree :=
  toAntisymmetrization TuringReducible (oracleFun (jumpIterChar o n))

theorem jumpDegree_le_of_le (o : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    jumpDegree o m ≤ jumpDegree o n :=
  jumpIter_mono o h

/-- The degree of the `n`-th jump is strictly monotone in `n`. -/
theorem jumpDegree_strictMono (o : ℕ → Bool) : StrictMono (jumpDegree o) := by
  intro m n h
  refine lt_iff_le_not_ge.mpr ⟨jumpDegree_le_of_le o (Nat.le_of_lt h), fun hred => ?_⟩
  exact not_jumpIter_le_of_lt o h hred

/-- **ℕ order-embeds into the Turing degrees**: the iterated-jump tower over
any base oracle is an infinite strictly increasing chain of degrees. -/
noncomputable def jumpOrderEmbedding (o : ℕ → Bool) : ℕ ↪o TuringDegree :=
  OrderEmbedding.ofStrictMono (jumpDegree o) (jumpDegree_strictMono o)

/-- **There are infinitely many Turing degrees** — an instance absent from
Mathlib's `Mathlib.Computability.TuringDegree`. Witnessed by the classical
jump tower over the computable base oracle. -/
instance : Infinite TuringDegree :=
  Infinite.of_injective (jumpDegree fun _ => false)
    (jumpDegree_strictMono fun _ => false).injective

/-! ### Section 5. The classical tower ∅ <ᵀ ∅′ <ᵀ ∅″ <ᵀ ⋯

Specializing the base to the trivially computable oracle `fun _ => false`
gives the unrelativized halting hierarchy: level 0 is computable, level 1 is
the (self-application form of the) halting problem, level `n` is the `n`-th
classical jump. -/

/-- The base of the classical tower is computable: `oracleFun (fun _ => false)`
is the constant partial function `fun _ => Part.some 0`. -/
theorem oracleFun_false_partrec : Partrec (oracleFun fun _ => false) :=
  Partrec.const' (Part.some 0)

/-- **The classical jump tower is strict**: `∅⁽ᵐ⁾ <ᵀ ∅⁽ⁿ⁾` for `m < n` —
the degree-form backbone of the arithmetical hierarchy's strictness
(Σ⁰ₙ ⊊ Σ⁰ₙ₊₁ via Post's hierarchy theorem). -/
theorem classical_jump_tower_strict {m n : ℕ} (h : m < n) :
    oracleFun (jumpIterChar (fun _ => false) m)
        ≤ᵀ oracleFun (jumpIterChar (fun _ => false) n) ∧
      ¬ oracleFun (jumpIterChar (fun _ => false) n)
          ≤ᵀ oracleFun (jumpIterChar (fun _ => false) m) :=
  jump_hierarchy_strict _ h

end RelativizedHaltingHierarchy
