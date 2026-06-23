import Mathlib.Tactic

/-
# Budan parity engine (P1) — companion to `DescartesRuleOfSignsOQ02.lean`

This file isolates and proves **P1** from the `budan_parity` formalization plan
(`research/problems/descartes-rule-of-signs-oq-02-oq-03/knowledge.md`, S1):

> `parity(signChangesInList l) = (firstNonzeroSign l ≠ lastNonzeroSign l)`

The mathematical heart of P1 is purely combinatorial and has **nothing to do**
with polynomials: for a list whose entries are all `±1`, the number of adjacent
sign changes (`countAdjacentDiffs`) is *even* iff the first and last entries
agree. This is because each adjacent difference *toggles* the running value in a
two-element set, so an even number of toggles returns to the start.

`countAdjacentDiffs` is re-declared here **verbatim** from
`DescartesRuleOfSignsOQ02.lean:130` so this file is self-contained and
independently checkable; the proved lemma drops into the main file unchanged
(same definition, same namespace target).

## How this feeds the axiom

In the main file, `signChangesInList l = countAdjacentDiffs (signs l)` where
`signs l := (l.filter (· ≠ 0)).map (fun x => if x > 0 then 1 else -1)` takes
values in `{1, -1}`. Hence `countAdjacentDiffs_parity` below applies directly
to give `parity(signChangesInList l) = [firstSign ≠ lastSign]`, which is P1.
P2 then identifies first sign `= sign p(x)` and last sign `= sign(n!·leadingCoeff)`
(sign-constant in `x`); P3 supplies the FTA content
`[sign p(a) ≠ sign p(b)] ⟺ Odd(rootsInInterval p a b)`.

Status: build-pending (Docker + Aristotle both unavailable 2026-06-15),
UNREGISTERED (not added to the gallery registry).
-/

namespace BudanParityEngine

/-- Count adjacent pairs that differ in a list of integers.
    (Verbatim copy of `BudanTheorem.countAdjacentDiffs`.) -/
def countAdjacentDiffs : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if a ≠ b then 1 else 0) + countAdjacentDiffs (b :: rest)

@[simp] theorem countAdjacentDiffs_nil : countAdjacentDiffs [] = 0 := rfl
@[simp] theorem countAdjacentDiffs_singleton (a : ℤ) : countAdjacentDiffs [a] = 0 := rfl

/-- **P1 (parity engine).** For a nonempty list `a :: t` whose entries are all
`±1`, the number of adjacent sign changes is even iff the head equals the last
entry. Equivalently, `countAdjacentDiffs (a :: t) % 2 = [head ≠ last]`.

The proof is structural induction on the tail; the only non-formal step is that
in a two-element value set `{1, -1}`, "`a` differs from `b`" XOR "`b` differs
from the last" equals "`a` differs from the last" — discharged by `split_ifs`
on the concrete `±1` cases plus `omega`. -/
theorem countAdjacentDiffs_parity :
    ∀ (a : ℤ) (t : List ℤ), (∀ y ∈ a :: t, y = 1 ∨ y = -1) →
      countAdjacentDiffs (a :: t) % 2 =
        (if a = (a :: t).getLast (List.cons_ne_nil a t) then 0 else 1)
  | a, [], _ => by
      have hg : ([a] : List ℤ).getLast (List.cons_ne_nil a []) = a := rfl
      simp [countAdjacentDiffs, hg]
  | a, b :: rest, hpm => by
      -- last entry of the whole list = last entry of the tail; name it `z`
      have hlast : (a :: b :: rest).getLast (List.cons_ne_nil a (b :: rest))
          = (b :: rest).getLast (List.cons_ne_nil b rest) :=
        List.getLast_cons (List.cons_ne_nil b rest)
      obtain ⟨z, hz_eq⟩ :
          ∃ z, (b :: rest).getLast (List.cons_ne_nil b rest) = z := ⟨_, rfl⟩
      have hz_mem : z ∈ b :: rest := by
        rw [← hz_eq]; exact List.getLast_mem _
      -- membership ⇒ each of a, b, z is ±1
      have ha : a = 1 ∨ a = -1 := hpm a (List.mem_cons_self _ _)
      have hb : b = 1 ∨ b = -1 :=
        hpm b (List.mem_cons_of_mem a (List.mem_cons_self _ _))
      have hzpm : z = 1 ∨ z = -1 := hpm z (List.mem_cons_of_mem a hz_mem)
      -- induction hypothesis on the tail
      have ih := countAdjacentDiffs_parity b rest
        (fun y hy => hpm y (List.mem_cons_of_mem a hy))
      rw [hz_eq] at ih
      -- unfold one step of the count, push getLast to `z`
      simp only [countAdjacentDiffs]
      rw [hlast, hz_eq]
      -- `countAdjacentDiffs (b :: rest)` is an opaque atom shared by `ih` and the
      -- goal; `omega` pins its parity from `ih`. Case-bash the ±1 endpoints.
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        rcases hzpm with rfl | rfl <;> split_ifs at ih ⊢ <;> omega

end BudanParityEngine
