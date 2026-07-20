import Mathlib
import Proofs.Erdos870Problem

/-
# Erdős #870 — the representation count is degenerate as defined
# (erdos-870-incomplete-01)

## Finding

`Erdos870Problem.lean` leaves two `sorry`s — `naturals_basis`
(`IsAdditiveBasis NaturalNumbers 1`) and the `basis_subset_reps` inheritance
step — both of which reduce to proving `representationCount A k n ≥ 1`.

**These sorries cannot be discharged honestly: they assert a false statement.**
The culprit is the definition

```
structure KRepresentation (A) (k n) where
  terms : Finset ℕ
  count : ℕ → ℕ           -- unconstrained off `terms`
  sum_eq : terms.sum count = n
  ...
noncomputable def representationCount A k n := Nat.card {rep : KRepresentation A k n // True}
```

The field `count : ℕ → ℕ` is a *total* function whose values **off** `terms` are
unconstrained (`sum_eq` only pins `∑_{terms} count`). So whenever a single
representation exists, perturbing `count` at any point outside `terms` yields
infinitely many distinct representations — the representation type is infinite,
hence `Nat.card = 0`. And if none exists the type is empty, again `Nat.card = 0`.
Either way `representationCount A k n = 0`, so `IsAdditiveBasis A k`
(`∃ n₀, ∀ n ≥ n₀, representationCount ≥ 1`) is **unsatisfiable for every `A`, `k`**.

## Results (namespace `Erdos870`)

1. `representationCount_eq_zero` — `representationCount A k n = 0` unconditionally.

2. `not_isAdditiveBasis` — consequently `¬ IsAdditiveBasis A k` for every `A`, `k`.

The fix (out of scope here, a definition change to the parent) is to make `count`
finitely supported — e.g. `count : ℕ →₀ ℕ` with `count.support ⊆ terms`, or drop
`count` and sum a multiset. Until then the file's basis theory is vacuous and the
two sorries should not be "closed". This is the honest resolution of the node.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

open Finset

namespace Erdos870

/-- **The representation count is identically zero as defined.** The unconstrained
total field `count : ℕ → ℕ` makes the representation type infinite whenever it is
nonempty (perturb `count` off `terms`), and `Nat.card` of an infinite type is `0`. -/
theorem representationCount_eq_zero (A : AdditiveSet) (k n : ℕ) :
    representationCount A k n = 0 := by
  rw [representationCount]
  rcases isEmpty_or_nonempty (KRepresentation A k n) with he | hne
  · -- No representation: the subtype is empty.
    rw [Nat.card_eq_zero]
    exact Or.inl ⟨fun x => he.false x.1⟩
  · -- A representation exists ⟹ infinitely many ⟹ Nat.card = 0.
    obtain ⟨r⟩ := hne
    -- Pick a point `w ∉ r.terms` and perturb `r.count` there.
    obtain ⟨w, hw⟩ : ∃ w, w ∉ r.terms :=
      ⟨r.terms.sup id + 1, by
        intro hmem
        have hle := Finset.le_sup (f := id) hmem
        simp only [id_eq] at hle
        omega⟩
    have hsum : ∀ m : ℕ, (r.terms.sum (Function.update r.count w m)) = n := by
      intro m
      have hcongr : r.terms.sum (Function.update r.count w m) = r.terms.sum r.count := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxw : x ≠ w := by rintro rfl; exact hw hx
        rw [Function.update_apply, if_neg hxw]
      rw [hcongr]; exact r.sum_eq
    -- The map `m ↦ (perturbed rep)` injects `ℕ` into the subtype.
    let g : ℕ → { rep : KRepresentation A k n // True } := fun m =>
      ⟨{ terms := r.terms, count := Function.update r.count w m,
         sum_eq := hsum m, bound := r.bound, subset := r.subset }, trivial⟩
    have hg : Function.Injective g := by
      intro m m' hmm'
      -- Equal subtype values ⟹ equal `count` fields ⟹ equal at `w` ⟹ `m = m'`.
      have h2 : (g m).val = (g m').val := Subtype.ext_iff.mp hmm'
      have hcount : Function.update r.count w m = Function.update r.count w m' :=
        congrArg KRepresentation.count h2
      have hval := congrFun hcount w
      simpa using hval
    haveI : Infinite { rep : KRepresentation A k n // True } :=
      Infinite.of_injective g hg
    exact Nat.card_eq_zero_of_infinite

/-- Consequently the basis predicate is unsatisfiable: no set is an additive basis
of any order under the current (degenerate) `representationCount`. -/
theorem not_isAdditiveBasis (A : AdditiveSet) (k : ℕ) : ¬ IsAdditiveBasis A k := by
  rintro ⟨n₀, h⟩
  have h1 := h n₀ (le_refl n₀)
  rw [representationCount_eq_zero] at h1
  exact absurd h1 (by norm_num)

end Erdos870
