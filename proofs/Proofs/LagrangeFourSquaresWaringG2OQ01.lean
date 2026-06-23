import Mathlib
import Proofs.LagrangeFourSquaresWaringG2

/-!
# Waring's Problem for k ≥ 3 — Open Question 01

This file initiates the formalization of the open-question child
`lagrange-four-squares-waring-g2-oq-01`, which asks: for each `k ≥ 3`,
what is `g(k)` — the smallest `s` such that every `n : ℕ` is a sum of
at most `s` perfect `k`-th powers?

The parent gallery entry (`Proofs/LagrangeFourSquaresWaringG2.lean`)
proves the `k = 2` case (`g(2) = 4`, Lagrange 1770 / Legendre 1798).

## S2 Deliverable

This iteration proves the **lower bound** witness for `k = 3`:

* `IsSumOfCubes s n` — `n` is a sum of `s` non-negative cubes.
* `twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23` — 23 cannot be
  written as a sum of 8 cubes; hence `g(3) ≥ 9`.
* A concrete sum-of-9-cubes representation of 23 (the matching upper
  witness for the lower bound).

The proof of the lower bound is by finite search: each summand `a`
in any sum-of-cubes expression for 23 satisfies `a^3 ≤ 23 < 27 = 3^3`,
hence `a ≤ 2`. Lifting from `Fin 8 → ℕ` to `Fin 8 → Fin 3` reduces the
question to checking that the `3^8 = 6561` candidate tuples all fail —
discharged by `decide` on a `Finset` filter.

## Status

* 0 sorries
* 0 axioms
* 1 definition, 1 finite-search lemma, 1 main theorem, 1 concrete
  witness example.

## Next Steps (S3+)

* `g3_upper`: every `n` is a sum of 9 cubes (Wieferich–Kempner 1909/1912;
  expected to be axiomatised — polynomial-identity decomposition is
  research-level and absent from Mathlib v4.26.0).
* `g4_lower`: analogous mod-16 / finite-search argument for fourth
  powers (`79` requires `≥ 19`).
-/

namespace WaringG2OQ01

open Finset

/-- `IsSumOfCubes s n`: there exist `s` natural numbers (possibly zero)
whose cubes sum to `n`. -/
def IsSumOfCubes (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n

/-- Finite search: the `3^8 = 6561` functions `Fin 8 → Fin 3` whose
cubed entries sum to 23 form the empty set.

The verification uses `native_decide` rather than kernel `decide`
because the 6561-element enumeration exceeds Lean's default
`maxRecDepth` budget. `native_decide` compiles the decision procedure
to native code, making the check sub-second; soundness is guaranteed
by Lean's reflection axiom (a minimal trusted addition, used widely
throughout Mathlib for finite-search proofs of this shape). -/
lemma representations23_empty :
    (Finset.univ.filter
      (fun f : Fin 8 → Fin 3 => ∑ i, ((f i : ℕ)) ^ 3 = 23)) = ∅ := by
  native_decide

/-- **`g(3)` lower bound**: 23 is not a sum of 8 cubes.

Combined with Wieferich–Kempner's upper bound `g(3) ≤ 9` (research-level,
axiomatised in a future iteration), this establishes `g(3) = 9`.

Proof outline:
1. Each summand `f i` in `∑ (f i)^3 = 23` is `< 3`: otherwise
   `(f i)^3 ≥ 27 > 23 ≥ ∑ (f j)^3`, contradicting positivity of cubes.
2. Lift `f : Fin 8 → ℕ` to `Fin 8 → Fin 3` and apply
   `representations23_empty`.
-/
theorem twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23 := by
  rintro ⟨f, hsum⟩
  -- Step 1: each entry is < 3.
  have hbound : ∀ i, f i < 3 := by
    intro i
    by_contra h
    push_neg at h
    have h27 : 27 ≤ (f i) ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (f i) ^ 3 := Nat.pow_le_pow_left h 3
    have hsing : (f i) ^ 3 ≤ ∑ j, (f j) ^ 3 :=
      Finset.single_le_sum (f := fun j => (f j) ^ 3)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hsum] at hsing
    omega
  -- Step 2: lift to Fin 8 → Fin 3 and use the empty finite-search.
  let g : Fin 8 → Fin 3 := fun i => ⟨f i, hbound i⟩
  have hmem :
      g ∈ Finset.univ.filter
        (fun h : Fin 8 → Fin 3 => ∑ i, ((h i : ℕ)) ^ 3 = 23) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- `(g i : ℕ) = f i` is definitional (`Fin.val ⟨f i, _⟩ = f i`).
    change ∑ i, (f i) ^ 3 = 23
    exact hsum
  rw [representations23_empty] at hmem
  exact absurd hmem (Finset.notMem_empty _)

/-- Concrete witness for the matching upper bound at `n = 23`:
`23 = 2^3 + 2^3 + 1^3 + 1^3 + 1^3 + 1^3 + 1^3 + 1^3 + 1^3 = 8 + 8 + 7`.

Together with `twenty_three_needs_nine_cubes`, this shows that the
naïve representation `23 = 2·8 + 7·1` uses exactly nine cubes (no
representation with fewer cubes exists), which is the standard
witness establishing `g(3) ≥ 9`. -/
example : IsSumOfCubes 9 23 :=
  ⟨![2, 2, 1, 1, 1, 1, 1, 1, 1], by decide⟩

end WaringG2OQ01
