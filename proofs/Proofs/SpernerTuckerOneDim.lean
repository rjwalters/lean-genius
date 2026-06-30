/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# One-dimensional Tucker's Lemma (combinatorial 1-D Borsuk–Ulam)

This file proves the `n = 1` case of **Tucker's lemma** — equivalently, the
combinatorial core of the **1-dimensional Borsuk–Ulam theorem** — by a direct
sign-change parity argument.

## Setting

The 1-ball `B¹ = [-m, m]` is triangulated by a path of `N + 1` vertices
`0, 1, …, N`, with edges connecting consecutive vertices `i` and `i + 1`
(here `N = 2m`). A *labelling* assigns each vertex a sign from `{+1, -1}`,
which we encode as an element of `ZMod 2` (`+1 ↦ 0`, `-1 ↦ 1`). The labelling
is **antipodal on the boundary** when the two endpoints `0` and `N` receive
opposite signs; under the `ZMod 2` encoding this is exactly `lam 0 ≠ lam N`.

An edge `i` (joining vertices `i` and `i + 1`) is **complementary** when its
two endpoints carry opposite signs: `lam i.castSucc ≠ lam i.succ`.

## Main results

* `TuckerOneDim.complementary_count_cast`: the number of complementary edges,
  cast into `ZMod 2`, equals `lam 0 + lam (Fin.last N)` (a telescoping
  identity — the count of sign changes is the total "displacement" of the
  sign along the path).
* `TuckerOneDim.tucker_one_dim`: with an antipodal boundary, the number of
  complementary edges is **odd**.
* `TuckerOneDim.exists_complementary_edge`: **1-D Tucker** — with an antipodal
  boundary, a complementary edge exists.

## Relationship to the abstract door-counting engine

The parent file `SpernerMathlib4.lean` proves Sperner's lemma for an abstract
`CellComplex` via door-counting parity. For `n = 1` the present result is the
*signed* analogue: complementary edges play the role of "doors", and the
antipodal boundary condition forces an odd count, exactly as an odd boundary
door count forces a panchromatic cell in Sperner.

This is a faithful `n = 1` milestone toward the open question
`sperner-mathlib4-oq-02` (Tucker from door-counting). It does **not** extend
mechanically to `n ≥ 2`: there the complementary-edge count is *not* a parity
invariant, and the standard remedy (Freund–Todd / Prescott–Su path-following
on almost-complementary simplices) is a genuinely different parity engine.

## References

* A. W. Tucker, *Some topological properties of disk and sphere* (1946).
* J. Matoušek, *Using the Borsuk–Ulam Theorem* (2003).

## Tags

Tucker, Borsuk-Ulam, combinatorics, parity, antipodal, sign-change
-/

open Finset

namespace TuckerOneDim

/-- In `ZMod 2`, an element is its own negation. -/
private lemma neg_self : ∀ x : ZMod 2, -x = x := by decide

/-- In `ZMod 2`, every element is its own additive inverse: `x + x = 0`. -/
private lemma add_self : ∀ x : ZMod 2, x + x = 0 := by decide

/-- The complementarity indicator equals the `ZMod 2` sum of the two endpoint
labels: `1` when the signs differ, `0` when they agree. -/
private lemma ite_ne_eq_add :
    ∀ a b : ZMod 2, (if a ≠ b then (1 : ZMod 2) else 0) = a + b := by decide

/-- An edge `i` of the path is **complementary** for the labelling `lam` when
its two endpoints (vertices `i` and `i + 1`) carry opposite signs. -/
def IsComplementary {N : ℕ} (lam : Fin (N + 1) → ZMod 2) (i : Fin N) : Prop :=
  lam i.castSucc ≠ lam i.succ

/-- **Sign-change parity (telescoping form).** The number of complementary
edges, cast into `ZMod 2`, equals the sum of the two boundary labels. This is
the discrete fundamental theorem of calculus: counting sign changes along the
path equals the net change of the sign between the endpoints. -/
theorem complementary_count_cast (N : ℕ) (lam : Fin (N + 1) → ZMod 2) :
    ((univ.filter
      (fun i : Fin N => lam i.castSucc ≠ lam i.succ)).card : ZMod 2)
      = lam 0 + lam (Fin.last N) := by
  -- Extend `lam` to a function on `ℕ` so we can telescope over `range N`.
  set g : ℕ → ZMod 2 := fun k => if h : k < N + 1 then lam ⟨k, h⟩ else 0 with hg
  have hg_cast : ∀ i : Fin N, g i.castSucc = lam i.castSucc := by
    intro i
    simp only [hg, Fin.coe_castSucc]
    rw [dif_pos (by omega)]
    rfl
  have hg_succ : ∀ i : Fin N, g (i.castSucc + 1) = lam i.succ := by
    intro i
    simp only [hg, Fin.coe_castSucc]
    rw [dif_pos (by omega)]
    rfl
  -- Rewrite the cardinality as a `ZMod 2` sum of indicators.
  rw [Finset.card_filter, Nat.cast_sum]
  have hstep : ∀ i : Fin N,
      ((if lam i.castSucc ≠ lam i.succ then 1 else 0 : ℕ) : ZMod 2)
        = g i.castSucc + g (i.castSucc + 1) := by
    intro i
    rw [hg_cast i, hg_succ i, ← ite_ne_eq_add]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  -- Reindex `Fin N` to `range N`, then telescope.
  have hreindex :
      (∑ i : Fin N, (g i.castSucc + g (i.castSucc + 1)))
        = ∑ i ∈ range N, (g i + g (i + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => g k + g (k + 1)) N]
    apply Finset.sum_congr rfl
    intro i _
    simp [Fin.coe_castSucc]
  rw [hreindex]
  -- In `ZMod 2`, `g i + g (i+1) = g (i+1) - g i`, so the sum telescopes.
  have hsub : ∀ i, g i + g (i + 1) = g (i + 1) - g i := by
    intro i
    rw [sub_eq_add_neg, neg_self, add_comm]
  rw [Finset.sum_congr rfl (fun i _ => hsub i), Finset.sum_range_sub g N]
  -- Identify the boundary values.
  have hg0 : g 0 = lam 0 := by
    simp only [hg]; rw [dif_pos (by omega)]; rfl
  have hgN : g N = lam (Fin.last N) := by
    simp only [hg]; rw [dif_pos (by omega)]; rfl
  rw [hg0, hgN, sub_eq_add_neg, neg_self, add_comm]

/-- **1-D Tucker, parity form.** If the boundary labels are antipodal
(`lam 0 ≠ lam (Fin.last N)`), the number of complementary edges is **odd**. -/
theorem tucker_one_dim (N : ℕ) (lam : Fin (N + 1) → ZMod 2)
    (hanti : lam 0 ≠ lam (Fin.last N)) :
    Odd (univ.filter
      (fun i : Fin N => lam i.castSucc ≠ lam i.succ)).card := by
  have hcast := complementary_count_cast N lam
  -- The antipodal condition pins the boundary sum to `1`.
  have hone : lam 0 + lam (Fin.last N) = 1 := by
    have h := ite_ne_eq_add (lam 0) (lam (Fin.last N))
    rw [if_pos hanti] at h
    exact h.symm
  rw [hone] at hcast
  -- `(card : ZMod 2) = 1` forces `card` odd.
  rcases Nat.even_or_odd
      (univ.filter (fun i : Fin N => lam i.castSucc ≠ lam i.succ)).card
      with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := he
    rw [hk] at hcast
    rw [Nat.cast_add, add_self] at hcast
    exact zero_ne_one hcast
  · exact ho

/-- **One-dimensional Tucker's lemma** (combinatorial 1-D Borsuk–Ulam). For any
sign labelling of a path that is antipodal on the boundary, some edge is
complementary: its two endpoints carry opposite signs. -/
theorem exists_complementary_edge (N : ℕ) (lam : Fin (N + 1) → ZMod 2)
    (hanti : lam 0 ≠ lam (Fin.last N)) :
    ∃ i : Fin N, lam i.castSucc ≠ lam i.succ := by
  have hodd := tucker_one_dim N lam hanti
  have hpos : 0 < (univ.filter
      (fun i : Fin N => lam i.castSucc ≠ lam i.succ)).card := by
    obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (mem_filter.mp hi).2⟩

end TuckerOneDim
