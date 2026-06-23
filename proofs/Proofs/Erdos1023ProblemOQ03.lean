/-
Erdős Problem #1023 (OQ-03): Single-layer constructions and an explicit
exponential lower bound for union-free families.

Parent: `Erdos1023Problem.lean` proves the union-free extremal function
satisfies `F(n) = C(n, ⌊n/2⌋)`, with the lower bound coming from the single
*middle* layer (`unionFreeMax_ge_middle`) and the matching upper bound routed
through Problem 447 (`problem_447_solution`, an external input).

This file isolates the part of the story that is fully self-contained and
**axiom-free**: the lower-bound construction. It makes three points.

  1. The middle layer is not special — *every* layer (the family of all
     `k`-element subsets, for any fixed `k`) is an antichain, hence union-free.
     So `F(n) ≥ C(n, k)` for every `k`, generalising the middle-layer bound.

  2. Summing the binomial row and bounding each term by the central one gives
     `2^n ≤ (n+1) · C(n, ⌊n/2⌋)`.

  3. Combining (1) and (2) yields an explicit, axiom-free exponential lower
     bound

        `2^n ≤ (n + 1) · F(n)`,      equivalently   `F(n) ≥ 2^n / (n + 1)`,

     proved purely from the single middle-layer construction and independent of
     the (harder) matching upper bound. This already certifies that `F(n)` grows
     exponentially — the crude pigeonhole `2^n / (n+1)` differs from the true
     `~ √(2/π) · 2^n / √n` only by the polynomial factor `√n / (n+1)`.

## Self-contained
To keep this contribution axiom-free and independent of the parent's asymptotic
section (which carries the 5 axioms routing the *upper* bound through Problem
447), the small amount of lower-bound infrastructure it needs — set families,
`isUnionFree`, `isAntichain`, `antichain_unionFree`, the extremal function
`unionFreeMax`, and the `layer` construction — is re-declared here verbatim from
the parent. Nothing below depends on any axiom: only `Classical.choice`,
`propext`, `Quot.sound` are used.

## Mathlib API used
- `Nat.choose_le_middle` (`Mathlib.Data.Nat.Choose.Basic`)
- `Nat.sum_range_choose` (`Mathlib.Data.Nat.Choose.Sum`)
- `Finset.sum_le_sum`, `Finset.sum_const`, `Finset.card_range`
- `Nat.div_le_div_right`, `Nat.mul_div_cancel_left`

Tags: combinatorics, extremal-set-theory, union-free, antichain, sperner,
      binomial-coefficients, lower-bound
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset

namespace Erdos1023OQ03

/-!
## Lower-bound infrastructure (re-declared from the parent, axiom-free)
-/

/-- A set family is a collection of subsets of `Fin n`. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The union of a subfamily. -/
def familyUnion (F : SetFamily n) : Finset (Fin n) :=
  F.sup id

/-- A set is a union of a subfamily (of size ≥ 2). -/
def isUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyUnion G = A

/-- A family is union-free: no member is the union of other members. -/
def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isUnionOf A (F.erase A)

/-- A family is an antichain if no set contains another. -/
def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- Each element of a subfamily contributes to the union. -/
lemma mem_sub_familyUnion {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    B ⊆ familyUnion F := by
  intro x hx
  simp only [familyUnion]
  exact Finset.mem_sup.mpr ⟨B, hB, hx⟩

/-- Antichains are union-free. -/
theorem antichain_unionFree (F : SetFamily n) : isAntichain F → isUnionFree F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  have hBsubA : ∀ B ∈ G, B ⊆ A := by
    intro B hB
    rw [← hGunion]
    exact mem_sub_familyUnion hB
  have hBeqA : ∀ B ∈ G, B = A := by
    intro B hB
    have hBF : B ∈ F := Finset.mem_of_mem_erase (hGsub hB)
    exact hanti B hBF A hA (hBsubA B hB)
  have : G.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp h
    exact hBC (by rw [hBeqA B hB, hBeqA C hC])
  omega

/-- The set of achievable cardinalities is bounded above by `2^n`. -/
theorem unionFree_sizes_bddAbove (n : ℕ) :
    BddAbove { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k } :=
  ⟨2 ^ n, fun k ⟨F, _, hk⟩ => hk ▸ (Finset.card_le_univ F).trans (by simp)⟩

/-- `F(n)`: maximum size of a union-free family on `{0,…,n-1}`. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }

/-- The `k`-th layer: all `k`-element subsets of `Fin n`. -/
def layer (n k : ℕ) : SetFamily n :=
  (univ.powerset).filter (fun A => A.card = k)

/-- Size of a layer equals the binomial coefficient. -/
theorem layer_card (n k : ℕ) : (layer n k).card = Nat.choose n k := by
  simp [layer]

/-!
## OQ-03 results
-/

/-- **Every layer is an antichain.** The family of all `k`-element subsets of
`Fin n` contains no two distinct comparable sets: if `A ⊆ B` and both have
cardinality `k`, then `A = B`. This generalises the parent's
`middleLayer_antichain` (the `k = n/2` case). -/
theorem layer_antichain (n k : ℕ) : isAntichain (layer n k) := by
  intro A hA B hB hAB
  simp only [layer, mem_filter] at hA hB
  exact Finset.eq_of_subset_of_card_le hAB (hA.2 ▸ hB.2 ▸ le_refl _)

/-- **Every layer is union-free.** Immediate from `layer_antichain` and
`antichain_unionFree`. -/
theorem layer_unionFree (n k : ℕ) : isUnionFree (layer n k) :=
  antichain_unionFree _ (layer_antichain n k)

/-- **Lower bound at every layer.** Each binomial coefficient `C(n, k)` is
realised by a union-free family (the `k`-th layer), so `F(n) ≥ C(n, k)` for
*every* `k`. This strictly generalises the parent's middle-layer bound. -/
theorem unionFreeMax_ge_choose (n k : ℕ) :
    unionFreeMax n ≥ Nat.choose n k := by
  apply le_csSup (unionFree_sizes_bddAbove n)
  exact ⟨layer n k, layer_unionFree n k, layer_card n k⟩

/-- The middle-layer bound, recovered as the `k = n/2` instance of
`unionFreeMax_ge_choose`, confirming the generalisation subsumes it. -/
theorem unionFreeMax_ge_middle (n : ℕ) :
    unionFreeMax n ≥ Nat.choose n (n / 2) :=
  unionFreeMax_ge_choose n (n / 2)

/-- **Row sum bounded by the central term.** The binomial coefficients in row `n`
sum to `2^n`, and each is at most the central coefficient `C(n, ⌊n/2⌋)`, so
`2^n ≤ (n + 1) · C(n, ⌊n/2⌋)`. -/
theorem two_pow_le_succ_mul_central (n : ℕ) :
    2 ^ n ≤ (n + 1) * Nat.choose n (n / 2) := by
  calc 2 ^ n = ∑ k ∈ Finset.range (n + 1), Nat.choose n k := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _k ∈ Finset.range (n + 1), Nat.choose n (n / 2) :=
        Finset.sum_le_sum (fun k _ => Nat.choose_le_middle k n)
    _ = (n + 1) * Nat.choose n (n / 2) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Explicit exponential lower bound (axiom-free).** Purely from the single
middle-layer construction,

  `2^n ≤ (n + 1) · F(n)`.

In particular `F(n)` grows at least like `2^n / (n + 1)` — exponentially —
without invoking the matching (harder) upper bound. -/
theorem unionFreeMax_exponential_lower_bound (n : ℕ) :
    2 ^ n ≤ (n + 1) * unionFreeMax n := by
  refine (two_pow_le_succ_mul_central n).trans ?_
  gcongr
  exact unionFreeMax_ge_middle n

/-- Division form of the exponential lower bound: `2^n / (n + 1) ≤ F(n)`. -/
theorem unionFreeMax_ge_two_pow_div (n : ℕ) :
    2 ^ n / (n + 1) ≤ unionFreeMax n := by
  calc 2 ^ n / (n + 1)
      ≤ ((n + 1) * unionFreeMax n) / (n + 1) :=
        Nat.div_le_div_right (unionFreeMax_exponential_lower_bound n)
    _ = unionFreeMax n := Nat.mul_div_cancel_left _ (Nat.succ_pos n)

#check @layer_antichain
#check @unionFreeMax_ge_choose
#check @unionFreeMax_exponential_lower_bound

end Erdos1023OQ03
