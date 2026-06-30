import Mathlib

/-
# Erdős #1023 OQ-01 / OQ-01: The LYM inequality and the antichain extremal value

## The Open Question (parent erdos-1023-oq-01, first open question)

The parent file proves the union-free / 2-union-free extremal value `F(n) = C(n, ⌊n/2⌋)` but
leaves the hard half — the Erdős–Kleitman upper bound — as an `axiom`
(`problem_447_solution`). The open question asks:

> **Prove `problem_447_solution` without axioms using the LYM inequality**
> `∑_{A ∈ F} 1/C(n,|A|) ≤ 1`.

## What this file does (and its honest scope)

The **Lubell–Yamamoto–Meshalkin inequality** and **Sperner's theorem** are both in Mathlib
(`lubell_yamamoto_meshalkin_inequality_sum_inv_choose`, `IsAntichain.sperner`). LYM bounds an
*antichain*. We use it to prove, fully axiom-free, the **antichain** analogue of Problem 447:

* `lym_inequality`  — the LYM inequality in the parent's vocabulary: `∑_{A∈F} 1/C(n,|A|) ≤ 1`;
* `sperner_bound`   — any antichain in `2^[n]` has size `≤ C(n, ⌊n/2⌋)`;
* `antichainMax_eq` — the maximum antichain size is **exactly** `C(n, ⌊n/2⌋)`, the middle layer
  being a witness.

Antichains are 2-union-free (a union of two distinct members strictly contains each, so it
cannot be a member of an antichain), so this also discharges, axiom-free, the **lower bound**
of `problem_447_solution`: `C(n,⌊n/2⌋) ≤ sup{2-union-free sizes}` (`twoUnionFree_max_ge_middle`).

**Honest gap.** LYM does *not* close the full question. A 2-union-free family need not be an
antichain (it may contain comparable pairs) and can be strictly larger; the statement that no
2-union-free family exceeds `C(n,⌊n/2⌋)` is the genuinely deeper Erdős–Kleitman content, which
is *not* a corollary of LYM alone. So `problem_447_solution` keeps its upper-bound half as the
open analytic core; what LYM buys, axiom-free, is the complete antichain theorem and the
matching lower bound.

Tags: combinatorics, set-families, lym-inequality, sperner, antichain, erdos, extremal
-/

namespace Erdos1023OQ01OQ01

open Finset

/-- A set family on `[n] = Fin n`. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- A family is an antichain: no member contains another. (Parent's `isAntichain`.) -/
def isAntichain {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- `A` is the union of two distinct members `B, C ≠ A`. (Parent's `isTwoUnionOf`.) -/
def isTwoUnionOf {n : ℕ} (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ B C : Finset (Fin n), B ∈ F ∧ C ∈ F ∧ B ≠ C ∧ A ≠ B ∧ A ≠ C ∧ B ∪ C = A

/-- A family is 2-union-free. (Parent's `isTwoUnionFree`.) -/
def isTwoUnionFree {n : ℕ} (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isTwoUnionOf A F

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: BRIDGE TO MATHLIB'S `IsAntichain`

The parent's order-theoretic `isAntichain` is exactly Mathlib's `IsAntichain (· ⊆ ·)`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The parent's `isAntichain` coincides with Mathlib's `IsAntichain (· ⊆ ·)`, unlocking
    the entire LYM/Sperner toolbox. -/
theorem toMathlibAntichain {n : ℕ} {F : SetFamily n} (h : isAntichain F) :
    IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) :=
  fun _ ha _ hb hne hsub => hne (h _ ha _ hb hsub)

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE LYM INEQUALITY AND SPERNER'S THEOREM (axiom-free, from Mathlib)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **The Lubell–Yamamoto–Meshalkin inequality** in the parent's vocabulary: for an antichain
    `F` in `2^[n]`, `∑_{A∈F} 1/C(n,|A|) ≤ 1`. This is the exact tool named in the open
    question. Restatement of Mathlib's `lubell_yamamoto_meshalkin_inequality_sum_inv_choose`. -/
theorem lym_inequality {n : ℕ} (F : SetFamily n) (h : isAntichain F) :
    ∑ A ∈ F, ((Nat.choose n A.card : ℚ))⁻¹ ≤ 1 := by
  have := lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜 := ℚ) (toMathlibAntichain h)
  simpa [Fintype.card_fin] using this

/-- **Sperner's theorem**: any antichain in `2^[n]` has at most `C(n, ⌊n/2⌋)` members.
    The LYM inequality, summed against the largest binomial coefficient, gives this bound.
    Restatement of Mathlib's `IsAntichain.sperner`. -/
theorem sperner_bound {n : ℕ} (F : SetFamily n) (h : isAntichain F) :
    F.card ≤ Nat.choose n (n / 2) := by
  have := IsAntichain.sperner (toMathlibAntichain h)
  simpa [Fintype.card_fin] using this

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE MIDDLE LAYER ATTAINS THE BOUND

The ⌊n/2⌋-subsets form an antichain of size C(n, ⌊n/2⌋), so Sperner's bound is sharp.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The middle layer: all `⌊n/2⌋`-element subsets of `[n]`. -/
def middle (n : ℕ) : SetFamily n := Finset.univ.powersetCard (n / 2)

/-- The middle layer has exactly `C(n, ⌊n/2⌋)` members. -/
theorem middle_card (n : ℕ) : (middle n).card = Nat.choose n (n / 2) := by
  rw [middle, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The middle layer is an antichain: distinct sets of equal cardinality are incomparable. -/
theorem middle_antichain (n : ℕ) : isAntichain (middle n) := by
  intro A hA B hB hAB
  rw [middle, Finset.mem_powersetCard] at hA hB
  exact Finset.eq_of_subset_of_card_le hAB (le_of_eq (hB.2.trans hA.2.symm))

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE ANTICHAIN EXTREMAL VALUE — EXACTLY C(n, ⌊n/2⌋)
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The maximum size of an antichain in `2^[n]`. -/
noncomputable def antichainMax (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ F : SetFamily n, isAntichain F ∧ F.card = m }

theorem antichain_sizes_bddAbove (n : ℕ) :
    BddAbove { m : ℕ | ∃ F : SetFamily n, isAntichain F ∧ F.card = m } :=
  ⟨Fintype.card (Finset (Fin n)), fun _ ⟨F, _, hm⟩ => hm ▸ Finset.card_le_univ F⟩

theorem antichain_sizes_nonempty (n : ℕ) :
    Set.Nonempty { m : ℕ | ∃ F : SetFamily n, isAntichain F ∧ F.card = m } :=
  ⟨0, ∅, fun A hA => absurd hA (Finset.notMem_empty A), Finset.card_empty⟩

/-- **The antichain analogue of Problem 447, axiom-free.** The maximum antichain size in
    `2^[n]` is exactly `C(n, ⌊n/2⌋)`: Sperner's theorem (`≤`) and the middle layer (`≥`). -/
theorem antichainMax_eq (n : ℕ) : antichainMax n = Nat.choose n (n / 2) := by
  apply le_antisymm
  · apply csSup_le (antichain_sizes_nonempty n)
    rintro m ⟨F, hF, rfl⟩
    exact sperner_bound F hF
  · apply le_csSup (antichain_sizes_bddAbove n)
    exact ⟨middle n, middle_antichain n, middle_card n⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: BRIDGE TO PROBLEM 447 — THE LOWER BOUND, AXIOM-FREE

Antichains are 2-union-free, so the middle layer gives `C(n,⌊n/2⌋) ≤ sup{2-union-free sizes}`.
This discharges, without axioms, the lower-bound half of `problem_447_solution`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Antichains are 2-union-free: a union of two distinct members `B, C` strictly contains
    `B`, so `B = B∪C` would force `B ⊆ B∪C ∈ F` to equal `B∪C`, contradicting `B ≠ B∪C`. -/
theorem antichain_twoUnionFree {n : ℕ} (F : SetFamily n) (h : isAntichain F) :
    isTwoUnionFree F := by
  rintro A hA ⟨B, C, hB, _, _, hAB, _, hunion⟩
  have hBsub : B ⊆ A := by rw [← hunion]; exact Finset.subset_union_left
  exact hAB (h B hB A hA hBsub).symm

/-- The middle layer is 2-union-free. -/
theorem middle_twoUnionFree (n : ℕ) : isTwoUnionFree (middle n) :=
  antichain_twoUnionFree _ (middle_antichain n)

/-- **Lower bound of Problem 447, axiom-free.** `C(n, ⌊n/2⌋) ≤ sup{2-union-free family sizes}`,
    witnessed by the middle layer. The parent's `problem_447_solution` axiom claims equality;
    this proves the `≥` half without any axiom. The remaining `≤` half (no 2-union-free family
    exceeds `C(n,⌊n/2⌋)`) is the deeper Erdős–Kleitman content, not a corollary of LYM. -/
theorem twoUnionFree_max_ge_middle (n : ℕ) :
    Nat.choose n (n / 2) ≤
      sSup { m : ℕ | ∃ F : SetFamily n, isTwoUnionFree F ∧ F.card = m } := by
  apply le_csSup
  · exact ⟨Fintype.card (Finset (Fin n)), fun _ ⟨F, _, hm⟩ => hm ▸ Finset.card_le_univ F⟩
  · exact ⟨middle n, middle_twoUnionFree n, middle_card n⟩

end Erdos1023OQ01OQ01

/-
## Summary

Engaging parent erdos-1023-oq-01's first open question — discharge `problem_447_solution` via
the LYM inequality.

**LYM and Sperner, axiom-free** (from Mathlib, restated in the parent's vocabulary):
- `lym_inequality`:  `∑_{A∈F} 1/C(n,|A|) ≤ 1` for an antichain `F`  (the named tool)
- `sperner_bound`:   antichain `F ⟹ |F| ≤ C(n, ⌊n/2⌋)`
- `antichainMax_eq`: the maximum antichain size is exactly `C(n, ⌊n/2⌋)`

**Bridge to Problem 447** (antichains ⊆ 2-union-free):
- `antichain_twoUnionFree`, `middle_twoUnionFree`
- `twoUnionFree_max_ge_middle`: `C(n,⌊n/2⌋) ≤ sup{2-union-free sizes}` — the lower-bound half
  of the parent axiom, now axiom-free.

**Honest scope.** LYM gives the complete *antichain* extremal theorem and the matching lower
bound for 2-union-free families. The upper bound for 2-union-free families (which need not be
antichains) is the deeper Erdős–Kleitman theorem and is not implied by LYM alone, so the
upper-bound half of `problem_447_solution` remains the open analytic core.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
