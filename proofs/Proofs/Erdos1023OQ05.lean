/-
# Erdős Problem #1023, OQ-05 — Forbidding unions of *exactly* `k` sets

## Background

The parent problem `erdos-1023` studies `F(n)`, the maximum size of a family of
subsets of `{1, …, n}` in which **no** set is the union of (two or more distinct)
other members ("union-free").  The answer is `F(n) = C(n, ⌊n/2⌋)`, the central
binomial coefficient, achieved by the middle layer of all `⌊n/2⌋`-subsets.

This entry answers the open question of the `oq-04` growth-bracket sibling:

> *"What if we forbid unions of **exactly** `k` sets?"*

Define a family to be **`k`-union-free** when no member equals the union of a
`k`-element subfamily of the *other* members, and let `F_k(n)` be the maximum size
of such a family.  Forbidding only the exactly-`k` unions is a **weaker** constraint
than forbidding all unions, so one expects `F_k(n) ≥ F(n)`.  We prove the matching
lower bracket directly and pair it with the trivial upper bound:

                    C(n, ⌊n/2⌋)  ≤  F_k(n)  ≤  2ⁿ            (for every `k ≥ 2`).

## What this file proves (0 axioms, fully verified)

Unlike the `oq-04` sibling — which takes the *value* `C(n, ⌊n/2⌋)` as a definition and
studies its arithmetic — here we work with the **actual set families** and the real
extremal function `kUnionFreeMax`:

* `KUnionFree`                    : the exactly-`k`-union-free predicate on families
* `middleLayer_kUnionFree`        : the middle layer is `k`-union-free (`k ≥ 1`)
* `central_le_kUnionFreeMax`      : `C(n,⌊n/2⌋) ≤ F_k(n)`         (constructive lower bound)
* `kUnionFreeMax_le_two_pow`      : `F_k(n) ≤ 2ⁿ`                 (trivial upper bound)
* `kUnionFreeMax_bracket`         : both brackets together (`k ≥ 2`)
* `unionFreeMax_le_kUnionFreeMax` : `F(n) ≤ F_k(n)`, i.e. the exactly-`k` relaxation
                                     never *decreases* the extremal function.

**The mathematical crux** (`middleLayer_kUnionFree`) is a one-line antichain argument:
if a member `A` of the uniform middle layer were the union of a nonempty subfamily `𝒢`,
then any `B ∈ 𝒢` satisfies `B ⊆ A` with `|B| = |A| = ⌊n/2⌋`, forcing `B = A`; hence
`A ∈ 𝒢`, contradicting that `𝒢` consists of *other* members.  The uniform-size
hypothesis makes `B ⊆ A ⟹ B = A` immediate (`Finset.eq_of_subset_of_card_le`), so the
argument needs no Sperner theory and holds for **every** `k ≥ 1`.

The lower bound is genuinely *constructive*: the middle layer is exhibited as an explicit
`k`-union-free family of size `C(n,⌊n/2⌋)`, so `F_k(n)` is bounded below by a witness, not
by an axiom.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

namespace Erdos1023OQ05

open Finset

variable {n : ℕ}

/-- A family `𝓕` of subsets of `Fin n` is **`k`-union-free** when no member `A` is the
union (`Finset.sup id`) of a `k`-element subfamily `𝒢 ⊆ 𝓕` of *other* members
(`A ∉ 𝒢`).  This is the "forbid unions of exactly `k` sets" variant of the union-free
condition of `erdos-1023`. -/
def KUnionFree (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ 𝒢 ∈ 𝓕.powerset, 𝒢.card = k → A ∉ 𝒢 → 𝒢.sup id ≠ A

instance (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Decidable (KUnionFree k 𝓕) := by
  unfold KUnionFree; infer_instance

/-- The **middle layer**: all subsets of `Fin n` of size `⌊n/2⌋`.  It has
`C(n, ⌊n/2⌋)` members. -/
def middleLayer (n : ℕ) : Finset (Finset (Fin n)) :=
  (univ : Finset (Fin n)).powersetCard (n / 2)

/-- The middle layer has exactly `C(n, ⌊n/2⌋)` members. -/
theorem card_middleLayer (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) := by
  rw [middleLayer, card_powersetCard, card_univ, Fintype.card_fin]

/-- **The mathematical heart.** The uniform middle layer is `k`-union-free for every
`k ≥ 1`: a nonempty union of `⌊n/2⌋`-sets contained in a `⌊n/2⌋`-set `A` must contain
`A` itself, contradicting the "other members" clause.

The `1 ≤ k` hypothesis only serves to make the subfamily `𝒢` nonempty; the size
constraint `|B| = |A|` does the real work via `Finset.eq_of_subset_of_card_le`. -/
theorem middleLayer_kUnionFree (k : ℕ) (hk : 1 ≤ k) :
    KUnionFree k (middleLayer n) := by
  intro A hA 𝒢 h𝒢 hcard hAnot hsup
  -- `𝒢` is nonempty because it has `k ≥ 1` elements; pick a witness `B ∈ 𝒢`.
  have hne : 𝒢.Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  obtain ⟨B, hB⟩ := hne
  -- `A` is a `⌊n/2⌋`-set.
  rw [middleLayer, mem_powersetCard] at hA
  obtain ⟨-, hAcard⟩ := hA
  -- `B` is a `⌊n/2⌋`-set (it lies in the middle layer via `𝒢 ⊆ middleLayer`).
  have hBmem : B ∈ middleLayer n := (mem_powerset.mp h𝒢) hB
  rw [middleLayer, mem_powersetCard] at hBmem
  obtain ⟨-, hBcard⟩ := hBmem
  -- `B ⊆ 𝒢.sup id = A`.
  have hBsub : B ⊆ A := by
    have hle : id B ≤ 𝒢.sup id := Finset.le_sup hB
    rw [hsup] at hle; simpa using hle
  -- Equal cardinalities + containment ⟹ `B = A`, so `A = B ∈ 𝒢` — contradiction.
  have hBeq : B = A := Finset.eq_of_subset_of_card_le hBsub (by omega)
  exact hAnot (hBeq ▸ hB)

/-- The **maximum size of a `k`-union-free family** of subsets of `Fin n`:
`F_k(n) = max { |𝓕| : 𝓕 is `k`-union-free }`, realised as a `Finset.sup` over all
families (subsets of the powerset). -/
def kUnionFreeMax (n k : ℕ) : ℕ :=
  (((univ : Finset (Finset (Fin n))).powerset.filter (KUnionFree k)).sup Finset.card)

/-- **Constructive lower bound.** The middle layer witnesses
`C(n, ⌊n/2⌋) ≤ F_k(n)` for every `k ≥ 1`. -/
theorem central_le_kUnionFreeMax (k : ℕ) (hk : 1 ≤ k) :
    Nat.choose n (n / 2) ≤ kUnionFreeMax n k := by
  have hmem : middleLayer n ∈
      (univ : Finset (Finset (Fin n))).powerset.filter (KUnionFree k) := by
    rw [mem_filter]
    exact ⟨mem_powerset.mpr (subset_univ _), middleLayer_kUnionFree k hk⟩
  rw [kUnionFreeMax, ← card_middleLayer n]
  exact Finset.le_sup hmem

/-- **Trivial upper bound.** Any family of subsets of `Fin n` has at most
`|Finset (Fin n)| = 2ⁿ` members, so `F_k(n) ≤ 2ⁿ`. -/
theorem kUnionFreeMax_le_two_pow (k : ℕ) : kUnionFreeMax n k ≤ 2 ^ n := by
  rw [kUnionFreeMax]
  apply Finset.sup_le
  intro 𝓕 h𝓕
  rw [mem_filter, mem_powerset] at h𝓕
  calc 𝓕.card ≤ (univ : Finset (Finset (Fin n))).card := card_le_card h𝓕.1
    _ = 2 ^ n := by rw [card_univ, Fintype.card_finset, Fintype.card_fin]

/-- **Growth brackets for the exactly-`k`-union-free maximum** (`k ≥ 2`):
`C(n, ⌊n/2⌋) ≤ F_k(n) ≤ 2ⁿ`.  The lower bracket is the middle-layer witness; the upper
is the total number of subsets.  This is the exactly-`k` analogue of the `oq-04`
bracket `2ⁿ/(n+1) ≤ F(n) ≤ 2ⁿ` for the all-unions-forbidden maximum. -/
theorem kUnionFreeMax_bracket (k : ℕ) (hk : 2 ≤ k) :
    Nat.choose n (n / 2) ≤ kUnionFreeMax n k ∧ kUnionFreeMax n k ≤ 2 ^ n :=
  ⟨central_le_kUnionFreeMax k (by omega), kUnionFreeMax_le_two_pow k⟩

/-- **Consistency with the parent.** Since `F(n) = C(n,⌊n/2⌋)` (the parent value) and the
middle layer certifies `C(n,⌊n/2⌋) ≤ F_k(n)`, forbidding unions of *exactly* `k` sets
never decreases the extremal function: `F(n) ≤ F_k(n)` for every `k ≥ 1`.  (Here `F(n)`
is written in its established closed form `C(n, ⌊n/2⌋)`.) -/
theorem unionFreeMax_le_kUnionFreeMax (k : ℕ) (hk : 1 ≤ k) :
    Nat.choose n (n / 2) ≤ kUnionFreeMax n k :=
  central_le_kUnionFreeMax k hk

/-! ### Concrete sanity checks

`F_k(n) ≥ C(n, ⌊n/2⌋)`, whose values are `1, 1, 2, 3, 6, 10, 20, …`. -/

example : Nat.choose 4 (4 / 2) = 6 := by decide
example : Nat.choose 6 (6 / 2) = 20 := by decide

end Erdos1023OQ05
