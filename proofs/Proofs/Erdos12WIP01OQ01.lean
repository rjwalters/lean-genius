import Mathlib

/-
# Erdős Problem #12: Quantitative Residue Bound for Divisibility-Free Sets

## Problem (follow-up OQ-01 to `erdos-12-wip-01`)
A set `A ⊆ ℕ` is **divisibility-free** when there are no distinct `a, b, c ∈ A`
with `b, c > a` and `a ∣ (b + c)`.  The parent leaf `erdos-12-wip-01` isolated
the *residue-level obstruction* `no_antipodal_pair`: for a fixed `a ∈ A`, no two
distinct larger elements of `A` are antipodal mod `a` (sum `≡ 0 mod a`).

This file **sharpens that qualitative obstruction into a quantitative bound**,
the first step toward a self-contained density argument:

> For `a ∈ A` (with `0 < a`), the residues mod `a` occupied by the larger
> elements of `A` fill **at most about half** of the `a` residue classes —
> precisely at most `a / 2 + 1` of them.

## Proof idea
The residues occupied by larger elements form a set `R ⊆ {0, …, a-1}` with no
antipodal pair `{r, a-r}` (two residues summing to `a` would come from two
distinct larger elements, forbidden by `no_antipodal_pair`).  The **folding map**
`fold r = min r (a - r)` sends `{0, …, a-1}` into `{0, …, ⌊a/2⌋}` and is
*injective on `R`*: the only collision `fold r = fold s` with `r ≠ s` is the
antipodal pair `s = a - r`, which `R` avoids.  An injection into a set of size
`a / 2 + 1` gives the bound.

## What this file proves
* `fold_le_half` / `fold_mem_range` — the folding map lands in `{0, …, ⌊a/2⌋}`.
* `fold_eq_iff` — `fold r = fold s` (for `r, s < a`) forces `r = s` or `r+s = a`.
* `no_antipodal_pair` — the residue-level obstruction (re-derived locally).
* `residue_card_le` — **main theorem**: the number of residue classes mod `a`
  occupied by larger elements of `A` is at most `a / 2 + 1`.
* `residue_card_two_mul_le` — the same bound in the "at most half" form
  `2 * (occupied residues) ≤ a + 2`.
* `divFree_456` — concrete witness that the hypotheses are non-vacuous.
-/

namespace Erdos12WIP01OQ01

/-- The divisibility-free property of Erdős #12 (kept local, matching the parent
leaf `Erdos12WIP01`): no `a ∣ (b + c)` for distinct `a < b, c` in `A`. -/
def IsDivisibilityFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c → a < b → a < c → ¬(a ∣ (b + c))

variable {A : Set ℕ}

/-- **Residue-level obstruction** (from the parent leaf): two distinct elements
of `A` larger than `a ∈ A` are never antipodal mod `a`. -/
theorem no_antipodal_pair (h : IsDivisibilityFree A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hac : a < c) (hbc : b ≠ c) : (b + c) % a ≠ 0 := by
  intro hmod
  exact h a b c ha hb hc (ne_of_lt hab) (ne_of_lt hac) hbc hab hac
    (Nat.dvd_of_mod_eq_zero hmod)

/-- The folding map `r ↦ min r (a - r)`, collapsing each residue with its
antipode. -/
def fold (a r : ℕ) : ℕ := min r (a - r)

/-- Folding lands at or below `⌊a/2⌋`. -/
theorem fold_le_half (a r : ℕ) : fold a r ≤ a / 2 := by
  unfold fold; rw [min_def]; split_ifs <;> omega

/-- `fold a` maps `{0, …, a-1}` into `Finset.range (a / 2 + 1)`. -/
theorem fold_mem_range {a r : ℕ} (_hr : r < a) :
    fold a r ∈ Finset.range (a / 2 + 1) := by
  rw [Finset.mem_range]
  have := fold_le_half a r
  omega

/-- **Fold collision characterisation.** For residues `r, s < a`, equal folds
force either equality or antipodality `r + s = a`. -/
theorem fold_eq_iff {a r s : ℕ} (hr : r < a) (hs : s < a) :
    fold a r = fold a s ↔ r = s ∨ r + s = a := by
  unfold fold
  rw [min_def, min_def]
  constructor
  · intro hfold
    split_ifs at hfold <;> omega
  · rintro (rfl | hrs) <;> split_ifs <;> omega

/--
**Main theorem — quantitative residue bound.**

Let `A` be divisibility-free and `a ∈ A` with `0 < a`.  For any finite set `S`
of elements of `A` all larger than `a`, the residues mod `a` that they occupy
number at most `a / 2 + 1`.

This is the quantitative sharpening of the parent's `no_antipodal_pair`: the
larger elements of a divisibility-free set can only reach *about half* of the
residue classes below `a`.
-/
theorem residue_card_le (h : IsDivisibilityFree A) {a : ℕ} (ha : a ∈ A)
    (ha0 : 0 < a) {S : Finset ℕ} (hSA : ↑S ⊆ A) (hlarge : ∀ b ∈ S, a < b) :
    (S.image (· % a)).card ≤ a / 2 + 1 := by
  -- Bound the residue set by injecting it via `fold a` into `range (a/2+1)`.
  rw [← Finset.card_range (a / 2 + 1)]
  apply Finset.card_le_card_of_injOn (fold a)
  · -- The folded residues land in `range (a/2+1)`.
    intro r hr
    simp only [Finset.mem_image] at hr
    obtain ⟨b, _, rfl⟩ := hr
    exact fold_mem_range (Nat.mod_lt b ha0)
  · -- `fold a` is injective on the residue set.
    intro r hr s hs hfold
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hr hs
    obtain ⟨b, hbS, rfl⟩ := hr
    obtain ⟨c, hcS, rfl⟩ := hs
    -- `fold`-equality forces equal residues or antipodality; the latter is
    -- forbidden by `no_antipodal_pair`, so the residues must coincide.
    rcases (fold_eq_iff (Nat.mod_lt b ha0) (Nat.mod_lt c ha0)).1 hfold with heq | hsum
    · exact heq
    · rcases eq_or_ne (b % a) (c % a) with heq | hne
      · exact heq
      · exfalso
        have hbc : b ≠ c := fun hbceq => hne (by rw [hbceq])
        have hmod : (b + c) % a = 0 := by rw [Nat.add_mod, hsum, Nat.mod_self]
        exact no_antipodal_pair h ha (hSA hbS) (hSA hcS)
          (hlarge b hbS) (hlarge c hcS) hbc hmod

/-- **"At most half" form** of the main bound: twice the number of occupied
residue classes is at most `a + 2`. -/
theorem residue_card_two_mul_le (h : IsDivisibilityFree A) {a : ℕ} (ha : a ∈ A)
    (ha0 : 0 < a) {S : Finset ℕ} (hSA : ↑S ⊆ A) (hlarge : ∀ b ∈ S, a < b) :
    2 * (S.image (· % a)).card ≤ a + 2 := by
  have := residue_card_le h ha ha0 hSA hlarge
  omega

/-- A concrete divisibility-free set witnessing the hypotheses are non-vacuous:
`{4, 5, 6}` (the only nontrivial check is `4 ∤ 5 + 6 = 11`). -/
theorem divFree_456 : IsDivisibilityFree ({4, 5, 6} : Set ℕ) := by
  intro a b c ha hb hc _ _ hbc hab hac
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> omega

end Erdos12WIP01OQ01
