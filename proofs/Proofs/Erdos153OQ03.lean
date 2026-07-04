/-
# Erdős Problem #153 — OQ-03: The B_h generalization of Sidon sets

The parent problem (Erdős #153) concerns the gap variance of the sumset of a
**Sidon set** (a B₂ set: all pairwise sums are distinct):

  Let A be a finite Sidon set and A+A = {s₁ < ... < sₜ}.
  Is (1/t) · Σ (s_{i+1} - s_i)² → ∞ as |A| → ∞?

The open follow-up question OQ-03 asks:

  *Does the analogous statement hold for B_h sets (h ≥ 3), where the h-wise
   sums are distinct?*

The full gap-variance conjecture for B_h sets is open (it already is for h = 2).
This file does **not** resolve it.  Instead it builds the reusable B_h
infrastructure and proves the foundational *structural* facts, most notably the
**nesting / downward-closure** property

    B_h  ⟹  B_{h-1}      (for nonempty A),

so that every B_h set with h ≥ 2 is in particular a Sidon set.  This is the exact
analog of a monotonicity-in-the-parameter lemma and gives an honest reduction:
the h ≥ 3 gap-variance question, restricted to B_h sets, is *at least as
constrained* as the Sidon (h = 2) case, because every B_h set is Sidon.

## Results (all 0 sorries, 0 axioms)
- `IsBhSet`                 : the B_h property, phrased via multisets of size h
- `isBhSet_one`            : every set is trivially B₁
- `isBhSet_of_succ`        : B_{h+1} ⟹ B_h        (one-step nesting, needs A ≠ ∅)
- `isBhSet_antitone`       : B_h ⟹ B_k for k ≤ h  (full downward closure)
- `isSidon_of_isBhSet_two` : the B₂ property yields the gallery's `IsSidon`
- `isSidon_of_isBhSet`     : every B_h set (h ≥ 2, nonempty) is Sidon
-/
import Mathlib

namespace Erdos153OQ03

/-!
## Section I: The B_h property

A finite set `A ⊆ ℕ` is a **B_h set** when the h-fold sums

  a₁ + a₂ + ⋯ + a_h    (aᵢ ∈ A, repetition allowed, order irrelevant)

are pairwise distinct.  An h-fold sum with repetition and no order is exactly a
`Multiset` of size `h` whose elements lie in `A`, and its value is `Multiset.sum`.
So "the h-fold sums are distinct" is the statement that `Multiset.sum` is injective
on the size-`h` multisets drawn from `A`.
-/

/-- `IsBhSet h A`: any two multisets of size `h`, both with all elements in `A`,
that have equal sum are equal.  For `h = 2` this is the Sidon (B₂) condition. -/
def IsBhSet (h : ℕ) (A : Finset ℕ) : Prop :=
  ∀ s t : Multiset ℕ,
    (∀ x ∈ s, x ∈ A) → (∀ x ∈ t, x ∈ A) →
    Multiset.card s = h → Multiset.card t = h →
    s.sum = t.sum → s = t

/-!
## Section II: Base case and nesting
-/

/-- Every set is a B₁ set: a size-1 multiset is determined by its unique element,
which equals its sum. -/
theorem isBhSet_one (A : Finset ℕ) : IsBhSet 1 A := by
  intro s t _ _ hcs hct hsum
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hcs
  obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp hct
  simp only [Multiset.sum_singleton] at hsum
  rw [hsum]

/-- **One-step nesting.** If `A` is nonempty and a B_{h+1} set, then it is a
B_h set.  Given two size-`h` multisets with equal sum, pad each with a fixed
element `a₀ ∈ A`; the padded multisets have size `h+1`, still draw from `A`, and
still share a sum, so the B_{h+1} property forces them equal — and cancelling the
padding element gives the original equality. -/
theorem isBhSet_of_succ {h : ℕ} {A : Finset ℕ} (hA : A.Nonempty)
    (H : IsBhSet (h + 1) A) : IsBhSet h A := by
  obtain ⟨a₀, ha₀⟩ := hA
  intro s t hs ht hcs hct hsum
  have hmem_s : ∀ x ∈ a₀ ::ₘ s, x ∈ A := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ha₀
    · exact hs x hx
  have hmem_t : ∀ x ∈ a₀ ::ₘ t, x ∈ A := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ha₀
    · exact ht x hx
  have key : a₀ ::ₘ s = a₀ ::ₘ t :=
    H (a₀ ::ₘ s) (a₀ ::ₘ t) hmem_s hmem_t
      (by rw [Multiset.card_cons, hcs]) (by rw [Multiset.card_cons, hct])
      (by rw [Multiset.sum_cons, Multiset.sum_cons, hsum])
  -- cancel the padding element `a₀` by erasing it from both sides
  have hcancel := congrArg (fun m => Multiset.erase m a₀) key
  simpa using hcancel

/-- **Full downward closure.** If `A` is nonempty and a B_h set, then it is a
B_k set for every `k ≤ h`.  Induct on `h`, peeling one element at a time with
`isBhSet_of_succ`. -/
theorem isBhSet_antitone {A : Finset ℕ} (hA : A.Nonempty) :
    ∀ {h k : ℕ}, k ≤ h → IsBhSet h A → IsBhSet k A := by
  intro h
  induction h with
  | zero =>
      intro k hk H
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact H
  | succ n ih =>
      intro k hk H
      rcases hk.lt_or_eq with hlt | heq
      · exact ih (Nat.lt_succ_iff.mp hlt) (isBhSet_of_succ hA H)
      · subst heq; exact H

/-!
## Section III: Bridge to the gallery's Sidon definition

The parent file `Erdos153Problem.lean` uses the ordered pairwise phrasing of the
Sidon condition.  We reproduce it here (self-contained) and show it is exactly
the `h = 2` instance of `IsBhSet`, so the new definition genuinely extends the
gallery's notion of a Sidon set.
-/

/-- The gallery's Sidon condition (from `Erdos153Problem.lean`): `a + b = c + d`
with `a ≤ b`, `c ≤ d` forces `(a, b) = (c, d)`. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- The `B₂` property implies the gallery's ordered Sidon condition.  From the
size-2 multisets `a ::ₘ b ::ₘ 0` and `c ::ₘ d ::ₘ 0` sharing a sum we obtain
multiset equality, and the orderings `a ≤ b`, `c ≤ d` pin down the components. -/
theorem isSidon_of_isBhSet_two {A : Finset ℕ} (H : IsBhSet 2 A) : IsSidon A := by
  intro a ha b hb c hc d hd hab hcd hsum
  have hpair : (a ::ₘ b ::ₘ (0 : Multiset ℕ)) = c ::ₘ d ::ₘ 0 := by
    refine H _ _ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact ha
      · rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact absurd hx (Multiset.notMem_zero x)
    · intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hx
      · exact hc
      · rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact hd
        · exact absurd hx (Multiset.notMem_zero x)
    · simp
    · simp
    · simp only [Multiset.sum_cons, Multiset.sum_zero, add_zero]; exact hsum
  -- extract componentwise equalities from the multiset identity
  have m1 : a = c ∨ a = d := by
    have h : a ∈ a ::ₘ b ::ₘ (0 : Multiset ℕ) := by simp
    rw [hpair] at h; simpa using h
  have m3 : c = a ∨ c = b := by
    have h : c ∈ c ::ₘ d ::ₘ (0 : Multiset ℕ) := by simp
    rw [← hpair] at h; simpa using h
  have m4 : d = a ∨ d = b := by
    have h : d ∈ c ::ₘ d ::ₘ (0 : Multiset ℕ) := by simp
    rw [← hpair] at h; simpa using h
  refine ⟨?_, ?_⟩ <;> omega

/-- Every nonempty B_h set with `h ≥ 2` is a Sidon set.  Combines downward
closure to `h = 2` with the bridge `isSidon_of_isBhSet_two`. -/
theorem isSidon_of_isBhSet {h : ℕ} {A : Finset ℕ} (hA : A.Nonempty)
    (hh : 2 ≤ h) (H : IsBhSet h A) : IsSidon A :=
  isSidon_of_isBhSet_two (isBhSet_antitone hA hh H)

/-!
## Section IV: Further structural facts

Two hereditary/base companions to the nesting results of Section II, and the converse
of the Sidon bridge (upgrading `isSidon_of_isBhSet_two` to a characterization).
-/

/-- **B₀ is trivial.** Every finite set is a B₀ set: the only multiset of card `0` is
the empty multiset, so the injectivity condition is vacuous. Complements `isBhSet_one`.
Unlike the nesting lemmas this needs no nonemptiness hypothesis. -/
theorem isBhSet_zero (A : Finset ℕ) : IsBhSet 0 A := by
  intro s t _ _ hcs hct _
  rw [Multiset.card_eq_zero.mp hcs, Multiset.card_eq_zero.mp hct]

/-- **B_h is hereditary (monotone in the ground set).** Every subset of a B_h set is a
B_h set: the injectivity of `Multiset.sum` on the size-`h` multisets drawn from the
larger set restricts to those drawn from the subset. This is the ground-set analog of
`isBhSet_antitone` (which is monotone in the order `h`), and — unlike the nesting
lemmas — needs no nonemptiness hypothesis. -/
theorem isBhSet_subset {h : ℕ} {A B : Finset ℕ} (hBA : B ⊆ A)
    (H : IsBhSet h A) : IsBhSet h B := by
  intro s t hs ht hcs hct hsum
  exact H s t (fun x hx => hBA (hs x hx)) (fun x hx => hBA (ht x hx)) hcs hct hsum

/-- **The gallery's ordered Sidon condition implies the B₂ property** — the converse of
`isSidon_of_isBhSet_two`. Two size-2 multisets from `A` with equal sum are each an
unordered pair `{x, y}` (`Multiset.card_eq_two`); sorting each pair and applying
`IsSidon` pins the two components down, so the multisets coincide. -/
theorem isBhSet_two_of_isSidon {A : Finset ℕ} (H : IsSidon A) : IsBhSet 2 A := by
  intro s t hs ht hcs hct hsum
  obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp hcs
  obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp hct
  have ha : a ∈ A := hs a (by simp)
  have hb : b ∈ A := hs b (by simp)
  have hc : c ∈ A := ht c (by simp)
  have hd : d ∈ A := ht d (by simp)
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum
  -- `hsum : a + b = c + d`; split on the two orderings and apply `IsSidon`.
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · obtain ⟨rfl, rfl⟩ := H a ha b hb c hc d hd hab hcd hsum
      first | rfl | exact Multiset.cons_swap _ _ _
    · obtain ⟨rfl, rfl⟩ := H a ha b hb d hd c hc hab hdc (by omega)
      first | rfl | exact Multiset.cons_swap _ _ _
  · rcases le_total c d with hcd | hdc
    · obtain ⟨rfl, rfl⟩ := H b hb a ha c hc d hd hba hcd (by omega)
      first | rfl | exact Multiset.cons_swap _ _ _
    · obtain ⟨rfl, rfl⟩ := H b hb a ha d hd c hc hba hdc (by omega)
      first | rfl | exact Multiset.cons_swap _ _ _

/-- **Characterization of B₂ sets.** The multiset `B₂` property is *exactly* the
gallery's ordered Sidon condition. Combines `isSidon_of_isBhSet_two` with its converse
`isBhSet_two_of_isSidon`. -/
theorem isBhSet_two_iff_isSidon {A : Finset ℕ} : IsBhSet 2 A ↔ IsSidon A :=
  ⟨isSidon_of_isBhSet_two, isBhSet_two_of_isSidon⟩

end Erdos153OQ03
