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
- `isBhSet_two_iff_isSidon`: B₂ is *exactly* the gallery's Sidon condition
- `isBhSet_empty`          : the empty set is B_h for every h
- `isBhSet_singleton`      : every singleton is B_h for every h
- `isBhSet_smul`           : dilation invariance — c·A is B_h whenever A is (c ≥ 1)
- `isBhSet_add`            : translation invariance — A+t is B_h whenever A is
- `isBhSet_affine`         : affine invariance — {c·a+t} is B_h whenever A is (c ≥ 1)
- `hSumset`                : the h-fold sumset {a₁+⋯+a_h : aᵢ ∈ A}
- `isBhSet_iff_injOn`      : B_h ⟺ Multiset.sum is injective on `A.sym h`
- `card_hSumset_of_isBhSet`: sharp count — |h-fold sumset| = |A.sym h| = C(|A|+h−1, h)
- `card_finset_sym_eq_choose`: the stars-and-bars bridge |A.sym h| = C(|A|+h−1, h)
- `card_hSumset_eq_choose_of_isBhSet` : saturation in closed binomial form
- `choose_le_of_isBhSet`     : the B_h density bound C(|A|+h−1, h) ≤ hN+1 in closed form
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

/-!
## Section V: Base cases and dilation invariance

Two more base cases — the empty set and singletons are `B_h` for *every* `h` — and
a genuine structural symmetry: the class of `B_h` sets is closed under dilation
`a ↦ c·a` (`c ≥ 1`).  Together with translation, dilation invariance makes
"being a `B_h` set" a property of the *affine structure* of `A`, independent of
its position and scale; this is the invariance underlying the standard reduction
of `B_h`-set problems to sets normalised to start at `0`.
-/

/-- **The empty set is `B_h`** for every `h`: there is no element to draw from `∅`,
so the only multiset with all elements in `∅` is `0`, and the injectivity
condition is vacuous.  Needs no nonemptiness — indeed `∅` is exactly the set for
which the nesting lemmas' hypothesis fails. -/
theorem isBhSet_empty (h : ℕ) : IsBhSet h (∅ : Finset ℕ) := by
  intro s t hs ht _ _ _
  have hs0 : s = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    exact Finset.notMem_empty x (hs x hx)
  have ht0 : t = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    exact Finset.notMem_empty x (ht x hx)
  rw [hs0, ht0]

/-- **Singletons are `B_h`** for every `h`: the only size-`h` multiset all of whose
elements equal `a` is `Multiset.replicate h a`, so any two competing size-`h`
multisets drawn from `{a}` already coincide before the sum is consulted.  Like
`isBhSet_empty` this needs no nonemptiness hypothesis. -/
theorem isBhSet_singleton (h a : ℕ) : IsBhSet h ({a} : Finset ℕ) := by
  intro s t hs ht hcs hct _
  have hs' : s = Multiset.replicate h a :=
    Multiset.eq_replicate.mpr ⟨hcs, fun b hb => Finset.mem_singleton.mp (hs b hb)⟩
  have ht' : t = Multiset.replicate h a :=
    Multiset.eq_replicate.mpr ⟨hct, fun b hb => Finset.mem_singleton.mp (ht b hb)⟩
  rw [hs', ht']

/-- **Dilation invariance.** If `A` is a `B_h` set and `c ≥ 1`, then the dilated set
`c · A = {c·a : a ∈ A}` (here `A.image (c * ·)`) is again a `B_h` set.  A size-`h`
multiset drawn from `c · A` is `c` times (elementwise) a size-`h` multiset drawn
from `A`; `Multiset.sum` scales by the factor `c`, and since `c` is cancellable,
equal sums downstairs pull back to equal sums upstairs, where the `B_h` property of
`A` closes the gap and re-dilating transports the equality back down. -/
theorem isBhSet_smul {h c : ℕ} {A : Finset ℕ} (hc : 0 < c)
    (H : IsBhSet h A) : IsBhSet h (A.image (fun a => c * a)) := by
  -- `Multiset.sum` scales linearly under elementwise multiplication by `c`.
  have hscale : ∀ m : Multiset ℕ, (m.map (fun x => c * x)).sum = c * m.sum := by
    intro m
    refine Multiset.induction_on m ?_ ?_
    · simp
    · intro a m ih
      simp [Multiset.map_cons, Multiset.sum_cons, ih, mul_add]
  -- division by `c` inverts multiplication by `c` on elements of the dilated set:
  -- re-dilating the pulled-back multiset recovers it, and its elements lie in `A`.
  have hinv : ∀ m : Multiset ℕ, (∀ x ∈ m, x ∈ A.image (fun a => c * a)) →
      (m.map (fun x => x / c)).map (fun x => c * x) = m ∧
      (∀ y ∈ m.map (fun x => x / c), y ∈ A) := by
    intro m hm
    refine ⟨?_, ?_⟩
    · rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id' m]
      apply Multiset.map_congr rfl
      intro x hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (hm x hx)
      show c * (c * a / c) = c * a
      rw [Nat.mul_div_cancel_left a hc]
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hm x hx)
      rw [Nat.mul_div_cancel_left a hc]
      exact ha
  intro s t hs ht hcs hct hsum
  obtain ⟨hs_rec, hsA⟩ := hinv s hs
  obtain ⟨ht_rec, htA⟩ := hinv t ht
  set s₀ : Multiset ℕ := s.map (fun x => x / c) with hs₀
  set t₀ : Multiset ℕ := t.map (fun x => x / c) with ht₀
  -- the pulled-back multisets keep size `h`
  have hcs₀ : Multiset.card s₀ = h := by rw [hs₀, Multiset.card_map]; exact hcs
  have hct₀ : Multiset.card t₀ = h := by rw [ht₀, Multiset.card_map]; exact hct
  -- and share a sum, after cancelling the common factor `c`
  have hsum₀ : s₀.sum = t₀.sum := by
    apply Nat.eq_of_mul_eq_mul_left hc
    rw [← hscale s₀, ← hscale t₀, hs_rec, ht_rec]
    exact hsum
  -- `B_h` upstairs forces `s₀ = t₀`; re-dilating both sides gives `s = t`.
  have h0 : s₀ = t₀ := H s₀ t₀ hsA htA hcs₀ hct₀ hsum₀
  rw [← hs_rec, ← ht_rec, h0]

/-- **Translation invariance.** If `A` is a `B_h` set, then the translate
`A + t = {a+t : a ∈ A}` (here `A.image (· + t)`) is again a `B_h` set.  The
companion to `isBhSet_smul`: where dilation scales every `h`-fold sum by `c`,
translation shifts every `h`-fold sum by the *constant* `h·t` (each of the `h`
summands gains `t`).  That shift cancels between two competing size-`h` sums, so
equal sums downstairs pull back to equal sums upstairs, where the `B_h` property
of `A` closes the gap and re-translating transports the equality back down.
Unlike the nesting lemmas this needs no nonemptiness hypothesis. -/
theorem isBhSet_add {h t : ℕ} {A : Finset ℕ}
    (H : IsBhSet h A) : IsBhSet h (A.image (fun a => a + t)) := by
  -- `Multiset.sum` shifts by `card · t` under an elementwise `+ t`.
  have hshift : ∀ m : Multiset ℕ,
      (m.map (fun x => x + t)).sum = m.sum + Multiset.card m * t := by
    intro m
    refine Multiset.induction_on m ?_ ?_
    · simp
    · intro a m ih
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih,
        Nat.add_mul, Nat.one_mul]
      ring
  -- subtracting `t` inverts the translation on elements of the translated set:
  -- re-translating the pulled-back multiset recovers it, and its elements lie in `A`.
  have hinv : ∀ m : Multiset ℕ, (∀ x ∈ m, x ∈ A.image (fun a => a + t)) →
      (m.map (fun x => x - t)).map (fun x => x + t) = m ∧
      (∀ y ∈ m.map (fun x => x - t), y ∈ A) := by
    intro m hm
    refine ⟨?_, ?_⟩
    · rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id' m]
      apply Multiset.map_congr rfl
      intro x hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (hm x hx)
      show a + t - t + t = a + t
      omega
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hm x hx)
      have : a + t - t = a := by omega
      rw [this]; exact ha
  intro s u hs hu hcs hcu hsum
  obtain ⟨hs_rec, hsA⟩ := hinv s hs
  obtain ⟨hu_rec, huA⟩ := hinv u hu
  set s₀ : Multiset ℕ := s.map (fun x => x - t) with hs₀
  set u₀ : Multiset ℕ := u.map (fun x => x - t) with hu₀
  -- the pulled-back multisets keep size `h`
  have hcs₀ : Multiset.card s₀ = h := by rw [hs₀, Multiset.card_map]; exact hcs
  have hcu₀ : Multiset.card u₀ = h := by rw [hu₀, Multiset.card_map]; exact hcu
  -- and share a sum, after cancelling the common shift `h·t`
  have hsum₀ : s₀.sum = u₀.sum := by
    have es : s.sum = s₀.sum + Multiset.card s₀ * t := by rw [← hs_rec, hshift]
    have eu : u.sum = u₀.sum + Multiset.card u₀ * t := by rw [← hu_rec, hshift]
    rw [hcs₀] at es; rw [hcu₀] at eu; omega
  -- `B_h` upstairs forces `s₀ = u₀`; re-translating both sides gives `s = u`.
  have h0 : s₀ = u₀ := H s₀ u₀ hsA huA hcs₀ hcu₀ hsum₀
  rw [← hs_rec, ← hu_rec, h0]

/-- **Affine invariance.** If `A` is a `B_h` set and `c ≥ 1`, then the affine image
`{c·a + t : a ∈ A}` (here `A.image (fun a => c·a + t)`) is again a `B_h` set.  This is
the structural payoff of Section V: the class of `B_h` sets is closed under every
order-preserving affine map `a ↦ c·a + t`, so "being a `B_h` set" depends only on the
*affine geometry* of `A`, not its position (`t`) or scale (`c`).  Proved by composing
dilation (`isBhSet_smul`) with translation (`isBhSet_add`), since
`a ↦ c·a + t = (· + t) ∘ (c · ·)`. -/
theorem isBhSet_affine {h c t : ℕ} {A : Finset ℕ} (hc : 0 < c)
    (H : IsBhSet h A) : IsBhSet h (A.image (fun a => c * a + t)) := by
  have himg : (A.image (fun a => c * a)).image (fun x => x + t)
            = A.image (fun a => c * a + t) := by
    rw [Finset.image_image]; rfl
  rw [← himg]
  exact isBhSet_add (isBhSet_smul hc H)

/-!
## Section VI: The sharp counting identity

The defining property of a `B_h` set is that its `h`-fold sums are *pairwise
distinct*.  Restated quantitatively: the `h`-fold sumset

    hΣ A  :=  { a₁ + ⋯ + a_h : aᵢ ∈ A }     (repetition allowed, order irrelevant)

attains the **maximum possible** cardinality — the number of size-`h` multisets
drawable from `A`, i.e. the multiset coefficient `C(|A| + h − 1, h)`.  We realise
`hΣ A` as the image of `A.sym h` (the finset of size-`h` multisets with entries in
`A`) under `Multiset.sum`, read the `B_h` property off as *injectivity* of that
image map, and conclude the cardinality identity.  This is the exact quantitative
face of "all `h`-fold sums distinct": a `B_h` set is precisely one whose `h`-fold
sumset is as large as the pigeonhole bound allows.
-/

/-- The `h`-fold sumset of `A`: the finite set of all sums of size-`h` multisets
drawn from `A` (repetition allowed, order irrelevant).  Built as the image of the
finset `A.sym h` of size-`h` multisets from `A` under `Multiset.sum`. -/
def hSumset (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.sym h).image (fun s : Sym ℕ h => (s : Multiset ℕ).sum)

/-- **`B_h` = injectivity of the sum map on `A.sym h`.**  The abstract `IsBhSet`
condition is exactly the statement that `Multiset.sum` is injective on the finset
`A.sym h` of size-`h` multisets drawn from `A`.  This is the `Sym`-packaged form of
the definition, and the engine behind the counting identity below. -/
theorem isBhSet_iff_injOn (h : ℕ) (A : Finset ℕ) :
    IsBhSet h A ↔
      Set.InjOn (fun s : Sym ℕ h => (s : Multiset ℕ).sum) (A.sym h) := by
  constructor
  · -- injectivity from the multiset definition
    intro H s hs t ht hsum
    apply Sym.coe_injective
    refine H _ _ ?_ ?_ ?_ ?_ hsum
    · intro x hx; exact (Finset.mem_sym_iff.mp hs) x (Sym.mem_coe.mp hx)
    · intro x hx; exact (Finset.mem_sym_iff.mp ht) x (Sym.mem_coe.mp hx)
    · exact s.2
    · exact t.2
  · -- the multiset definition from injectivity
    intro H s t hs ht hcs hct hsum
    have hsS : (⟨s, hcs⟩ : Sym ℕ h) ∈ A.sym h :=
      Finset.mem_sym_iff.mpr (fun a ha => hs a ha)
    have htS : (⟨t, hct⟩ : Sym ℕ h) ∈ A.sym h :=
      Finset.mem_sym_iff.mpr (fun a ha => ht a ha)
    have heq : (⟨s, hcs⟩ : Sym ℕ h) = ⟨t, hct⟩ := H hsS htS (by simpa using hsum)
    exact Subtype.ext_iff.mp heq

/-- **The sharp cardinality identity.**  For a `B_h` set `A`, the `h`-fold sumset
`hSumset h A` has cardinality exactly `(A.sym h).card` — every one of the size-`h`
multisets drawn from `A` yields a *distinct* sum, so no collisions shrink the image.
Since `(A.sym h).card` is the multiset coefficient `C(|A| + h − 1, h)` (the total
number of size-`h` multisets on `|A|` symbols), this says a `B_h` set is precisely
one whose `h`-fold sumset *saturates* that pigeonhole maximum — the quantitative
restatement of "all `h`-fold sums distinct". -/
theorem card_hSumset_of_isBhSet {h : ℕ} {A : Finset ℕ} (H : IsBhSet h A) :
    (hSumset h A).card = (A.sym h).card :=
  Finset.card_image_of_injOn ((isBhSet_iff_injOn h A).mp H)

/-!
## Section VII: The density bound  `|A| = O(N^{1/h})`

The counting identity of Section VI becomes a *density* statement once the ground set
is bounded.  If `A ⊆ {0, 1, …, N}` then every `h`-fold sum lies in `{0, …, hN}`, so the
`h`-fold sumset has at most `hN+1` elements.  For a `B_h` set that sumset has cardinality
exactly `(A.sym h).card` — the number of size-`h` multisets drawable from `A`, i.e. the
stars-and-bars count `C(|A|+h−1, h)`.  Hence

    (A.sym h).card = C(|A| + h − 1, h)  ≤  hN + 1.

Since the left side grows like `|A|^h / h!`, this forces `|A| = O(N^{1/h})` — the sharp
counting bound on the size of a `B_h` set in an interval, the `h`-fold generalisation of
the `|A| = O(√N)` Sidon (`h = 2`) bound that motivates OQ-03.

(Mathlib provides the stars-and-bars identity only in its `Fintype` form
`Sym.card_sym_eq_choose : Fintype.card (Sym α k) = C(card α + k − 1, k)`; the `Finset`-level
equality `(A.sym h).card = C(|A|+h−1, h)` is not yet available, so the bound is stated with
the honest quantity `(A.sym h).card`, which *is* that multiset coefficient.)
-/

/-- If `A ⊆ {0, …, N}` then every `h`-fold sum is at most `hN`, so the `h`-fold sumset is
contained in `{0, …, hN}`. -/
theorem hSumset_subset_range {h N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range (N + 1)) :
    hSumset h A ⊆ Finset.range (h * N + 1) := by
  intro y hy
  rw [hSumset, Finset.mem_image] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  rw [Finset.mem_range, Nat.lt_succ_iff]
  have hbound : ∀ x ∈ (s : Multiset ℕ), x ≤ N := by
    intro x hx
    have hxA : x ∈ A := (Finset.mem_sym_iff.mp hs) x (Sym.mem_coe.mp hx)
    have hlt := hA hxA
    rw [Finset.mem_range, Nat.lt_succ_iff] at hlt
    exact hlt
  have hcard : (s : Multiset ℕ).card = h := s.2
  calc (s : Multiset ℕ).sum ≤ (s : Multiset ℕ).card • N :=
        Multiset.sum_le_card_nsmul _ _ hbound
    _ = h * N := by rw [hcard, smul_eq_mul]

/-- **The `B_h` density bound.**  A `B_h` set `A ⊆ {0, …, N}` has at most `hN + 1` distinct
`h`-fold sums, and — since it is `B_h` — those sums are all distinct, so the number of
size-`h` multisets it supports satisfies `(A.sym h).card ≤ hN + 1`.  As `(A.sym h).card`
is the multiset coefficient `C(|A| + h − 1, h) ∼ |A|^h/h!`, this forces `|A| = O(N^{1/h})`:
the sharp `h`-fold generalisation of the `|A| = O(√N)` Sidon density bound. -/
theorem card_sym_le_of_isBhSet {h N : ℕ} {A : Finset ℕ}
    (H : IsBhSet h A) (hA : A ⊆ Finset.range (N + 1)) :
    (A.sym h).card ≤ h * N + 1 := by
  rw [← card_hSumset_of_isBhSet H]
  calc (hSumset h A).card ≤ (Finset.range (h * N + 1)).card :=
        Finset.card_le_card (hSumset_subset_range hA)
    _ = h * N + 1 := Finset.card_range _

/-!
## Section VIII: The saturation characterization

Section VI proved one direction — a `B_h` set saturates the multiset bound,
`(hSumset h A).card = (A.sym h).card`.  The converse also holds: if the `h`-fold sumset
attains that maximum, then the sum map on `A.sym h` has no collisions, so `A` is `B_h`.
Combining gives a clean *characterization*:

    A is B_h  ⟺  its h-fold sumset saturates the multiset bound (hΣ A).card = (A.sym h).card.

This is the exact quantitative face of the `B_h` property: `B_h` sets are precisely those
whose `h`-fold sumset is as large as the pigeonhole maximum `C(|A| + h − 1, h)` allows.
(No stars-and-bars identity is needed — the statement is phrased with the honest quantity
`(A.sym h).card`, which *is* that multiset coefficient.)
-/

/-- **The saturation characterization of `B_h`.**  A finite set `A` is `B_h` if and only if
its `h`-fold sumset attains the maximal cardinality `(A.sym h).card` — i.e. no two distinct
size-`h` multisets drawn from `A` share a sum.  The forward direction is Section VI's
`card_hSumset_of_isBhSet`; the converse reads injectivity of the sum map off the
image-cardinality equality via `Finset.injOn_of_card_image_eq`. -/
theorem isBhSet_iff_card_hSumset (h : ℕ) (A : Finset ℕ) :
    IsBhSet h A ↔ (hSumset h A).card = (A.sym h).card := by
  rw [isBhSet_iff_injOn]
  constructor
  · intro H
    exact Finset.card_image_of_injOn H
  · intro H
    exact Finset.injOn_of_card_image_eq H

/-!
## Section IX: The explicit stars-and-bars bridge  `(A.sym h).card = C(|A|+h−1, h)`

Sections VII–VIII stated every quantitative result with the *honest* quantity
`(A.sym h).card`, noting only that it "is" the multiset coefficient
`C(|A| + h − 1, h)` — because Mathlib supplies the stars-and-bars identity only
in its `Fintype` form `Sym.card_sym_eq_choose` (for `Fintype.card (Sym α h)`),
with no ready-made `Finset`-level `(A.sym h).card` companion.

Here we close that gap.  The finset `A.sym h` of size-`h` multisets drawn from
`A` is in explicit bijection with `Sym ↥A h`, the size-`h` multisets on the
subtype `↥A = {a // a ∈ A}`: the map `Sym.map (Subtype.val)` sends a multiset on
`↥A` to the underlying multiset on `ℕ` (whose elements all lie in `A`, so it
lands in `A.sym h`), it is injective (`Subtype.val` is), and it is onto
`A.sym h` (any size-`h` multiset with elements in `A` lifts back via
`Sym.attach`).  Transporting `Sym.card_sym_eq_choose` across this bijection and
using `Fintype.card ↥A = |A|` gives the closed form, upgrading the density bound
and the saturation identity to their textbook binomial statements.
-/

/-- **The stars-and-bars identity for `Finset.sym`.**  The number of size-`h`
multisets drawable from a finite set `A ⊆ ℕ` is the multiset coefficient
    `(A.sym h).card = C(|A| + h − 1, h)`.
Proof: `A.sym h` is the injective image of the universe of `Sym ↥A h` under
`Sym.map Subtype.val`, so its cardinality is `Fintype.card (Sym ↥A h)`; the
`Fintype`-level `Sym.card_sym_eq_choose` then evaluates that to
`C(Fintype.card ↥A + h − 1, h)`, and `Fintype.card ↥A = |A|`. -/
theorem card_finset_sym_eq_choose {h : ℕ} (A : Finset ℕ) :
    (A.sym h).card = (A.card + h - 1).choose h := by
  have hinj : Function.Injective (Sym.map (Subtype.val : {x // x ∈ A} → ℕ)) :=
    Sym.map_injective Subtype.val_injective h
  -- `A.sym h` is exactly the image of `Sym ↥A h` under `Sym.map Subtype.val`.
  have key : A.sym h
      = (Finset.univ : Finset (Sym {x // x ∈ A} h)).image (Sym.map Subtype.val) := by
    ext s
    simp only [Finset.mem_sym_iff, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · -- a multiset with all elements in `A` lifts to `Sym ↥A h` via `attach`
      intro hs
      refine ⟨Sym.map (fun x : {a // a ∈ s} => (⟨x.1, hs x.1 x.2⟩ : {a // a ∈ A}))
                s.attach, ?_⟩
      rw [Sym.map_map]
      exact Sym.attach_map_coe s
    · -- every element of an image multiset is a `Subtype.val`, hence in `A`
      rintro ⟨t, rfl⟩ a ha
      rw [Sym.mem_map] at ha
      obtain ⟨x, _, rfl⟩ := ha
      exact x.2
  rw [key, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Sym.card_sym_eq_choose, Fintype.card_coe]

/-- **Saturation in closed binomial form.**  For a `B_h` set `A`, the `h`-fold
sumset has cardinality exactly the multiset coefficient:
    `(hSumset h A).card = C(|A| + h − 1, h)`.
The closed-form refinement of `card_hSumset_of_isBhSet`, obtained by evaluating
`(A.sym h).card` via `card_finset_sym_eq_choose`. -/
theorem card_hSumset_eq_choose_of_isBhSet {h : ℕ} {A : Finset ℕ} (H : IsBhSet h A) :
    (hSumset h A).card = (A.card + h - 1).choose h := by
  rw [card_hSumset_of_isBhSet H, card_finset_sym_eq_choose]

/-- **The `B_h` density bound in closed binomial form.**  A `B_h` set
`A ⊆ {0, …, N}` satisfies
    `C(|A| + h − 1, h) ≤ hN + 1`.
Since the left side is `∼ |A|^h / h!`, this is the sharp `|A| = O(N^{1/h})`
generalisation of the Sidon (`h = 2`) bound `|A| = O(√N)`.  The closed-form
refinement of `card_sym_le_of_isBhSet`, via `card_finset_sym_eq_choose`. -/
theorem choose_le_of_isBhSet {h N : ℕ} {A : Finset ℕ}
    (H : IsBhSet h A) (hA : A ⊆ Finset.range (N + 1)) :
    (A.card + h - 1).choose h ≤ h * N + 1 := by
  rw [← card_finset_sym_eq_choose]
  exact card_sym_le_of_isBhSet H hA

end Erdos153OQ03
