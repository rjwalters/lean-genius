import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Proofs.FrobeniusNumber
import Proofs.FrobeniusNumberOQ02

/-!
# Frobenius Number OQ-01: Count of Non-Representable Numbers = (a-1)(b-1)/2

For coprime positive integers a, b ≥ 2 with Frobenius number g = ab-a-b,
exactly (a-1)(b-1)/2 positive integers in {1,...,g} cannot be expressed as
a non-negative integer linear combination of a and b.

## Proof

1. **Symmetry** (OQ-02, `FrobeniusSymmetry.frobenius_symmetry`): For 0 < n < g,
   `Representable a b n ↔ ¬Representable a b (g-n)`.
2. The map k ↦ g-k bijects nonRep∩{1,...,g-1} bijectively onto Rep∩{1,...,g-1}.
3. So |nonRep∩{1,...,g-1}| = |Rep∩{1,...,g-1}|, and their sum = g-1 (partition of {1,...,g-1}).
   Thus each is (g-1)/2.
4. Adding g (not representable): total nonRep count = (g-1)/2 + 1 = (g+1)/2 = (a-1)(b-1)/2,
   since g+1 = (a-1)(b-1).
-/

open FrobeniusNumber FrobeniusSymmetry Classical

noncomputable section

namespace FrobeniusCountOQ01

variable {a b : ℕ}

-- ============================================================
-- Part 1: Symmetry bijection gives equal cardinality
-- ============================================================

/-- The involution k ↦ g-k gives a bijection from nonRep∩{1,...,g-1} to Rep∩{1,...,g-1}. -/
private lemma card_nonrep_eq_rep (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ((Finset.Icc 1 (frobeniusNumber a b - 1)).filter (fun k => ¬Representable a b k)).card =
    ((Finset.Icc 1 (frobeniusNumber a b - 1)).filter (fun k => Representable a b k)).card := by
  apply Finset.card_bij (fun k _ => frobeniusNumber a b - k)
  · -- Well-defined: ¬Rep(k) → Rep(g-k)
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk1, hk2⟩, hk_not⟩ := hk
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    by_contra h_rep
    exact hk_not ((frobenius_symmetry ha hb hab hk1 (by omega)).mpr h_rep)
  · -- Injective
    intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk₁ hk₂; omega
  · -- Surjective: Rep(m) ↦ nonRep(g-m)
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    obtain ⟨⟨hm1, hm2⟩, hm_rep⟩ := hm
    exact ⟨frobeniusNumber a b - m,
           ⟨⟨by omega, by omega⟩, (frobenius_symmetry ha hb hab hm1 (by omega)).mp hm_rep⟩,
           by omega⟩

-- ============================================================
-- Part 2: (a-1)(b-1) is always even for coprime a, b ≥ 2
-- ============================================================

/-- For coprime a, b ≥ 2, at least one of a-1, b-1 is even, so (a-1)(b-1) is even. -/
private lemma prod_pred_even (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2 ∣ (a - 1) * (b - 1) := by
  rcases Nat.even_or_odd a with ⟨ka, hka⟩ | ⟨ka, hka⟩
  · -- a even → b must be odd → b-1 even
    have h_a2 : 2 ∣ a := ⟨ka, hka⟩
    have h_b_odd : ¬2 ∣ b :=
      fun h_b2 => absurd (hab ▸ Nat.dvd_gcd h_a2 h_b2) (by norm_num)
    have h_b1 : 2 ∣ b - 1 := by
      rw [Nat.dvd_iff_mod_eq_zero] at h_b_odd ⊢; omega
    exact h_b1.mul_left _
  · -- a odd → a-1 = 2*ka is even
    exact ⟨ka * (b - 1), by have : a - 1 = 2 * ka := by omega; rw [this]; ring⟩

-- ============================================================
-- Part 3: Main theorem
-- ============================================================

/-- **OQ-01**: Exactly (a-1)(b-1)/2 positive integers in {1,...,g(a,b)} are not
    representable as non-negative integer linear combinations of a and b. -/
theorem frobenius_count (hab : Nat.Coprime a b) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ((Finset.Icc 1 (frobeniusNumber a b)).filter (fun k => ¬Representable a b k)).card =
    (a - 1) * (b - 1) / 2 := by
  set g := frobeniusNumber a b with hg_def
  have hg_pos : 0 < g := by simp only [hg_def, frobeniusNumber]; nlinarith
  have hg_not : ¬Representable a b g := (sylvester_frobenius hab ha hb).2.1
  -- Rewrite {1,...,g}.filter(nonRep) = {1,...,g-1}.filter(nonRep) ∪ {g}
  have hsplit : (Finset.Icc 1 g).filter (fun k => ¬Representable a b k) =
      (Finset.Icc 1 (g - 1)).filter (fun k => ¬Representable a b k) ∪ {g} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro ⟨⟨h1, h2⟩, hn⟩
      exact if h : k = g then Or.inr h else Or.inl ⟨⟨h1, by omega⟩, hn⟩
    · rintro (⟨⟨h1, h2⟩, hn⟩ | rfl)
      · exact ⟨⟨h1, by omega⟩, hn⟩
      · exact ⟨⟨hg_pos, le_refl _⟩, hg_not⟩
  have hdisj : Disjoint
      ((Finset.Icc 1 (g - 1)).filter (fun k => ¬Representable a b k)) {g} := by
    simp only [Finset.disjoint_singleton_right, Finset.mem_filter, Finset.mem_Icc]; omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  -- Define c = |nonRep∩{1,...,g-1}|
  set c := ((Finset.Icc 1 (g - 1)).filter (fun k => ¬Representable a b k)).card
  -- By OQ-02 bijection: c = |Rep∩{1,...,g-1}|
  have hceq : c = ((Finset.Icc 1 (g - 1)).filter (fun k => Representable a b k)).card :=
    card_nonrep_eq_rep hab ha hb
  -- Partition {1,...,g-1}: |nonRep| + |Rep| = g-1
  have hcpart :
      c + ((Finset.Icc 1 (g - 1)).filter (fun k => Representable a b k)).card = g - 1 := by
    have hfilt := Finset.filter_card_add_filter_neg_card_eq_card (Finset.Icc 1 (g - 1))
                    (Representable a b ·)
    rw [Finset.card_Icc] at hfilt; omega
  -- From hceq and hcpart: 2*c = g-1
  have h2c : 2 * c = g - 1 := by linarith [hceq]
  -- (a-1)(b-1) = g+1 (from frobeniusNumber definition)
  have hg1 : (a - 1) * (b - 1) = g + 1 := by
    simp only [hg_def, frobeniusNumber]; nlinarith
  -- Get q with (a-1)(b-1) = 2*q (even)
  obtain ⟨q, hq⟩ := prod_pred_even hab ha hb
  -- (a-1)(b-1)/2 = q
  have hq' : (a - 1) * (b - 1) / 2 = q := by
    rw [hq, Nat.mul_div_cancel_left _ (by norm_num)]
  -- 2*q = g+1 (from hg1 and hq)
  have h2q : 2 * q = g + 1 := by linarith [hg1, hq]
  -- Conclusion: c+1 = q = (a-1)(b-1)/2
  rw [← hq']
  -- From h2c : 2*c = g-1 and h2q : 2*q = g+1: 2*(c+1) = 2*q, so c+1 = q
  linarith

end FrobeniusCountOQ01

end -- noncomputable section

-- ============================================================
-- Examples
-- ============================================================

open FrobeniusNumber FrobeniusCountOQ01

-- For (3,5): g=7, count = (2)(4)/2 = 4; nonRep = {1,2,4,7}
example : frobeniusNumber 3 5 = 7 := by native_decide
example : (3 - 1 : ℕ) * (5 - 1) / 2 = 4 := by norm_num
example : ¬Representable 3 5 1 := fun ⟨x, y, h⟩ => by omega
example : ¬Representable 3 5 2 := fun ⟨x, y, h⟩ => by omega
example : ¬Representable 3 5 4 := fun ⟨x, y, h⟩ => by omega
example : ¬Representable 3 5 7 := fun ⟨x, y, h⟩ => by omega

-- For (3,7): g=11, count = (2)(6)/2 = 6
example : frobeniusNumber 3 7 = 11 := by native_decide
example : (3 - 1 : ℕ) * (7 - 1) / 2 = 6 := by norm_num

-- For (5,8): g=27, count = (4)(7)/2 = 14
example : frobeniusNumber 5 8 = 27 := by native_decide
example : (5 - 1 : ℕ) * (8 - 1) / 2 = 14 := by norm_num

#check @FrobeniusCountOQ01.frobenius_count
