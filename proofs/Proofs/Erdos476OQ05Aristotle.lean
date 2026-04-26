import Mathlib

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05Aristotle

variable {p : ℕ} [hp : Fact p.Prime]

/-
An arithmetic progression in ZMod p starting at `a` with difference `d`.
Mirroring the definition from Erdos476OQ05Problem.
-/
def IsArithmeticProgression (A : Finset (ZMod p)) (a d : ZMod p) : Prop :=
  A = (Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)

/-
Cauchy-Davenport lower bound for erase+sumset: |(A\{a₀})+B| ≥ |A|+|B|-2 when |A|≥2, |B|≥1.
-/
lemma erase_add_card_ge (A B : Finset (ZMod p)) (a₀ : ZMod p) (ha₀ : a₀ ∈ A)
    (hA : 2 ≤ A.card) (hB : 1 ≤ B.card) (hlt : A.card + B.card - 1 < p) :
    A.card + B.card - 2 ≤ (A.erase a₀ + B).card := by
  -- By ZMod.cauchy_davenport:
  have h_cauchy_davenport : (p ⊓ (Finset.card (A.erase a₀) + Finset.card B - 1)) ≤ Finset.card ((A.erase a₀) + B) := by
    apply_rules [ ZMod.cauchy_davenport ];
    · exact hp.1;
    · exact Finset.card_pos.mp ( by rw [ Finset.card_erase_of_mem ha₀ ] ; omega );
    · exact Finset.card_pos.mp hB;
  grind +qlia

/-
Upper bound: |(A\{a₀})+B| ≤ |A+B|.
-/
lemma erase_add_card_le (A B : Finset (ZMod p)) (a₀ : ZMod p) :
    (A.erase a₀ + B).card ≤ (A + B).card := by
  exact Finset.card_le_card ( Finset.add_subset_add_right ( Finset.erase_subset _ _ ) )

/-
If some b₀ ∈ B is "non-redundant" (removing it decreases the sumset),
    then the new element gives a non-redundant a₀ ∈ A.
-/
lemma non_redundant_b_gives_a (A B : Finset (ZMod p)) (b₀ : ZMod p) (hb₀ : b₀ ∈ B)
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card < p)
    (hcard : (A + B.erase b₀).card = A.card + B.card - 2) :
    ∃ a₀ ∈ A, ((A.erase a₀) + B).card = A.card + B.card - 2 := by
  -- Since A + B = (A + B.erase b₀) ∪ (A + {b₀}) and the sets differ by 1 in cardinality, there is exactly 1 element y in (A + {b₀}) \ (A + B.erase b₀).
  obtain ⟨y, hy⟩ : ∃ y ∈ A + {b₀}, y ∉ A + B.erase b₀ := by
    contrapose! h;
    have h_subset : A + B ⊆ A + B.erase b₀ := by
      simp_all +decide [ Finset.subset_iff, Finset.mem_add ];
      grind;
    exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_card h_subset ) ( by omega ) );
  -- Let $a₀$ be such that $y = a₀ + b₀$.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ ∈ A, y = a₀ + b₀ := by
    rw [ Finset.mem_add ] at hy ; aesop;
  -- So y ∉ (A.erase a₀) + B, meaning (A.erase a₀) + B ⊊ A + B.
  have h_strict_subset : (A.erase a₀ + B) ⊂ A + B := by
    simp_all +decide [ Finset.ssubset_def, Finset.subset_iff ];
    simp_all +decide [ Finset.mem_add ];
    grind;
  -- Since (A.erase a₀) + B ⊆ A + B and y ∉ (A.erase a₀) + B:
  have h_card_le : (A.erase a₀ + B).card ≤ (A + B).card - 1 := by
    exact Nat.le_sub_one_of_lt ( Finset.card_lt_card h_strict_subset );
  exact ⟨ a₀, ha₀.1, le_antisymm ( by omega ) ( by have := erase_add_card_ge A B a₀ ha₀.1 hA ( by linarith ) ( by omega ) ; omega ) ⟩

/-
In the all-redundant case, the counting argument gives (|A|-2)(|B|-2) ≥ 2,
    which is false for |B| = 2.
-/
lemma all_redundant_contradiction_B2 (A B : Finset (ZMod p))
    (hA3 : 2 < A.card) (hB : B.card = 2)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card < p)
    (hredundant : ∀ b₀ ∈ B, (A + B.erase b₀).card = A.card + B.card - 1) :
    False := by
  obtain ⟨ b₁, b₂, hb₁, hb₂, hne ⟩ := Finset.card_eq_two.mp hB;
  simp_all +decide [ Finset.sum_add_distrib ]

/-- Orbit injectivity in ZMod p: k ↦ x₀ + k*d is injective on Fin p when d ≠ 0. -/
private lemma zmod_orbit_inj {x₀ d : ZMod p} (hd : d ≠ 0) :
    Function.Injective (fun k : Fin p => x₀ + (k : ZMod p) * d) := by
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ heq
  simp only at heq
  have hmul : (j₁ : ZMod p) * d = (j₂ : ZMod p) * d := add_left_cancel heq
  have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := mul_right_cancel₀ hd hmul
  ext
  have hval := congrArg ZMod.val h_eq
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at hval
  omega

/-
**Position Analysis**: When AP₁ (start s₁, length n, diff d) and AP₂ (start s₂, length m, diff d)
satisfy (AP₁ \ AP₂).card = 1 with n ≤ m and n + m ≤ p, then:
  s₁ = s₂ - d  (AP₁ "predecessor" of AP₂, the unique missing element is the first of AP₁)
  OR
  s₁ = s₂ + (m - n + 1) * d  (AP₁ "successor" of AP₂, the unique missing element is the last of AP₁)

This is used to identify a₀'s position relative to the AP A' = A.erase a₀:
  a₀ = a₁ - d  (a₀ is the predecessor of AP A')
  OR
  a₀ = a₁ + |A'| * d  (a₀ is the successor of AP A')
-/
lemma ap_sdiff_endpoint (AP₁ AP₂ : Finset (ZMod p)) (s₁ s₂ d : ZMod p)
    (hAP₁ : IsArithmeticProgression AP₁ s₁ d)
    (hAP₂ : IsArithmeticProgression AP₂ s₂ d)
    (hd : d ≠ 0)
    (h₁ : 0 < AP₁.card)
    (h₁₂ : AP₁.card ≤ AP₂.card)
    (hlt : AP₁.card + AP₂.card ≤ p)
    (h_sdiff : (AP₁ \ AP₂).card = 1) :
    s₁ = s₂ - d ∨ s₁ = s₂ + ((AP₂.card - AP₁.card + 1 : ℕ) : ZMod p) * d := by
  sorry

/-
**Case 1 Existence**: In the inductive step of Vosper's theorem (|A| ≥ 3),
there always exists a "non-redundant" element a₀ ∈ A such that removing it
decreases the sumset cardinality.

The proof strategy:
1. Assume for contradiction that all a ∈ A are redundant (removing any a doesn't change |A+B|).
2. Show that all b ∈ B must also be redundant (using non_redundant_b_gives_a contrapositively).
3. Derive a contradiction:
   - For |B| = 2: use all_redundant_contradiction_B2.
   - For |B| = 3 with |A| = 3: counting argument gives 3*3 = 9 < 2*(3+3-1) = 10, contradiction.
   - General case: Cauchy-Davenport structure of ZMod p (prime order, no nontrivial subgroups)
     forces at least one element to be non-redundant.
-/
lemma case1_exists (A B : Finset (ZMod p))
    (hA3 : 2 < A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card - 1 < p) :
    ∃ a₀ ∈ A, ((A.erase a₀) + B).card = A.card + B.card - 2 := by
  by_contra hall
  push_neg at hall
  -- All a ∈ A are redundant
  have hredA : ∀ a ∈ A, ((A.erase a) + B).card = A.card + B.card - 1 := by
    intro a haA
    have hlo := erase_add_card_ge A B a haA (by omega) (by omega) (by omega)
    have hhi := erase_add_card_le A B a
    rw [h] at hhi
    exact Nat.le_antisymm (by omega) (by exact (hall a haA).symm ▸ by omega)
  -- All b ∈ B are also redundant (by non_redundant_b_gives_a contrapositive)
  have hredB : ∀ b ∈ B, (A + (B.erase b)).card = A.card + B.card - 1 := by
    intro b hbB
    have hlo : A.card + B.card - 2 ≤ (A + (B.erase b)).card := by
      have hCD : (p ⊓ (A.card + (B.erase b).card - 1)) ≤ (A + B.erase b).card :=
        ZMod.cauchy_davenport hp.1
          (Finset.card_pos.mp (by omega))
          (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hbB]; omega))
      rw [Finset.card_erase_of_mem hbB] at hCD
      simp only [Nat.inf_eq_min] at hCD
      omega
    have hhi : (A + (B.erase b)).card ≤ A.card + B.card - 1 := by
      have := Finset.card_le_card (Finset.add_subset_add_left (Finset.erase_subset b B))
      omega
    by_contra hne
    have hcard : (A + B.erase b).card = A.card + B.card - 2 := by omega
    obtain ⟨a₀, ha₀A, hcase1⟩ :=
      non_redundant_b_gives_a A B b hbB (by omega) hB h (by omega) hcard
    exact absurd hcase1 (by have := hredA a₀ ha₀A; omega)
  -- Set-equality from card-equality
  have hredA_eq : ∀ a ∈ A, A.erase a + B = A + B := fun a haA =>
    Finset.eq_of_subset_of_card_le
      (Finset.add_subset_add_right (Finset.erase_subset _ _))
      (h.trans (hredA a haA).symm).le
  -- Case on B.card
  by_cases hB2 : B.card = 2
  · -- |B| = 2: orbit argument — A is closed under b₁-b₂, orbit of size p contradicts |A|<p
    have hA_lt_p : A.card < p := by omega
    obtain ⟨b₁, b₂, hne_b, hB_eq⟩ := Finset.card_eq_two.mp hB2
    have hb₁B : b₁ ∈ B := by rw [hB_eq]; exact Finset.mem_insert_self b₁ _
    have hd : b₁ - b₂ ≠ 0 := sub_ne_zero.mpr hne_b
    have hclosed : ∀ a ∈ A, a + (b₁ - b₂) ∈ A := by
      intro a haA
      have hmem : a + b₁ ∈ A.erase a + B := by
        rw [hredA_eq a haA]; exact Finset.mem_add.mpr ⟨a, haA, b₁, hb₁B, rfl⟩
      obtain ⟨a', ha'er, b', hb'B, heq⟩ := Finset.mem_add.mp hmem
      rw [Finset.mem_erase] at ha'er
      rw [hB_eq, Finset.mem_insert, Finset.mem_singleton] at hb'B
      rcases hb'B with rfl | rfl
      · exact absurd (add_right_cancel heq) ha'er.1
      · have ha'_val : a' = a + (b₁ - b₂) := by linear_combination heq
        rw [← ha'_val]; exact ha'er.2
    obtain ⟨a₀, ha₀A⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have horbit_nat : ∀ k : ℕ, a₀ + (k : ZMod p) * (b₁ - b₂) ∈ A := by
      intro k
      induction k with
      | zero => simpa using ha₀A
      | succ n ih =>
        have := hclosed _ ih
        convert this using 1
        push_cast; ring
    have horbit : ∀ k : Fin p, a₀ + (k : ZMod p) * (b₁ - b₂) ∈ A :=
      fun k => horbit_nat k.val
    have himg_card : (Finset.univ.image (fun k : Fin p =>
        a₀ + (k : ZMod p) * (b₁ - b₂))).card = p := by
      rw [Finset.card_image_of_injective _ (zmod_orbit_inj hd),
          Finset.card_univ, Fintype.card_fin]
    have himg_sub : (Finset.univ.image (fun k : Fin p =>
        a₀ + (k : ZMod p) * (b₁ - b₂))) ⊆ A :=
      fun _ hx => by obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx; exact horbit j
    linarith [Finset.card_le_card himg_sub]
  · -- |B| ≥ 3: double counting argument
    have hB3 : 3 ≤ B.card := by omega
    -- Each x ∈ A+B has ≥ 2 A-representations (any a that uniquely represents x contradicts hredA)
    have hrep2 : ∀ x ∈ A + B, 2 ≤ (A.filter (fun a => x - a ∈ B)).card := by
      intro x hx
      by_contra hlt2
      push_neg at hlt2
      have hpos : 0 < (A.filter (fun a => x - a ∈ B)).card := by
        obtain ⟨a, haA, b, hbB, hxab⟩ := Finset.mem_add.mp hx
        exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr
          ⟨haA, show x - a ∈ B by rw [show x - a = b from (eq_sub_of_add_eq hxab).symm]; exact hbB⟩⟩
      have hcard1 : (A.filter (fun a => x - a ∈ B)).card = 1 := by omega
      obtain ⟨a₁, ha₁⟩ := Finset.card_eq_one.mp hcard1
      have ha₁A : a₁ ∈ A := (Finset.mem_filter.mp (ha₁ ▸ Finset.mem_singleton_self a₁)).1
      have hxnotin : x ∉ A.erase a₁ + B := by
        intro hcontra
        obtain ⟨a', ha'er, b', hb'B, hsum'⟩ := Finset.mem_add.mp hcontra
        rw [Finset.mem_erase] at ha'er
        have ha'filt : a' ∈ A.filter (fun a => x - a ∈ B) :=
          Finset.mem_filter.mpr ⟨ha'er.2, (eq_sub_of_add_eq hsum') ▸ hb'B⟩
        rw [ha₁] at ha'filt
        exact ha'er.1 (Finset.mem_singleton.mp ha'filt)
      exact hxnotin (hredA_eq a₁ ha₁A ▸ hx)
    -- ∑_{x ∈ A+B} r(x) = |A|·|B| by double counting (bijection with A×B)
    have hsum_eq : ∑ x ∈ A + B, (A.filter (fun a => x - a ∈ B)).card = A.card * B.card := by
      rw [← Finset.card_sigma, ← Finset.card_product]
      apply Finset.card_bij (fun xa _ => (xa.2, xa.1 - xa.2))
      · intro ⟨x, a⟩ hmem
        simp only [Finset.mem_sigma, Finset.mem_filter] at hmem
        exact Finset.mem_product.mpr ⟨hmem.2.1, hmem.2.2⟩
      · intro ⟨x₁, a₁⟩ _ ⟨x₂, a₂⟩ _ heq
        simp only [Prod.mk.injEq] at heq
        obtain ⟨ha, hd⟩ := heq; obtain rfl := ha
        have h1 : x₁ = x₂ := by
          have := congr_arg (· + a₁) hd; simp only [sub_add_cancel] at this; exact this
        simp [h1]
      · intro (a, b) hmem
        rw [Finset.mem_product] at hmem
        obtain ⟨haA, hbB⟩ := hmem
        exact ⟨⟨a + b, a⟩,
          Finset.mem_sigma.mpr ⟨Finset.mem_add.mpr ⟨a, haA, b, hbB, rfl⟩,
            Finset.mem_filter.mpr ⟨haA, show a + b - a ∈ B by convert hbB using 1; ring⟩⟩,
          Prod.ext rfl (show a + b - a = b by ring)⟩
    have hlb : 2 * (A + B).card ≤ ∑ x ∈ A + B, (A.filter (fun a => x - a ∈ B)).card :=
      calc 2 * (A + B).card = ∑ _ ∈ A + B, 2 := by simp [Finset.sum_const, mul_comm]
        _ ≤ _ := Finset.sum_le_sum hrep2
    -- (|A|-2)(|B|-2) ≥ 2
    have hineq : 2 * (A.card + B.card - 1) ≤ A.card * B.card := by
      have := hsum_eq ▸ h ▸ hlb; omega
    -- Case |A|=3, |B|=3: 2*(3+3-1)=10 ≤ 3*3=9 is false → contradiction
    by_cases hAB3 : A.card = 3 ∧ B.card = 3
    · obtain ⟨hA3eq, hB3eq⟩ := hAB3
      rw [hA3eq, hB3eq] at hineq; norm_num at hineq
    · -- |A|≥4 or |B|≥4: (|A|-2)(|B|-2) ≥ 2, consistent with hineq.
      -- The counting argument is exhausted. Need Kneser's theorem (not in Mathlib) or
      -- a structural argument using Z/pZ having no proper non-trivial subgroups.
      -- The key fact: from hredA + hredB, both A and B are "translation-closed" in a
      -- union sense: ∀ a ∈ A, ∃ d ∈ (B-B)\{0}: a+d ∈ A. For |B|=2, d is unique →
      -- A is closed under a single translation → orbit of size p. For |B|≥3, multiple
      -- choices of d make the orbit argument fail without additional prime-group structure.
      sorry -- [HARD] Requires Kneser's theorem or complete restructuring of Vosper proof

end Erdos476OQ05Aristotle
