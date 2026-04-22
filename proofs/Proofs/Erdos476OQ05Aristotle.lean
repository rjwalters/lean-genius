/-
Aristotle targets for Erdős Problem #476 OQ05 (Vosper's Theorem)

Two key sorry'd lemmas from the Vosper proof:
  1. vosper_case1_exists  — find a non-redundant element in A (SORRY 1/2)
  2. vosper_ap_sdiff_card — AP has exactly 1 element with no d-predecessor (SORRY 2/2)

These are HARD lemmas — known mathematical results needing Lean formalization.
See Erdos476OQ05Problem.lean for the full Vosper proof context.

Mathematical context:
  Vosper's Theorem (1956): If |A+B| = |A|+|B|-1 < p in Z/pZ (p prime), |A|,|B| ≥ 2,
  then A and B are arithmetic progressions with the same common difference d.

  Proof structure:
    - Induction on |A|. Base case |A|=2 proved (vosper_base).
    - Inductive step: find a₀ ∈ A with |(A\{a₀})+B| = |A|+|B|-2 (SORRY 1).
    - Apply IH to A\{a₀} and B, get APs with diff d.
    - Show A is also AP: |A \ A.image(·+d)| = 1 (SORRY 2), apply ap_of_near_periodic.
-/
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05Aristotle

variable {p : ℕ} [hp : Fact p.Prime]

/- ###Definitions (matching Erdos476OQ05Problem.lean) -/

/-- An arithmetic progression in ZMod p starting at `a` with difference `d` -/
def IsArithmeticProgression (A : Finset (ZMod p)) (a d : ZMod p) : Prop :=
  A = (Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)

/- ###Helper lemmas (proved in Erdos476OQ05Problem.lean, restated here for Aristotle) -/

lemma shift_card_eq (B : Finset (ZMod p)) (d : ZMod p) :
    (B.image (· + d)).card = B.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  have h := congrArg (· - d) hxy
  simp only [add_sub_cancel_right] at h
  exact h

/-- If A is an AP with diff d and has ≥ 2 elements, then d ≠ 0. -/
lemma d_ne_zero_of_isAP {A : Finset (ZMod p)} {a d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hcard : 2 ≤ A.card) : d ≠ 0 := by
  intro hd
  have hAcard : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [IsArithmeticProgression, hd] at hA
    simp only [mul_zero, add_zero] at hA
    rw [hA] at hx hy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    rfl
  omega

/-- Key: if B \ B.image(·+d) has exactly 1 element and d ≠ 0 and |B| < p, then B is an AP. -/
lemma ap_of_near_periodic {B : Finset (ZMod p)} {d : ZMod p}
    (hd : d ≠ 0) (hlt : B.card < p)
    (h : (B \ (B.image (· + d))).card = 1) :
    ∃ b₀ : ZMod p, IsArithmeticProgression B b₀ d := by
  sorry -- This is proved in Erdos476OQ05Problem.lean; restated for context

/-- The pointwise sum of two AP-sets equals the expected range image. -/
lemma add_isAP_eq {A B : Finset (ZMod p)} {a b d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hB : IsArithmeticProgression B b d)
    (hApos : 0 < A.card) (hBpos : 0 < B.card) :
    A + B = (Finset.range (A.card + B.card - 1)).image (fun (k : ℕ) => (a + b) + (k : ZMod p) * d) := by
  apply Finset.Subset.antisymm
  · -- Forward: A + B ⊆ range.image
    intro x hx
    simp only [Finset.mem_add] at hx
    obtain ⟨xa, hxaA, xb, hxbB, rfl⟩ := hx
    rw [hA] at hxaA; rw [hB] at hxbB
    simp only [Finset.mem_image, Finset.mem_range] at hxaA hxbB
    obtain ⟨i, hi, rfl⟩ := hxaA
    obtain ⟨j, hj, rfl⟩ := hxbB
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨i + j, by omega, ?_⟩
    simp only [Nat.cast_add]; ring
  · -- Reverse: range.image ⊆ A + B
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    let i := min k (A.card - 1)
    let j := k - i
    have hi : i < A.card := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hApos Nat.one_pos)
    have hj : j < B.card := by
      simp only [i, j]
      rcases le_or_gt k (A.card - 1) with h | h
      · simp [Nat.min_eq_left h]; exact Finset.card_pos.mp hBpos
      · have : min k (A.card - 1) = A.card - 1 := Nat.min_eq_right (by omega)
        simp [this]; omega
    have h_ij : i + j = k := by simp only [i, j]; omega
    simp only [Finset.mem_add]
    refine ⟨a + (i : ZMod p) * d, ?_, b + (j : ZMod p) * d, ?_, ?_⟩
    · rw [hA]; simp only [Finset.mem_image, Finset.mem_range]; exact ⟨i, hi, rfl⟩
    · rw [hB]; simp only [Finset.mem_image, Finset.mem_range]; exact ⟨j, hj, rfl⟩
    · have hk : (k : ZMod p) = (i : ZMod p) + j := by
        have h := congrArg (Nat.cast (R := ZMod p)) h_ij.symm
        rwa [Nat.cast_add] at h
      rw [hk]; ring

/-- Sum of two APs with same diff is an AP, given CD equality. -/
lemma isAP_sum {A B : Finset (ZMod p)} {a b d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hB : IsArithmeticProgression B b d)
    (hApos : 0 < A.card) (hBpos : 0 < B.card)
    (hABcard : (A + B).card = A.card + B.card - 1) :
    IsArithmeticProgression (A + B) (a + b) d := by
  unfold IsArithmeticProgression
  rw [hABcard]
  exact add_isAP_eq hA hB hApos hBpos

/- ###SORRY 1: Case 1 existence (key lemma for Vosper inductive step) -/

/-- **Vosper Case 1 Existence**: In the inductive step of Vosper's theorem,
    there exists a₀ ∈ A such that removing a₀ gives CD equality for A\{a₀}+B.

    Proof strategy: By contradiction, if all a ∈ A are "redundant" (Case 2), then:
    - Every x ∈ A+B has at least 2 representations from A×B.
    - Counting: |A|·|B| ≥ 2·|A+B| = 2(|A|+|B|-1), i.e., (|A|-2)(|B|-2) ≥ 2.
    - This fails for (|A|-2)(|B|-2) < 2 (|B|=2 always, |A|=3,|B|=3).
    - For the general case with (|A|-2)(|B|-2) ≥ 2: apply the "iterative removal"
      argument showing A+B = {a*}+B for any singleton, contradicting |A+B| > |B|. -/
theorem vosper_case1_exists (A B : Finset (ZMod p))
    (hA3 : 2 < A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card - 1 < p) :
    ∃ a₀ ∈ A, ((A.erase a₀) + B).card = A.card + B.card - 2 := by
  sorry

/- ###SORRY 2: AP sdiff cardinality (key lemma for Vosper AP extension) -/

/-- **Vosper AP Sdiff Card**: Given IsAP(A\{a₀}, a₁, d) and IsAP(B, b₀, d),
    the set A has exactly 1 element with no d-predecessor in A.

    Proof strategy:
    1. isAP_sum gives IsAP(A'+B, a₁+b₀, d) where A' = A.erase a₀.
    2. a₀+B = AP(a₀+b₀, d, |B|). |a₀+B \ A'+B| = |A+B| - |A'+B| = 1.
    3. Let c = (a₀-a₁)·d⁻¹ ∈ ZMod p. Elements of a₀+B at "positions" {c,...,c+m-1}.
       A'+B at positions {0,...,n'+m-2} (n' = |A'|, m = |B|). Both have same diff d.
    4. |{c,...,c+m-1} \ {0,...,n'+m-2}| = 1 forces c = n' (successor) or c = p-1 (≡ -1).
    5. c = n' → a₀ = a₁+n'·d (successor): A\A.image(·+d) = {a₁} (the AP start).
       c = p-1 → a₀ = a₁-d (predecessor): A\A.image(·+d) = {a₀} (the new start).
    6. In both cases |A \ A.image(·+d)| = 1. -/
theorem vosper_ap_sdiff_card
    (A : Finset (ZMod p)) (a₀ a₁ b₀ d : ZMod p) (B : Finset (ZMod p))
    (ha₀A : a₀ ∈ A)
    (hA3 : 2 < A.card)
    (hB : 2 ≤ B.card)
    (hlt : A.card + B.card - 1 < p)
    (hAB : (A + B).card = A.card + B.card - 1)
    (hcase1 : ((A.erase a₀) + B).card = A.card + B.card - 2)
    (hAP_A' : IsArithmeticProgression (A.erase a₀) a₁ d)
    (hAP_B : IsArithmeticProgression B b₀ d) :
    (A \ A.image (· + d)).card = 1 := by
  sorry

end Erdos476OQ05Aristotle
