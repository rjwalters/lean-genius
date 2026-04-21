/-
Erdős Problem #476, Open Question 5: Vosper's Theorem (1956)

Source: Follow-up to erdos-476 (Erdős-Heilbronn conjecture)
Status: PARTIAL — infrastructure proved (4 lemmas), 3 sorries remain

Statement (Vosper 1956):
Let p be prime, A, B ⊆ Z/pZ with |A|, |B| ≥ 2.
If |A + B| = |A| + |B| - 1 (Cauchy-Davenport equality) and |A + B| < p,
then A and B are arithmetic progressions with the same common difference d.

Proof Strategy:
  1. Define arithmetic progressions in ZMod p.
  2. Key sublemma: if the "forward shift" B → B+d removes exactly 1 element from B
     (i.e., |B \ (B + d)| = 1), then B is an AP with difference d.
  3. For |A| = 2: A = {a, a+d} is trivially an AP; equality in CD forces
     |B ∩ (B + d)| = |B| - 1, hence B is an AP by the key sublemma.
  4. General induction on |A|: reduce to smaller cases by removing elements.

Proved (0 sorries):
  - IsArithmeticProgression (definition)
  - isAP_singleton, isAP_pair, isAP_shift, shift_card_eq

Remaining (3 sorries):
  - ap_of_near_periodic: backward-shift induction on |B|
  - vosper_base: base case |A|=2 using ap_of_near_periodic
  - vosper: full theorem by induction on |A|

References:
  - Vosper, A.G. (1956): "The fractions of subsets of integers summing to a given value"
  - Nathanson, M.B. (1996): Additive Number Theory: Inverse Problems, §2.4
  - Mathlib: ZMod.cauchy_davenport (Mathlib.Combinatorics.Additive.CauchyDavenport)
-/

import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.IntervalCases

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Arithmetic Progressions in ZMod p -/

/-- An arithmetic progression in ZMod p starting at `a` with difference `d`:
    the set `{a, a+d, a+2d, ..., a+(k-1)d}` where `k = A.card`.

    The parameter `i : ℕ` ranges over {0, ..., k-1} and is cast to ZMod p. -/
def IsArithmeticProgression (A : Finset (ZMod p)) (a d : ZMod p) : Prop :=
  A = (Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)

/-! ### Basic AP Infrastructure -/

/-- Translation preserves cardinality: |B.image (·+d)| = |B|. -/
lemma shift_card_eq (B : Finset (ZMod p)) (d : ZMod p) :
    (B.image (· + d)).card = B.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  -- x + d = y + d → x = y by subtracting d from both sides
  have h := congrArg (· - d) hxy
  simp only [add_sub_cancel_right] at h
  exact h

/-- Every singleton is an arithmetic progression (with any common difference). -/
lemma isAP_singleton (a d : ZMod p) :
    IsArithmeticProgression ({a} : Finset (ZMod p)) a d := by
  simp [IsArithmeticProgression]

/-- A two-element set {a, b} (with a ≠ b) is an AP starting at a with difference b - a. -/
lemma isAP_pair (a b : ZMod p) (hab : a ≠ b) :
    IsArithmeticProgression ({a, b} : Finset (ZMod p)) a (b - a) := by
  rw [IsArithmeticProgression, Finset.card_pair hab]
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨1, by omega, by simp only [Nat.cast_one, one_mul]; ring⟩
  · rintro ⟨i, hi, rfl⟩
    have h_cases : i = 0 ∨ i = 1 := by omega
    rcases h_cases with rfl | rfl
    · left; simp  -- i = 0: a + (0 : ZMod p) * (b - a) = a
    · right; simp only [Nat.cast_one, one_mul]; ring  -- i = 1: a + 1 * (b - a) = b

/-- Translating an AP by a constant `c` gives an AP with the same difference. -/
lemma isAP_shift (A : Finset (ZMod p)) (a d c : ZMod p)
    (h : IsArithmeticProgression A a d) :
    IsArithmeticProgression (A.image (· + c)) (a + c) d := by
  unfold IsArithmeticProgression at h ⊢
  rw [shift_card_eq A c]
  -- Rewrite A.image (· + c) on LHS without touching A.card on RHS
  have step1 : A.image (· + c) =
      ((Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)).image (· + c) := by
    congr 1; exact h
  rw [step1, Finset.image_image]
  congr 1
  ext i
  simp only [Function.comp_apply]
  ring

/-! ### The Key "Near-Periodic" Lemma -/

/-- **Key Lemma**: If B ⊆ ZMod p (p prime) with d ≠ 0 and |B| < p, and
    the "shifted complement" |B \ (B.image (· + d))| = 1, then B is an
    arithmetic progression with common difference d.

    Proof idea (backward-shift induction on |B|):
    - Let {b₀} = B \ (B.image (· + d)). Then b₀ has no predecessor: b₀ - d ∉ B.
    - Every b ∈ B \ {b₀} satisfies b - d ∈ B.
    - Starting from any b ∈ B, repeatedly subtracting d stays in B until reaching b₀.
    - Since |B| < p and d ≠ 0, this backward sequence has length exactly |B|.
    - Thus B = {b₀, b₀+d, ..., b₀+(|B|-1)d}.

    Sorry: the Lean formalization of the backward-shift induction requires a
    well-founded recursion argument pending in this session. -/
lemma ap_of_near_periodic {B : Finset (ZMod p)} {d : ZMod p}
    (hd : d ≠ 0) (hlt : B.card < p)
    (h : (B \ (B.image (· + d))).card = 1) :
    ∃ b₀ : ZMod p, IsArithmeticProgression B b₀ d := by
  sorry

/-! ### Vosper's Theorem -/

/-- **Vosper Base Case**: For |A| = 2, the equality |A+B| = |B|+1 forces B to be an AP
    with the same difference d = (second element of A) - (first element of A). -/
lemma vosper_base (A B : Finset (ZMod p)) (hA : A.card = 2) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1) (hlt : A.card + B.card - 1 < p) :
    ∃ (d a₀ b₀ : ZMod p),
      IsArithmeticProgression A a₀ d ∧ IsArithmeticProgression B b₀ d := by
  /- Key computation:
     - A = {a, b} (two elements), d := b - a
     - A + B = {a} + B ∪ {b} + B = (a + B) ∪ (b + B)
     - |(a+B) ∩ (b+B)| = |(a+B)| + |(b+B)| - |A+B| = 2|B| - (|B|+1) = |B|-1
     - |B ∩ (d+B)| = |B|-1 (translating), so |B \ (d+B)| = 1
     - By ap_of_near_periodic: B is an AP with difference d -/
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
  have hA_ap : IsArithmeticProgression ({a, b} : Finset (ZMod p)) a (b - a) :=
    isAP_pair a b hab
  sorry

/-- **Vosper's Theorem** (1956): equality case of Cauchy-Davenport.
    If p is prime, A, B ⊆ Z/pZ, |A|, |B| ≥ 2, |A+B| = |A|+|B|-1, and |A+B| < p,
    then A and B are arithmetic progressions with the same common difference d. -/
theorem vosper (A B : Finset (ZMod p)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1) (hlt : A.card + B.card - 1 < p) :
    ∃ (d a₀ b₀ : ZMod p),
      IsArithmeticProgression A a₀ d ∧ IsArithmeticProgression B b₀ d := by
  /- Proof by strong induction on |A|.
     Base |A| = 2: apply vosper_base.
     Step |A| ≥ 3: remove element a ∈ A.
       - A' = A \ {a}, |A'| = |A| - 1 ≥ 2
       - CD: |A'+B| ≥ min(p, |A'|+|B|-1) = |A|+|B|-2
       - Containment: A'+B ⊆ A+B, so |A'+B| ≤ |A|+|B|-1
       - Equality must hold: |A'+B| = |A'|+|B|-1
       - By IH: A', B are APs with same difference d
       - Then a must extend A' by exactly ±d, so A is an AP -/
  sorry

end Erdos476OQ05
