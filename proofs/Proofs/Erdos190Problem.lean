/-
Erdős Problem #190: Canonical Ramsey Number for Arithmetic Progressions

Source: https://erdosproblems.com/190
Status: OPEN

Statement:
Let H(k) denote the smallest N such that any finite coloring of {1, ..., N}
(using any number of colors) guarantees either:
- a monochromatic k-term arithmetic progression, OR
- a rainbow k-term arithmetic progression (all elements have different colors)

Questions:
1. Estimate H(k)
2. Is it true that H(k)^{1/k}/k → ∞ as k → ∞?

Known Results:
- H(k) exists for all k (follows from Szemerédi's theorem)
- H(k)^{1/k} → ∞ as k → ∞ (straightforward)
- Better bounds remain open

Key Insight:
This is a "canonical" Ramsey theory problem. Unlike van der Waerden numbers
(which only require monochromatic APs), H(k) allows rainbow APs as an
alternative "win condition". However, H(k) ≥ W(k;2): for 2-colorings,
rainbow k-APs are impossible for k ≥ 3, so canonical = monochromatic.

References:
- Erdős-Graham [ErGr79, p.333]
- Erdős-Graham [ErGr80, p.17]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

namespace Erdos190

/- ## Part I: Arithmetic Progressions -/

/--
**k-term Arithmetic Progression**

A sequence a, a+d, a+2d, ..., a+(k-1)d with common difference d.
-/
def isArithmeticProgression (s : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ s = (Finset.range k).image (fun i => a + i * d)

/-- Alternative definition: equally spaced elements. -/
def isAPSequence (f : Fin k → ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : Fin k, f i = a + i.val * d

/- ## Part II: Colorings -/

/--
**Coloring of an Interval**

A coloring of {1, ..., N} assigns each element a color from some set C.
-/
def Coloring (N : ℕ) (C : Type*) := Fin N → C

/--
**Monochromatic Set**

A set S is monochromatic if all elements have the same color.
-/
def isMonochromatic {N C : Type*} (χ : N → C) (s : Finset N) : Prop :=
  ∃ c : C, ∀ x ∈ s, χ x = c

/--
**Rainbow Set**

A set S is rainbow if all elements have distinct colors.
-/
def isRainbow {N C : Type*} [DecidableEq C] (χ : N → C) (s : Finset N) : Prop :=
  s.card = (s.image χ).card

/-- Alternative: all pairs have different colors. -/
def isRainbowAlt {N C : Type*} (χ : N → C) (s : Finset N) : Prop :=
  ∀ x y : N, x ∈ s → y ∈ s → x ≠ y → χ x ≠ χ y

/- ## Part III: The Canonical Property -/

/--
**Canonical Property for Arithmetic Progressions**

A coloring has the canonical property for k-APs if it contains either
a monochromatic k-AP or a rainbow k-AP.
-/
def hasCanonicalAP {N C : Type*} [DecidableEq C] (χ : Fin N → C) (k : ℕ) : Prop :=
  ∃ f : Fin k → Fin N,
    isAPSequence (fun i => (f i).val) ∧
    (isMonochromatic χ (Finset.image f Finset.univ) ∨
     isRainbow χ (Finset.image f Finset.univ))

/- ## Part IV: The H(k) Function -/

/--
**H(k): The Canonical Ramsey Number**

H(k) is the smallest N such that every coloring of {1, ..., N}
has the canonical property for k-term arithmetic progressions.
-/
noncomputable def H (k : ℕ) : ℕ :=
  Nat.find (exists_canonical_threshold k)

/-- H(k) is well-defined (existence follows from Szemerédi). -/
axiom exists_canonical_threshold (k : ℕ) :
    ∃ N : ℕ, ∀ (C : Type) [DecidableEq C] (χ : Fin N → C), hasCanonicalAP χ k

/-- For N ≥ H(k), every coloring has the canonical property.
    Proof: restrict χ : Fin N → C to Fin (H k) via Fin.castLE,
    apply Nat.find_spec, then lift the AP back via Fin.castLE.
    The monochromatic/rainbow property transfers because castLE is injective. -/
theorem H_spec (k N : ℕ) (hN : N ≥ H k) :
    ∀ (C : Type) [DecidableEq C] (χ : Fin N → C), hasCanonicalAP χ k := by
  intro C _ χ
  have hle : H k ≤ N := hN
  -- Restrict coloring to first H(k) elements
  let χ' : Fin (H k) → C := χ ∘ Fin.castLE hle
  -- By Nat.find_spec, χ' has a canonical AP
  obtain ⟨f, hAP, hColor⟩ := Nat.find_spec (exists_canonical_threshold k) C χ'
  -- Lift AP to Fin N: castLE preserves .val so AP property transfers
  have hinj := Fin.castLE_injective hle
  refine ⟨Fin.castLE hle ∘ f, ?_, ?_⟩
  · -- isAPSequence preserved: castLE preserves .val
    obtain ⟨a, d, hd, hf⟩ := hAP
    exact ⟨a, d, hd, fun i => by simp [Fin.castLE, hf i]⟩
  · -- Coloring property transfers via castLE
    have himg : Finset.image (Fin.castLE hle ∘ f) Finset.univ =
        Finset.image (Fin.castLE hle) (Finset.image f Finset.univ) := by
      rw [← Finset.image_comp]
    rw [himg]
    cases hColor with
    | inl hMono =>
      left
      obtain ⟨c, hc⟩ := hMono
      exact ⟨c, fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact hc y hy⟩
    | inr hRain =>
      right
      unfold isRainbow at hRain ⊢
      rw [Finset.card_image_of_injective _ hinj, Finset.image_image]
      exact hRain

/-- H(k) is the minimum such N.
    Proof: direct from Nat.find_min (minimality of Nat.find). -/
theorem H_minimal (k N : ℕ) (hN : N < H k) :
    ∃ (C : Type) (_ : DecidableEq C) (χ : Fin N → C), ¬ hasCanonicalAP χ k := by
  -- H k = Nat.find ..., so hN : N < Nat.find ...
  have h := Nat.find_min (exists_canonical_threshold k) hN
  -- h : ¬(∀ C [DecidableEq C] χ, hasCanonicalAP χ k) at Fin N
  push_neg at h
  exact h

/- ## Part V: Relation to van der Waerden Numbers -/

/--
**Van der Waerden Number W(k)**

W(k) is the smallest N such that every 2-coloring of {1, ..., N}
contains a monochromatic k-term AP. Existence is van der Waerden's theorem.
-/
axiom vanDerWaerden_exists (k : ℕ) :
    ∃ N : ℕ, ∀ (χ : Fin N → Bool), ∃ s : Finset (Fin N),
      isArithmeticProgression (s.image Fin.val) k ∧ isMonochromatic χ s

noncomputable def W (k : ℕ) : ℕ :=
  Nat.find (vanDerWaerden_exists k)

/-- W(k) ≤ H(k): for 2-colorings, rainbow k-APs (k ≥ 3) are impossible since Bool
    has only 2 elements. So the canonical condition reduces to monochromatic, meaning
    H(k) satisfies the van der Waerden property. -/
theorem W_le_H (k : ℕ) (hk : k ≥ 3) : W k ≤ H k := by
  -- Show H k satisfies the van der Waerden property, then Nat.find_min'
  apply Nat.find_min' (vanDerWaerden_exists k)
  intro χ
  -- Get canonical AP from H_spec
  obtain ⟨f, hAP, hColor⟩ := H_spec k (H k) le_rfl Bool χ
  obtain ⟨a, d, hd, hf⟩ := hAP
  -- Provide the Finset and properties
  refine ⟨image f univ, ?_, ?_⟩
  · -- isArithmeticProgression (s.image Fin.val) k
    refine ⟨a, d, hd, ?_⟩
    rw [image_image]
    ext x
    simp only [mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.val, i.isLt, hf i⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, hf ⟨i, hi⟩⟩
  · -- isMonochromatic χ s (rainbow is impossible for Bool with k ≥ 3)
    rcases hColor with hMono | hRain
    · exact hMono
    · -- Rainbow: s.card = (s.image χ).card, but s.card ≥ 3 and (s.image χ).card ≤ 2
      exfalso
      unfold isRainbow at hRain
      have hf_inj : Function.Injective f := by
        intro i j hij
        have := congr_arg Fin.val hij
        rw [hf i, hf j] at this
        exact Fin.ext (by omega)
      have hs : (image f univ).card = k := by
        rw [card_image_of_injective _ hf_inj, card_univ, Fintype.card_fin]
      have himg : ((image f univ).image χ).card ≤ 2 := by
        calc ((image f univ).image χ).card
            ≤ (univ : Finset Bool).card := card_le_card (subset_univ _)
          _ = 2 := by decide
      rw [hs] at hRain; omega

/-- H(k) ≥ k for k ≥ 1: a k-term AP a, a+d, ..., a+(k-1)d with d ≥ 1
    requires N ≥ k (since the max value a+(k-1)d ≥ k-1).
    Strengthened from original k ≥ 3 to k ≥ 1. -/
theorem H_lower_bound (k : ℕ) (hk : k ≥ 1) : H k ≥ k := by
  by_contra h
  push_neg at h  -- h : H k < k
  -- Nat.find_spec gives a canonical AP for any coloring of Fin (H k)
  obtain ⟨f, ⟨a, d, hd, hf⟩, _⟩ :=
    Nat.find_spec (exists_canonical_threshold k) (Fin (H k)) (fun x => x)
  -- f : Fin k → Fin (H k) with f i = a + i * d, d > 0
  -- The last element: a + (k-1)*d < H k
  have hval := hf ⟨k - 1, by omega⟩
  have hlt := (f ⟨k - 1, by omega⟩).isLt
  -- But a + (k-1)*d ≥ (k-1)*1 = k-1 (since d ≥ 1)
  have hge : k - 1 ≤ a + (k - 1) * d := by
    calc k - 1 = (k - 1) * 1 := by omega
      _ ≤ (k - 1) * d := Nat.mul_le_mul_left _ (by omega : 1 ≤ d)
      _ ≤ a + (k - 1) * d := Nat.le_add_left _ _
  -- k-1 ≤ a+(k-1)*d < H k < k — no natural between k-1 and k
  omega

/- ## Part VI: Known Asymptotic Results -/

/--
**H(k)^{1/k} → ∞**

This is known: the k-th root of H(k) goes to infinity.
-/
axiom H_root_to_infinity :
    ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, (H k : ℝ) ^ (1 / k : ℝ) > M

/--
**Conjecture: H(k)^{1/k}/k → ∞**

The stronger question asks whether H(k)^{1/k} grows faster than k.
Equivalently, H(k) > k^k eventually.
-/
def erdos190Conjecture : Prop :=
    ∀ M : ℕ, ∃ K : ℕ, ∀ k ≥ K, (H k : ℝ) ^ (1 / k : ℝ) / k > M

-- Note: erdos190Conjecture is OPEN — not asserted as an axiom.
-- Previous unsound `axiom erdos_190` removed.

/- ## Part VIII: Connections -/

/--
**Connection to Szemerédi's Theorem**

Szemerédi's theorem guarantees that any dense subset of ℕ contains
arbitrarily long APs. This implies H(k) exists: for large enough N,
either we find a monochromatic AP (by density) or we've used many
colors, increasing the chance of a rainbow AP.
-/

/--
**Canonical vs Standard Ramsey Theory**

In standard Ramsey theory, we want monochromatic structures.
In canonical Ramsey theory, we allow "canonical" patterns like
rainbow colorings. This typically gives smaller numbers.
-/

/- ## Part IX: Why This Is Hard -/

/--
**The Difficulty**

The challenge is obtaining precise asymptotics for H(k).

Known:
- H(k)^{1/k} → ∞ (not hard)

Unknown:
- Does H(k)^{1/k}/k → ∞?
- Precise bounds on H(k)

The interplay between monochromatic and rainbow conditions makes
the analysis subtle. Rainbow APs require many distinct colors,
which competes with the pigeonhole principle that pushes toward
monochromatic structures.
-/

/- ## Part X: Summary -/

/--
**H(k) is Positive (for k ≥ 1)**

For k ≥ 1: hasCanonicalAP χ k requires f : Fin k → Fin N, which doesn't
exist for N = 0 (since Fin 0 is empty but Fin k is nonempty). So H(k) ≥ 1.
Note: H(0) = 0 since the empty AP trivially satisfies the condition.
-/
theorem H_pos (k : ℕ) (hk : k ≥ 1) : H k > 0 := by
  by_contra h
  push_neg at h
  have hH0 : H k = 0 := by omega
  have hspec := Nat.find_spec (exists_canonical_threshold k)
  rw [hH0] at hspec
  have hfalse := hspec Bool Fin.elim0
  obtain ⟨f, _, _⟩ := hfalse
  exact Fin.elim0 (f ⟨0, by omega⟩)

/--
**Erdős Problem #190: Summary**

**Questions:**
1. Estimate H(k) - the canonical Ramsey number for k-APs
2. Is H(k)^{1/k}/k → ∞?

**Status:** OPEN

**Known:**
- H(k) exists (via Szemerédi's theorem)
- H(k)^{1/k} → ∞
- W(k) ≤ H(k) (proved: canonical reduces to monochromatic for 2-colorings)

**Key Challenge:**
Determining whether the growth rate is super-exponential in a
strong sense (faster than k^k).
-/
theorem erdos_190_summary :
    -- H(k) is positive for k ≥ 1
    (∀ k, k ≥ 1 → H k > 0) ∧
    -- H(k)^{1/k} → ∞
    (∀ M : ℕ, ∃ K, ∀ k ≥ K, (H k : ℝ) ^ (1 / k : ℝ) > M) ∧
    -- W(k) ≤ H(k) for k ≥ 3
    (∀ k, k ≥ 3 → W k ≤ H k) :=
  ⟨H_pos, H_root_to_infinity, W_le_H⟩

-- The main conjecture (OPEN): H(k)^{1/k}/k → ∞, i.e., H(k) grows
-- faster than k^k. This remains unresolved.

end Erdos190
