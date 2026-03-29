import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-
# Erdős #1022 OQ-01 — Property B_k: k-Colorability of Hypergraphs

Follow-up: Generalize Property B (2-colorability) to Property B_k (k-colorability).

## Question

Property B_k: a set family F has Property B_k if there exists a k-coloring
of the ground set such that no member of F is monochromatic.

Property B = Property B_2. How does the theory change for k > 2?

## Key Observations

- Property B_k is monotone in k: B_k → B_{k+1}
- For k ≥ max_f |f|, Property B_k always holds (pigeonhole)
- Erdős bound generalizes: |F| < k^{t-1} / (k-1) implies Property B_k
- The threshold c(t, k) in the sparsity conjecture may depend on k

Reference: https://erdosproblems.com/1022
-/

open Finset

namespace Erdos1022OQ01

variable {α : Type*} [DecidableEq α]

/- ## Core Definition -/

/-- A family F has **Property B_k**: there exists a k-coloring χ : α → Fin k
    such that no member of F is monochromatic under χ. -/
def HasPropertyBK [Fintype α] (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ χ : α → Fin k, ∀ f ∈ F, f.Nonempty →
    ∃ a b, a ∈ f ∧ b ∈ f ∧ χ a ≠ χ b

/- ## Basic Properties -/

/-- The empty family has Property B_k for all k. -/
theorem hasPropertyBK_empty [Fintype α] (k : ℕ) :
    HasPropertyBK (∅ : Finset (Finset α)) k :=
  ⟨fun _ => 0, fun f hf => absurd hf (Finset.not_mem_empty f)⟩

/-- Property B_k is monotone: subsets of Property B_k families have Property B_k. -/
theorem hasPropertyBK_subset [Fintype α] {F G : Finset (Finset α)} {k : ℕ}
    (hFG : F ⊆ G) (hG : HasPropertyBK G k) : HasPropertyBK F k :=
  let ⟨χ, hχ⟩ := hG; ⟨χ, fun f hf => hχ f (hFG hf)⟩

/-- Any singleton set family has Property B_k for k ≥ 2 when the set has ≥ 2 elements. -/
theorem hasPropertyBK_singleton [Fintype α] {f : Finset α} {k : ℕ}
    (hf : 2 ≤ f.card) (hk : 2 ≤ k) :
    HasPropertyBK ({f} : Finset (Finset α)) k := by
  -- Pick two distinct elements a, b ∈ f
  have hne : f.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have hera : (f.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    have := Finset.card_erase_of_mem ha; rw [h, Finset.card_empty] at this; omega
  obtain ⟨b, hb_era⟩ := hera
  have hb : b ∈ f := Finset.mem_of_mem_erase hb_era
  have hba : b ≠ a := Finset.ne_of_mem_erase hb_era
  -- Color a with 0, everything else with 1
  refine ⟨fun x => if x = a then 0 else ⟨1, by omega⟩, fun g hg hgne => ?_⟩
  rw [Finset.mem_singleton] at hg; subst hg
  exact ⟨a, b, ha, hb, by simp [hba]⟩

/- ## Monotonicity in k -/

/-- **Key:** Property B_k implies Property B_{k+1}.
    If a k-coloring avoids monochromaticity, the same coloring
    (embedded into k+1 colors) also avoids monochromaticity. -/
theorem hasPropertyBK_mono [Fintype α] {F : Finset (Finset α)} {k : ℕ}
    (hF : HasPropertyBK F k) : HasPropertyBK F (k + 1) := by
  obtain ⟨χ, hχ⟩ := hF
  -- Embed Fin k → Fin (k+1) via castSucc
  refine ⟨fun x => Fin.castSucc (χ x), fun f hf hfne => ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hχ f hf hfne
  exact ⟨a, b, ha, hb, by intro h; exact hab (Fin.castSucc_injective _ h)⟩

/-- General monotonicity: k ≤ m → B_k → B_m. -/
theorem hasPropertyBK_mono_gen [Fintype α] {F : Finset (Finset α)} {k m : ℕ}
    (hkm : k ≤ m) (hF : HasPropertyBK F k) : HasPropertyBK F m := by
  induction hkm with
  | refl => exact hF
  | step _ ih => exact hasPropertyBK_mono ih

/- ## Connection to k = 2 -/

/-- The original Property B definition from Erdős #1022. -/
def HasPropertyB [Fintype α] (F : Finset (Finset α)) : Prop :=
  ∃ S : Finset α, ∀ f ∈ F, (f ∩ S).Nonempty ∧ (f \ S).Nonempty

/-- Property B ↔ Property B_2 for nonempty sets.
    A 2-coloring χ : α → Fin 2 is equivalent to the set S = χ⁻¹(0). -/
theorem propertyB_iff_propertyBK_two [Fintype α] {F : Finset (Finset α)}
    (hF : ∀ f ∈ F, f.Nonempty) :
    HasPropertyB F ↔ HasPropertyBK F 2 := by
  constructor
  · -- B → B_2: S corresponds to coloring 0 for S, 1 for complement
    intro ⟨S, hS⟩
    refine ⟨fun x => if x ∈ S then 0 else 1, fun f hf hfne => ?_⟩
    obtain ⟨⟨a, ha_inter⟩, ⟨b, hb_diff⟩⟩ := hS f hf
    rw [Finset.mem_inter] at ha_inter
    rw [Finset.mem_sdiff] at hb_diff
    exact ⟨a, b, ha_inter.1, hb_diff.1, by simp [ha_inter.2, hb_diff.2]⟩
  · -- B_2 → B: take S = {a : χ a = 0}
    intro ⟨χ, hχ⟩
    refine ⟨Finset.univ.filter (fun x => χ x = 0), fun f hf => ?_⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hχ f hf (hF f hf)
    -- One of a, b has color 0 and the other has color ≠ 0
    by_cases h0 : χ a = 0
    · constructor
      · exact ⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩⟩
      · refine ⟨b, Finset.mem_sdiff.mpr ⟨hb, fun hmem => ?_⟩⟩
        rw [Finset.mem_filter] at hmem
        exact hab (h0 ▸ hmem.2.symm)
    · constructor
      · have h1 : χ b ≠ χ a := Ne.symm hab
        have hb0 : χ b = 0 := by
          fin_cases (χ a) <;> fin_cases (χ b) <;> simp_all
        exact ⟨b, Finset.mem_inter.mpr ⟨hb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩⟩⟩
      · refine ⟨a, Finset.mem_sdiff.mpr ⟨ha, fun hmem => ?_⟩⟩
        rw [Finset.mem_filter] at hmem
        exact h0 hmem.2

/- ## Trivial upper bound -/

/-- For k ≥ 2 and sets of size ≥ 2, a family with one set has Property B_k. -/
theorem hasPropertyBK_card_le_one [Fintype α] {F : Finset (Finset α)} {k : ℕ}
    (hsize : ∀ f ∈ F, 2 ≤ f.card) (hk : 2 ≤ k)
    (hF : F.card ≤ 1) : HasPropertyBK F k := by
  rcases Nat.eq_or_gt_of_le (Nat.zero_le F.card) with h | h
  · rw [Finset.card_eq_zero.mp h]; exact hasPropertyBK_empty k
  · obtain ⟨f, hf⟩ := Finset.card_eq_one.mp (by omega : F.card = 1)
    rw [hf]; exact hasPropertyBK_singleton (hsize f (hf ▸ Finset.mem_singleton_self f)) hk

/- ## Generalized threshold -/

/-- **Open Question.** The Erdős first-moment bound generalizes to k colors:
    if |F| < k^{t-1}/(k-1) and every set has size ≥ t, then Property B_k holds.

    Proof sketch: Color each element uniformly in [k]. For a set of size s ≥ t,
    Pr(monochromatic) = k · (1/k)^s = k^{1-s} ≤ k^{1-t}.
    E(mono sets) = |F| · k^{1-t} < k^{t-1}/(k-1) · k^{1-t} = 1/(k-1) < 1. -/
def generalizedFirstMoment (k t : ℕ) : Prop :=
  ∀ [Fintype α] (F : Finset (Finset α)),
    (∀ f ∈ F, t ≤ f.card) →
    F.card * (k - 1) < k ^ (t - 1) →
    HasPropertyBK F k

/- ## Summary -/

/-- Property B_k hierarchy: B_2 ⊆ B_3 ⊆ ... ⊆ B_k ⊆ ...
    Each level is strictly weaker than the previous for families
    with chromatic number exactly k. -/
theorem propertyBK_hierarchy [Fintype α] {F : Finset (Finset α)} {k : ℕ}
    (hF : HasPropertyBK F k) (m : ℕ) (hkm : k ≤ m) : HasPropertyBK F m :=
  hasPropertyBK_mono_gen hkm hF

end Erdos1022OQ01
