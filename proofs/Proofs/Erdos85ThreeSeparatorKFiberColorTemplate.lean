import Proofs.Erdos85ThreeSeparatorUniformKFiberSurplus

/-!
# Separator-color template for the K-fiber intersection graph

Two K-centers that share a separator neighbor have disjoint X-fibers,
since an intersection point together with that separator point would give
two common neighbors.  Applying this exclusion to the wing colors and the
six-cycle points gives the three forbidden-adjacency assertions in (B41).
-/

open Finset

namespace Erdos85

/-- Abstract form of the B41 color template.  `F k` is the X-fiber of a
K-center, `I k` its separator-incidence set, `Kw w` the ordinary K-wing of
color `w`, and `p w` the P-point complementary to that color. -/
theorem KFiber_separator_color_template
    {V : Type*} [DecidableEq V]
    (K W P : Finset V) (c : V)
    (F I : V → Finset V) (Kw : V → Finset V) (p : V → V)
    (hcommonDisjoint : ∀ k ∈ K, ∀ l ∈ K, ∀ w ∈ W,
      w ∈ I k → w ∈ I l → Disjoint (F k) (F l))
    (hwing : ∀ w ∈ W, ∀ k ∈ Kw w, k ∈ K ∧ w ∈ I k)
    (hPK : P ⊆ K)
    (hPcommon : ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
      ∃ w ∈ W, w ∈ I p₁ ∧ w ∈ I p₂)
    (hpP : ∀ w ∈ W, p w ∈ P)
    (hpOutsideCommon : ∀ w ∈ W, ∀ k ∈ K,
      k ≠ c → k ∉ Kw w → ∃ v ∈ W, v ∈ I (p w) ∧ v ∈ I k) :
    (∀ w ∈ W, ∀ k₁ ∈ Kw w, ∀ k₂ ∈ Kw w,
        Disjoint (F k₁) (F k₂)) ∧
      (∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
        Disjoint (F p₁) (F p₂)) ∧
      ∀ w ∈ W, ∀ k ∈ K,
        k ∉ insert c (Kw w) → Disjoint (F (p w)) (F k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw k₁ hk₁ k₂ hk₂
    have h₁ := hwing w hw k₁ hk₁
    have h₂ := hwing w hw k₂ hk₂
    exact hcommonDisjoint k₁ h₁.1 k₂ h₂.1 w hw h₁.2 h₂.2
  · intro p₁ hp₁ p₂ hp₂ hpne
    obtain ⟨w, hw, hwp₁, hwp₂⟩ := hPcommon p₁ hp₁ p₂ hp₂ hpne
    exact hcommonDisjoint p₁ (hPK hp₁) p₂ (hPK hp₂) w hw hwp₁ hwp₂
  · intro w hw k hk hnot
    have hkc : k ≠ c := by
      intro h
      subst k
      exact hnot (by simp)
    have hkwing : k ∉ Kw w := by
      intro h
      exact hnot (by simp [h])
    obtain ⟨v, hv, hvp, hvk⟩ := hpOutsideCommon w hw k hk hkc hkwing
    exact hcommonDisjoint (p w) (hPK (hpP w hw)) k hk v hv hvp hvk

#print axioms KFiber_separator_color_template

end Erdos85
