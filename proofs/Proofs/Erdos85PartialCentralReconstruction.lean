/- Elementary algebraic reconstruction; no Mathlib or axioms are imported. -/
universe u
namespace Erdos85PartialCentral
variable {V : Type u}

def HasOutput (R : V → V → V → Prop) (x z : V) : Prop := ∃ y, R x y z

structure Laws (R : V → V → V → Prop) : Prop where
  functional : ∀ {x y z w}, R x y z → R x y w → z = w
  commutative : ∀ {x y z}, R x y z → R y x z
  noDiagonal : ∀ {x z}, ¬ R x x z
  avoidLeft : ∀ {x y z}, R x y z → z ≠ x
  central : ∀ {a b c v w}, R a b v → R b c w → v ≠ w → R v w b
  rich : ∀ x z, HasOutput R x z → ∃ w, w ≠ z ∧ HasOutput R x w

theorem output_symmetric {R : V → V → V → Prop} (h : Laws R)
    {x z : V} (hx : HasOutput R x z) : HasOutput R z x := by
  cases hx with
  | intro y hy =>
    cases h.rich x z ⟨y, hy⟩ with
    | intro w hw =>
      cases hw with
      | intro hne hw =>
        cases hw with
        | intro t ht =>
          exact ⟨w, h.central (h.commutative hy) ht (Ne.symm hne)⟩

theorem output_irreflexive {R : V → V → V → Prop} (h : Laws R)
    (x : V) : ¬ HasOutput R x x := by
  intro hx
  cases hx with
  | intro y hy => exact h.avoidLeft hy rfl

theorem relation_iff_common_output {R : V → V → V → Prop} (h : Laws R)
    {x y z : V} (hne : x ≠ y) :
    R x y z ↔ HasOutput R x z ∧ HasOutput R y z := by
  constructor
  · intro hr
    exact ⟨⟨y, hr⟩, ⟨x, h.commutative hr⟩⟩
  · intro hc
    cases output_symmetric h hc.1 with
    | intro a ha =>
      cases output_symmetric h hc.2 with
      | intro b hb =>
        exact h.central (h.commutative ha) hb hne

theorem common_output_unique {R : V → V → V → Prop} (h : Laws R)
    {x y z w : V} (hne : x ≠ y)
    (hz : HasOutput R x z ∧ HasOutput R y z)
    (hw : HasOutput R x w ∧ HasOutput R y w) : z = w := by
  exact h.functional ((relation_iff_common_output h hne).mpr hz)
    ((relation_iff_common_output h hne).mpr hw)

/- The converse starts with a symmetric, irreflexive relation A having at
most one common neighbor for distinct inputs. -/
def Common (A : V → V → Prop) (x y z : V) : Prop :=
  x ≠ y ∧ A x z ∧ A y z

theorem reconstructed_relation {R : V → V → V → Prop} (h : Laws R)
    {x y z : V} : R x y z ↔ Common (HasOutput R) x y z := by
  constructor
  · intro hr
    have hne : x ≠ y := by
      intro heq
      cases heq
      exact h.noDiagonal hr
    exact ⟨hne, (relation_iff_common_output h hne).mp hr⟩
  · intro hc
    exact (relation_iff_common_output h hc.1).mpr hc.2

theorem common_central {A : V → V → Prop}
    (hs : ∀ {x y}, A x y → A y x)
    {a b c v w : V} (hv : Common A a b v) (hw : Common A b c w)
    (hne : v ≠ w) : Common A v w b := by
  exact ⟨hne, hs hv.2.2, hs hw.2.1⟩

theorem common_has_output_iff {A : V → V → Prop}
    (hs : ∀ {x y}, A x y → A y x)
    (htwo : ∀ x z, A x z → ∃ y, y ≠ x ∧ A z y)
    {x z : V} : HasOutput (Common A) x z ↔ A x z := by
  constructor
  · intro h
    cases h with
    | intro y hy => exact hy.2.1
  · intro h
    cases htwo x z h with
    | intro y hy => exact ⟨y, Ne.symm hy.1, h, hs hy.2⟩

theorem common_laws {A : V → V → Prop}
    (hs : ∀ {x y}, A x y → A y x)
    (hi : ∀ x, ¬ A x x)
    (hu : ∀ {x y z w}, x ≠ y → A x z → A y z → A x w → A y w → z = w)
    (htwo : ∀ x z, A x z → ∃ y, y ≠ x ∧ A z y)
    (hrich : ∀ x z, A x z → ∃ w, w ≠ z ∧ A x w) : Laws (Common A) where
  functional := by
    intro x y z w hz hw
    exact hu hz.1 hz.2.1 hz.2.2 hw.2.1 hw.2.2
  commutative := by
    intro x y z h
    exact ⟨Ne.symm h.1, h.2.2, h.2.1⟩
  noDiagonal := by
    intro x z h
    exact h.1 rfl
  avoidLeft := by
    intro x y z h heq
    exact hi x (heq ▸ h.2.1)
  central := common_central hs
  rich := by
    intro x z h
    have hxz := (common_has_output_iff hs htwo).mp h
    cases hrich x z hxz with
    | intro w hw =>
      exact ⟨w, hw.1, (common_has_output_iff hs htwo).mpr hw.2⟩

/- Exact total central groupoids have no commuting pair of distinct inputs. -/
theorem central_anticommutative (op : V → V → V)
    (hc : ∀ a b c, op (op a b) (op b c) = b)
    {a b : V} (hcomm : op a b = op b a) : a = b := by
  have h1 := hc a b a
  have h2 := hc b a b
  rw [hcomm] at h1 h2
  exact h2.symm.trans h1

#print axioms output_symmetric
#print axioms output_irreflexive
#print axioms relation_iff_common_output
#print axioms reconstructed_relation
#print axioms common_output_unique
#print axioms common_laws
#print axioms central_anticommutative
end Erdos85PartialCentral
