/-
# Erdős Problem #117 — Covering Groups by Abelian Subgroups

Let h(n) be the minimum number of Abelian subgroups needed to cover
any group G with the property that every subset of size > n contains
some x ≠ y with xy = yx.

Estimate h(n).

## Known Results
- Pyber (1987): c₁^n < h(n) < c₂^n for constants c₂ > c₁ > 1
- Lower bound previously known to Isaacs

Status: OPEN
Reference: https://erdosproblems.com/117
-/

import Mathlib
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- A group has the n-commuting property if every subset of size > n
    contains two distinct commuting elements. -/
def HasNCommutingProperty (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ S : Finset G, S.card > n →
    ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ x * y = y * x

/-- A subgroup H of G is Abelian. -/
def IsAbelianSubgroup (G : Type*) [Group G] (H : Subgroup G) : Prop :=
  ∀ x y : G, x ∈ H → y ∈ H → x * y = y * x

/-- h(n) is the minimum k such that every group with the n-commuting
    property can be covered by k Abelian subgroups. -/
noncomputable def abelianCoverNumber (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type*) [Group G] [Fintype G],
    HasNCommutingProperty G n →
    ∃ H : Fin k → Subgroup G,
      (∀ i, IsAbelianSubgroup G (H i)) ∧
      ∀ g : G, ∃ i, g ∈ H i}

/- ## Main Problem -/

/-  **Erdős Problem #117**: estimate h(n). Known: exponential in n. -/
/- ## Known Results -/

/-  **Pyber (1987)**: h(n) is exponential. There exist c₂ > c₁ > 1 with
    c₁^n < h(n) < c₂^n. The gap between c₁ and c₂ is open. -/
/-  **Isaacs Lower Bound**: the exponential lower bound c₁^n was known
    to Isaacs before Pyber's work. -/
/- ## Observations -/

/- **Trivial Case n = 1**: every pair of elements commutes, so G is Abelian.
    Then h(1) = 1. -/
/- **Connection to Ramsey Theory**: the n-commuting property is a Ramsey-type
    condition on the group. The covering number h(n) measures how far the group
    is from being globally Abelian. -/

/- **Open**: determine the exact base of the exponential growth. Is there
    a single constant c > 1 with h(n) = Θ(c^n)? -/

/- ## Foundational lemmas (axiom-free)

Elementary structural facts developing the def-only stub: monotonicity of the
`n`-commuting property, the characterisation of the `n = 1` case as
commutativity, and closure properties of the abelian-subgroup predicate. -/

/-- The `n`-commuting property is monotone in `n`: a larger threshold is a
weaker hypothesis (fewer subsets qualify), so it follows from a smaller one. -/
theorem hasNCommutingProperty_mono {G : Type*} [Group G] {n m : ℕ} (hnm : n ≤ m)
    (h : HasNCommutingProperty G n) : HasNCommutingProperty G m :=
  fun S hS => h S (lt_of_le_of_lt hnm hS)

/-- Every commutative group has the `1`-commuting property: any subset of size
`> 1` contains two distinct (hence commuting) elements. -/
theorem commGroup_hasNCommutingProperty_one {G : Type*} [CommGroup G] :
    HasNCommutingProperty G 1 := by
  intro S hS
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hS
  exact ⟨x, y, hx, hy, hxy, mul_comm x y⟩

/-- **The `n = 1` case is exactly commutativity.** If `G` has the `1`-commuting
property then any two elements commute: taking the two-element subset `{x, y}`
of size `2 > 1`, its only distinct pair must commute. -/
theorem commute_of_hasNCommutingProperty_one {G : Type*} [Group G]
    (h : HasNCommutingProperty G 1) (x y : G) : x * y = y * x := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  obtain ⟨a, b, ha, hb, hab, hcomm⟩ :=
    h {x, y} (by rw [Finset.card_pair hxy]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact hcomm
  · exact hcomm.symm
  · exact absurd rfl hab

/-- The trivial subgroup is abelian. -/
theorem isAbelianSubgroup_bot {G : Type*} [Group G] :
    IsAbelianSubgroup G (⊥ : Subgroup G) := by
  intro x y hx hy
  rw [Subgroup.mem_bot] at hx hy
  subst hx; subst hy; simp

/-- In a commutative group the whole group is an abelian subgroup. -/
theorem isAbelianSubgroup_top_of_commGroup {G : Type*} [CommGroup G] :
    IsAbelianSubgroup G (⊤ : Subgroup G) :=
  fun x y _ _ => mul_comm x y

/-- The abelian-subgroup predicate is downward closed: a subgroup of an abelian
subgroup is abelian. -/
theorem isAbelianSubgroup_mono {G : Type*} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (hK : IsAbelianSubgroup G K) : IsAbelianSubgroup G H :=
  fun x y hx hy => hK x y (hHK hx) (hHK hy)

/-- `IsAbelianSubgroup` agrees with Mathlib's `IsMulCommutative` on the
subgroup (the coerced subtype). -/
theorem isAbelianSubgroup_iff_isMulCommutative {G : Type*} [Group G]
    (H : Subgroup G) : IsAbelianSubgroup G H ↔ IsMulCommutative H := by
  constructor
  · intro h
    exact isMulCommutative_iff.mpr (fun a b => Subtype.ext (h a b a.2 b.2))
  · intro h x y hx hy
    haveI := h
    exact setLike_mul_comm hx hy
