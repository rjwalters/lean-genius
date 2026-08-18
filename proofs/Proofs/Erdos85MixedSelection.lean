import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prime selection for the mixed parity terminal

The mixed parity terminal consumes a prime `p ≥ 7` such that every
`p`-divisible defect component is odd and the number of `p`-divisible
components is odd.  Such a prime need not exist for an arbitrary length
family — `{7, 7, 3}` has its only large prime dividing an even number of
members — so the selection layer is a dichotomy: either a usable prime
exists, or the family satisfies the explicit `SelectionObstructed`
predicate, whose consequences (every large prime divides an even-length
member or an even number of members) are recorded here for the residual
analysis.  Discharging the obstructed case requires the quotient
constraints of the boundary graph, not bare arithmetic.
-/

namespace Erdos85

variable {C : Type*} [Fintype C]

/-- No prime `p ≥ 7` is usable for the parity terminal: each such prime
divides some even-length member, or divides an even number of members. -/
def SelectionObstructed (ℓ : C → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → 7 ≤ p →
    (∃ c, p ∣ ℓ c ∧ Even (ℓ c)) ∨
      Even (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card

/-- **The selection dichotomy.**  Either some prime `p ≥ 7` satisfies
both hypotheses of the mixed parity terminal, or the length family is
selection-obstructed. -/
theorem exists_selection_or_obstructed (ℓ : C → ℕ) :
    (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧
      (∀ c, p ∣ ℓ c → Odd (ℓ c)) ∧
      Odd (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card) ∨
      SelectionObstructed ℓ := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧
      (∀ c, p ∣ ℓ c → Odd (ℓ c)) ∧
      Odd (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card
  · exact Or.inl h
  · right
    intro p hp hp7
    by_cases hodd : ∀ c, p ∣ ℓ c → Odd (ℓ c)
    · right
      have hcount : ¬ Odd
          (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card := by
        intro hcount
        exact h ⟨p, hp, hp7, hodd, hcount⟩
      rwa [Nat.not_odd_iff_even] at hcount
    · left
      push_neg at hodd
      obtain ⟨c, hdvd, heven⟩ := hodd
      exact ⟨c, hdvd, Nat.not_odd_iff_even.mp heven⟩

/-- With every length odd, obstruction says exactly: every prime `p ≥ 7`
divides an even number of members. -/
theorem obstructed_even_counts_of_all_odd {ℓ : C → ℕ}
    (hAllOdd : ∀ c, Odd (ℓ c)) (hobs : SelectionObstructed ℓ)
    (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    Even (Finset.univ.filter fun c : C ↦ p ∣ ℓ c).card := by
  rcases hobs p hp hp7 with ⟨c, _, heven⟩ | hcount
  · exact absurd heven (Nat.not_even_iff_odd.mpr (hAllOdd c))
  · exact hcount

/-- A family whose members have no prime factor `≥ 7` is vacuously
obstructed: the filter is empty for every large prime. -/
theorem selectionObstructed_of_smooth {ℓ : C → ℕ}
    (hsmooth : ∀ c, ∀ q : ℕ, q.Prime → q ∣ ℓ c → q < 7) :
    SelectionObstructed ℓ := by
  intro p hp hp7
  right
  have hempty : (Finset.univ.filter fun c : C ↦ p ∣ ℓ c) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro c _ hdvd
    exact absurd (hsmooth c p hp hdvd) (by omega)
  rw [hempty]
  simp

/-- Conversely, an obstructed all-odd family with some member divisible
by a large prime `q` must contain a *second* member divisible by `q`. -/
theorem exists_second_member_of_obstructed {ℓ : C → ℕ}
    (hAllOdd : ∀ c, Odd (ℓ c)) (hobs : SelectionObstructed ℓ)
    {q : ℕ} (hq : q.Prime) (hq7 : 7 ≤ q)
    {c₀ : C} (hc₀ : q ∣ ℓ c₀) :
    ∃ c₁ : C, c₁ ≠ c₀ ∧ q ∣ ℓ c₁ := by
  have heven := obstructed_even_counts_of_all_odd hAllOdd hobs q hq hq7
  have hmem : c₀ ∈ Finset.univ.filter fun c : C ↦ q ∣ ℓ c := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ c₀, hc₀⟩
  have hpos : 0 < (Finset.univ.filter fun c : C ↦ q ∣ ℓ c).card :=
    Finset.card_pos.mpr ⟨c₀, hmem⟩
  have h2 : 2 ≤ (Finset.univ.filter fun c : C ↦ q ∣ ℓ c).card := by
    rcases heven with ⟨k, hk⟩
    omega
  obtain ⟨c₁, hc₁mem, hc₁ne⟩ :=
    Finset.exists_mem_ne (s := Finset.univ.filter fun c : C ↦ q ∣ ℓ c) (by omega) c₀
  rw [Finset.mem_filter] at hc₁mem
  exact ⟨c₁, hc₁ne, hc₁mem.2⟩

end Erdos85
