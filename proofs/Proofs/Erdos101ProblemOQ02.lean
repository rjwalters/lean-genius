/-
# Erdős Problem #101 — Elementary Incidence Bound (toward Szemerédi–Trotter)

Follow-up to Erdős Problem #101 (`Erdos101Problem.lean`), open question OQ-02:
*"Formalize the Szemerédi–Trotter bound `I(P,L) ≤ C(|P|^{2/3}|L|^{2/3} + |P| + |L|)`."*

The full Szemerédi–Trotter theorem requires either the crossing-number inequality
or a cell decomposition, both substantial. This file formalizes the classical
**elementary predecessor** of that theorem — the Cauchy–Schwarz incidence bound —
in fully rigorous, axiom-free form.

## Setup

An *incidence system* is a set of points `P`, a set of lines `L`, and an incidence
relation `Inc`, subject to the defining axiom of a linear space:

  **two distinct points lie on at most one common line.**

Write `r ℓ = |{p ∈ P : Inc p ℓ}|` for the number of points on a line and
`I = ∑_{ℓ∈L} r ℓ` for the total number of incidences.

## Main result

  `incidences_sq_le : I² ≤ |L| · (|P|² + I)`

This is the sharp, sqrt-free integer form of the elementary bound. It immediately
gives (over the reals) `I ≤ |P|·√|L| + |L|` and, symmetrically, `I ≤ |L|·√|P| + |P|`,
the bounds that Szemerédi–Trotter improves to `|P|^{2/3}|L|^{2/3}`.

## Proof

Pure double counting of collinear point-pairs plus Cauchy–Schwarz:

* `sum_choose_two_le` : `∑_ℓ C(r ℓ, 2) ≤ C(|P|, 2)` — each pair of points is
  collinear on at most one line, so the map `(ℓ, {p,q}) ↦ {p,q}` from
  line-incident pairs into all pairs is injective.
* `sq_eq_self_add_two_mul_choose_two` : `n² = n + 2·C(n,2)`, converting the
  pair count into a sum of squares: `∑_ℓ (r ℓ)² = I + 2·∑_ℓ C(r ℓ,2) ≤ I + |P|²`.
* Cauchy–Schwarz: `I² = (∑_ℓ r ℓ)² ≤ |L|·∑_ℓ (r ℓ)² ≤ |L|·(|P|² + I)`.

All results are axiom-free (0 sorries, 0 axioms).

Reference: https://erdosproblems.com/101
-/

import Mathlib

namespace Erdos101OQ02ST

open Finset

/-- The elementary identity `n² = n + 2·C(n,2)` relating a square to a triangular
    number. This is what turns a sum of pair-counts into a sum of squares. -/
lemma sq_eq_self_add_two_mul_choose_two (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hc : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        show k + k.choose 2 = k.choose 2 + k
        omega
      have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      rw [hc, hsq, ih]; ring

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The points of `P` lying on the line `ℓ` under the incidence relation `Inc`. -/
def pointsOn (Inc : α → β → Prop) [DecidableRel Inc] (P : Finset α) (ℓ : β) : Finset α :=
  P.filter (fun p => Inc p ℓ)

lemma pointsOn_subset (Inc : α → β → Prop) [DecidableRel Inc] (P : Finset α) (ℓ : β) :
    pointsOn Inc P ℓ ⊆ P := Finset.filter_subset _ _

/-- Total number of point–line incidences `I(P,L) = ∑_{ℓ∈L} |{p ∈ P : Inc p ℓ}|`. -/
def incidences (Inc : α → β → Prop) [DecidableRel Inc] (P : Finset α) (L : Finset β) : ℕ :=
  ∑ ℓ ∈ L, (pointsOn Inc P ℓ).card

/-- **Double counting of collinear pairs.** In a linear space (two distinct points
    determine at most one common line), the number of point-pairs summed over the
    lines they lie on is bounded by the total number of point-pairs `C(|P|, 2)`. -/
lemma sum_choose_two_le
    (Inc : α → β → Prop) [DecidableRel Inc] (P : Finset α) (L : Finset β)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ ℓ₁ ∈ L, ∀ ℓ₂ ∈ L,
      Inc p ℓ₁ → Inc q ℓ₁ → Inc p ℓ₂ → Inc q ℓ₂ → ℓ₁ = ℓ₂) :
    ∑ ℓ ∈ L, (pointsOn Inc P ℓ).card.choose 2 ≤ P.card.choose 2 := by
  -- The LHS is the cardinality of the Σ-type of 2-element incident subsets.
  have hcard : ∑ ℓ ∈ L, (pointsOn Inc P ℓ).card.choose 2
      = (L.sigma (fun ℓ => (pointsOn Inc P ℓ).powersetCard 2)).card := by
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [Finset.card_powersetCard]
  rw [hcard, show P.card.choose 2 = (P.powersetCard 2).card from
        (Finset.card_powersetCard 2 P).symm]
  -- Project `(ℓ, e) ↦ e`; injectivity is exactly the linear-space axiom.
  apply Finset.card_le_card_of_injOn (fun x => x.2)
  · rintro ⟨ℓ, e⟩ hx
    obtain ⟨_, he⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hsub, hc2⟩ := Finset.mem_powersetCard.mp he
    exact Finset.mem_powersetCard.mpr ⟨hsub.trans (pointsOn_subset Inc P ℓ), hc2⟩
  · rintro ⟨ℓ₁, e₁⟩ hx₁ ⟨ℓ₂, e₂⟩ hx₂ heq
    obtain ⟨hℓ₁, he₁⟩ := Finset.mem_sigma.mp hx₁
    obtain ⟨hℓ₂, he₂⟩ := Finset.mem_sigma.mp hx₂
    obtain ⟨hsub₁, hcard₁⟩ := Finset.mem_powersetCard.mp he₁
    obtain ⟨hsub₂, _⟩ := Finset.mem_powersetCard.mp he₂
    -- `heq : e₁ = e₂` (after beta / `Sigma.snd`)
    have heqe : e₁ = e₂ := heq
    subst heqe
    obtain ⟨a, b, hab, hrfl⟩ := Finset.card_eq_two.mp hcard₁
    subst hrfl
    have ha1 : a ∈ pointsOn Inc P ℓ₁ := hsub₁ (by simp)
    have hb1 : b ∈ pointsOn Inc P ℓ₁ := hsub₁ (by simp)
    have ha2 : a ∈ pointsOn Inc P ℓ₂ := hsub₂ (by simp)
    have hb2 : b ∈ pointsOn Inc P ℓ₂ := hsub₂ (by simp)
    simp only [pointsOn, Finset.mem_filter] at ha1 hb1 ha2 hb2
    have hll : ℓ₁ = ℓ₂ :=
      huniq a ha1.1 b hb1.1 hab ℓ₁ hℓ₁ ℓ₂ hℓ₂ ha1.2 hb1.2 ha2.2 hb2.2
    subst hll; rfl

/-- `∑_ℓ (r ℓ)² = I + 2·∑_ℓ C(r ℓ, 2)`, where `r ℓ = |pointsOn ℓ|` and `I` is the
    incidence count. -/
lemma sum_sq_eq (Inc : α → β → Prop) [DecidableRel Inc] (P : Finset α) (L : Finset β) :
    ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card) ^ 2
      = incidences Inc P L + 2 * ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card).choose 2 := by
  unfold incidences
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ℓ _
  exact sq_eq_self_add_two_mul_choose_two _

/-- Cauchy–Schwarz for natural-number sums: `(∑ f)² ≤ |s| · ∑ f²`.
    Proved over `ℝ` and cast back to `ℕ`. -/
lemma sq_sum_le_card_mul_sum_sq_nat (s : Finset β) (f : β → ℕ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => (f i : ℝ)) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  calc (∑ i ∈ s, (f i : ℝ)) ^ 2
      ≤ (∑ i ∈ s, (f i : ℝ) ^ 2) * s.card := h
    _ = s.card * ∑ i ∈ s, (f i : ℝ) ^ 2 := by ring

/-- **Elementary incidence bound (toward Szemerédi–Trotter).**

In any incidence system in which two distinct points lie on at most one common line,
the number of incidences `I` satisfies

    `I² ≤ |L| · (|P|² + I)`.

Over the reals this yields `I ≤ |P|·√|L| + |L|`. Szemerédi–Trotter improves the
right-hand side to `O(|P|^{2/3}|L|^{2/3} + |P| + |L|)`; this bound is the elementary
Cauchy–Schwarz predecessor, and is sharp for the linear-space axiom alone (it is
attained, e.g., by a projective plane where every pair of points lies on a line). -/
theorem incidences_sq_le
    (Inc : α → β → Prop) [DecidableRel Inc] (P : Finset α) (L : Finset β)
    (huniq : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ ℓ₁ ∈ L, ∀ ℓ₂ ∈ L,
      Inc p ℓ₁ → Inc q ℓ₁ → Inc p ℓ₂ → Inc q ℓ₂ → ℓ₁ = ℓ₂) :
    (incidences Inc P L) ^ 2 ≤ L.card * (P.card ^ 2 + incidences Inc P L) := by
  -- Cauchy–Schwarz: I² ≤ |L| · ∑_ℓ (r ℓ)²
  have hCS : (incidences Inc P L) ^ 2 ≤ L.card * ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq_nat L (fun ℓ => (pointsOn Inc P ℓ).card)
    unfold incidences
    exact h
  -- Sum-of-squares bound: ∑_ℓ (r ℓ)² ≤ |P|² + I
  have hA : ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card) ^ 2 ≤ P.card ^ 2 + incidences Inc P L := by
    rw [sum_sq_eq]
    have hchoose := sum_choose_two_le Inc P L huniq
    have h2 : 2 * P.card.choose 2 ≤ P.card ^ 2 := by
      rw [sq_eq_self_add_two_mul_choose_two P.card]; omega
    have hkey : 2 * ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card).choose 2 ≤ P.card ^ 2 := by
      calc 2 * ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card).choose 2
          ≤ 2 * P.card.choose 2 := by gcongr
        _ ≤ P.card ^ 2 := h2
    omega
  calc (incidences Inc P L) ^ 2
      ≤ L.card * ∑ ℓ ∈ L, ((pointsOn Inc P ℓ).card) ^ 2 := hCS
    _ ≤ L.card * (P.card ^ 2 + incidences Inc P L) := by gcongr

-- Axiom audit: should depend only on the foundational `propext`,
-- `Classical.choice`, `Quot.sound` (fully verified, no extra axioms).
#print axioms incidences_sq_le

end Erdos101OQ02ST
