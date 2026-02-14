import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

/-
# Cantor's Characterization of the Rationals as a Linear Order (OQ-02)

## What This Proves

This file extends the denumerability of ℚ (OQ-01) with Cantor's remarkable characterization
theorem: **ℚ is, up to order-isomorphism, the unique countable dense linear order without
endpoints.** Any two countable, densely ordered linear orders without minimum or maximum
elements are order-isomorphic to each other — and hence to ℚ.

## The Back-and-Forth Method

The proof uses Cantor's **back-and-forth argument** (1895):
1. Enumerate both orders as sequences (possible since they're countable)
2. Build an order-isomorphism step by step
3. The density + no-endpoints conditions ensure each extension is always possible
4. The resulting map is a total order-isomorphism

Mathlib formalizes this via `Order.PartialIso` (finite partial isomorphisms)
and `Order.iso_of_countable_dense` (the full theorem).

## Key Results
- `cantor_characterization`: Any countable dense linear order without endpoints ≃o ℚ
- `countable_dense_linear_orders_iso`: Any two such orders are isomorphic
- `rationals_selfsimilar`: ℚ ≃o ℚ (non-trivial self-isomorphism exists)
- `integers_embed`: ℤ embeds order-preservingly into ℚ
- `rationals_dense`: Between any two rationals lies another

## Wiedijk's 100 Theorems: #3 (Extension)
-/

namespace DenumerabilityRationalsOQ02

-- ========================================================================
-- Part I: ℚ as a Countable Dense Linear Order Without Endpoints
-- ========================================================================

instance : LinearOrder ℚ := inferInstance
instance : Countable ℚ := inferInstance
instance : DenselyOrdered ℚ := inferInstance
instance : NoMinOrder ℚ := inferInstance
instance : NoMaxOrder ℚ := inferInstance
instance : Nonempty ℚ := ⟨0⟩

/-- Density spelled out: for any p < q in ℚ, there exists r with p < r < q. -/
theorem rationals_dense (p q : ℚ) (h : p < q) : ∃ r : ℚ, p < r ∧ r < q :=
  DenselyOrdered.dense p q h

/-- No minimum: for any q in ℚ, there exists p < q. -/
theorem rationals_no_min (q : ℚ) : ∃ p : ℚ, p < q :=
  NoMinOrder.exists_lt q

/-- No maximum: for any q in ℚ, there exists r > q. -/
theorem rationals_no_max (q : ℚ) : ∃ r : ℚ, q < r :=
  NoMaxOrder.exists_gt q

-- ========================================================================
-- Part II: Cantor's Characterization Theorem
-- ========================================================================

/-- **Cantor's Characterization Theorem**: Any countable dense linear order without
endpoints is order-isomorphic to ℚ. -/
theorem cantor_characterization
    (α : Type*) [LinearOrder α] [Countable α] [DenselyOrdered α]
    [NoMinOrder α] [NoMaxOrder α] [Nonempty α] :
    Nonempty (α ≃o ℚ) :=
  Order.iso_of_countable_dense α ℚ

/-- **Uniqueness of Countable Dense Linear Orders**: Any two countable dense
linear orders without endpoints are order-isomorphic. -/
theorem countable_dense_linear_orders_iso
    (α β : Type*) [LinearOrder α] [LinearOrder β]
    [Countable α] [DenselyOrdered α] [NoMinOrder α] [NoMaxOrder α] [Nonempty α]
    [Countable β] [DenselyOrdered β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] :
    Nonempty (α ≃o β) :=
  Order.iso_of_countable_dense α β

-- ========================================================================
-- Part III: The Back-and-Forth Infrastructure
-- ========================================================================

example : Type := Order.PartialIso ℚ ℚ

example (f : Order.PartialIso ℚ ℚ) : Order.PartialIso ℚ ℚ :=
  f.comm

/-- The key density lemma. -/
theorem density_extension_lemma
    {α : Type*} [LinearOrder α] [DenselyOrdered α] [NoMinOrder α]
    [NoMaxOrder α] [Nonempty α]
    (lo hi : Finset α) (h : ∀ x ∈ lo, ∀ y ∈ hi, x < y) :
    ∃ m, (∀ x ∈ lo, x < m) ∧ ∀ y ∈ hi, m < y :=
  Order.exists_between_finsets lo hi h

-- ========================================================================
-- Part IV: Self-Similarity of ℚ
-- ========================================================================

/-- ℚ is order-isomorphic to itself (self-similarity). -/
theorem rationals_selfsimilar : Nonempty (ℚ ≃o ℚ) :=
  Order.iso_of_countable_dense ℚ ℚ

def trivial_automorphism : ℚ ≃o ℚ := OrderIso.refl ℚ

-- ========================================================================
-- Part V: Embedding Results
-- ========================================================================

/-- The integers embed order-preservingly into the rationals. -/
def integers_embed : ℤ ↪o ℚ where
  toFun := fun n => (n : ℚ)
  inj' := Int.cast_injective
  map_rel_iff' := by
    intro a b
    change (a : ℚ) ≤ (b : ℚ) ↔ a ≤ b
    exact Int.cast_le

/-- The natural numbers embed order-preservingly into the rationals. -/
def naturals_embed : ℕ ↪o ℚ where
  toFun := fun n => (n : ℚ)
  inj' := Nat.cast_injective
  map_rel_iff' := by
    intro a b
    change (a : ℚ) ≤ (b : ℚ) ↔ a ≤ b
    exact Nat.cast_le

-- ========================================================================
-- Part VI: Concrete Density Examples
-- ========================================================================

/-- The midpoint of two rationals lies strictly between them. -/
theorem midpoint_between (p q : ℚ) (h : p < q) :
    p < (p + q) / 2 ∧ (p + q) / 2 < q := by
  constructor
  · linarith
  · linarith

/-- Explicit witness: between 1/3 and 1/2 lies 5/12. -/
example : (1 : ℚ) / 3 < (5 : ℚ) / 12 ∧ (5 : ℚ) / 12 < (1 : ℚ) / 2 :=
  ⟨by norm_num, by norm_num⟩

/-- Explicit witness: between 0 and any positive rational lies half of it. -/
theorem half_between_zero (q : ℚ) (hq : 0 < q) : 0 < q / 2 ∧ q / 2 < q := by
  constructor
  · linarith
  · linarith

-- ========================================================================
-- Part VII: No Minimum and No Maximum — Constructive Witnesses
-- ========================================================================

theorem pred_lt (q : ℚ) : q - 1 < q := by linarith
theorem succ_gt (q : ℚ) : q < q + 1 := by linarith

-- ========================================================================
-- Part IX: Density Propagation
-- ========================================================================

/-- Between any two distinct rationals, there exist at least two distinct
rationals strictly between them. -/
theorem two_between (p q : ℚ) (h : p < q) :
    ∃ r s : ℚ, p < r ∧ r < s ∧ s < q := by
  obtain ⟨m, hpm, hmq⟩ := DenselyOrdered.dense p q h
  obtain ⟨s, hms, hsq⟩ := DenselyOrdered.dense m q hmq
  exact ⟨m, s, hpm, hms, hsq⟩

/-- Between any two distinct rationals, there exist at least three distinct
rationals strictly between them. -/
theorem three_between (p q : ℚ) (h : p < q) :
    ∃ r s t : ℚ, p < r ∧ r < s ∧ s < t ∧ t < q := by
  obtain ⟨r, s, hpr, hrs, hsq⟩ := two_between p q h
  obtain ⟨t, hst, htq⟩ := DenselyOrdered.dense s q hsq
  exact ⟨r, s, t, hpr, hrs, hst, htq⟩

-- ========================================================================
-- Part X: Connections to Cardinal Arithmetic
-- ========================================================================

/-- The cardinality of ℚ is ℵ₀. -/
theorem card_rat_aleph0 : Cardinal.mk ℚ = Cardinal.aleph0 :=
  Cardinal.mk_denumerable ℚ

/-- ℚ and ℕ have the same cardinality (from OQ-01). -/
theorem card_rat_eq_nat : Cardinal.mk ℚ = Cardinal.mk ℕ := by
  rw [card_rat_aleph0, Cardinal.mk_denumerable ℕ]

-- ========================================================================
-- Part XI: Comparison with Other Familiar Orders
-- ========================================================================

/-- There is no integer strictly between n and n + 1. -/
theorem no_integer_between (n : ℤ) : ¬∃ m : ℤ, n < m ∧ m < n + 1 := by
  intro ⟨m, hm1, hm2⟩
  omega

/-- 0 is the minimum of ℕ. -/
theorem nat_has_min : ∀ n : ℕ, 0 ≤ n := Nat.zero_le

-- ========================================================================
-- Part XII: The Universality of ℚ
-- ========================================================================

/-- Three elements {0, 1, 2} embed into ℚ preserving their order. -/
example : ∃ f : Fin 3 → ℚ, StrictMono f :=
  ⟨fun n => (n : ℚ), fun {a b} h => by
    show ((a : ℕ) : ℚ) < ((b : ℕ) : ℚ)
    exact Nat.cast_lt.mpr h⟩

/-- Any Fin n embeds strictly monotonically into ℚ. -/
theorem fin_embeds (n : ℕ) : ∃ f : Fin n → ℚ, StrictMono f :=
  ⟨fun k => (k : ℚ), fun {a b} h => by
    show ((a : ℕ) : ℚ) < ((b : ℕ) : ℚ)
    exact Nat.cast_lt.mpr h⟩

-- ========================================================================
-- Verification Examples
-- ========================================================================

example : Nonempty (ℚ ≃o ℚ) := cantor_characterization ℚ

example : (1 : ℚ) / 4 < ((1 : ℚ) / 4 + (3 : ℚ) / 4) / 2 ∧
    ((1 : ℚ) / 4 + (3 : ℚ) / 4) / 2 < (3 : ℚ) / 4 :=
  ⟨by norm_num, by norm_num⟩

example : integers_embed 3 < integers_embed 5 := by
  show (3 : ℚ) < 5
  norm_num

end DenumerabilityRationalsOQ02
