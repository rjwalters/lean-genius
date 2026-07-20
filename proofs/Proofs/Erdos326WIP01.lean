/-
# Erdős Problem #326 (Additive Bases and Non-Convergent Subsequences) — Foundational Lemmas

Axiom-free foundational scaffolding for the objects defined in
`Proofs/Erdos326Problem.lean`:

    IsAddBasis A          = ∃ N, ∀ n ≥ N, n is a sum of finitely many elements of A,
    IsAddBasisOfOrder A k = the same with at most k summands,
    growthRatio b k       = bₖ / k²,
    HasGrowthLimit b x     / HasNoGrowthLimit b.

Erdős #326 asks whether every order-2 additive basis `A` contains a sub-basis
`B ⊆ A` whose growth ratio `bₖ/k²` fails to converge — it is **open**
(Cassels 1957 disproved the `A = B` variant).  The deep growth/oscillation
content is untouched; this file records the elementary order-theory and
monotonicity of the basis predicates and the basic behaviour of the growth
ratio and its limit:

* order monotonicity `IsAddBasisOfOrder A k → k ≤ k' → IsAddBasisOfOrder A k'`
  and set monotonicity under `⊆`, for both `IsAddBasisOfOrder` and `IsAddBasis`;
* `Set.univ` is an order-1 basis; the empty set and order 0 are never bases;
* the perfect squares are a concrete additive basis of **order 4** (Lagrange's
  four-square theorem) — the canonical non-vacuous witness for the predicate;
* `growthRatio` is nonnegative, `growthRatio b 0 = 0`;
* the growth limit is unique, and existence of a limit contradicts
  `HasNoGrowthLimit`.

All results are `0`-axiom / `0`-sorry.

Reference: <https://erdosproblems.com/326>
-/

import Mathlib
import Proofs.Erdos326Problem

open Filter Set
open scoped Topology

namespace Erdos326

/-! ## Monotonicity of the basis predicates -/

/-- An order-`k` basis is an order-`k'` basis for any larger `k'`. -/
theorem IsAddBasisOfOrder.mono_order {A : Set ℕ} {k k' : ℕ}
    (h : IsAddBasisOfOrder A k) (hkk' : k ≤ k') : IsAddBasisOfOrder A k' := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨m, hm, f, hf, hsum⟩ := hN n hn
  exact ⟨m, hm.trans hkk', f, hf, hsum⟩

/-- An order-`k` basis of `A` is an order-`k` basis of any superset `B ⊇ A`. -/
theorem IsAddBasisOfOrder.mono_set {A B : Set ℕ} {k : ℕ}
    (h : IsAddBasisOfOrder A k) (hAB : A ⊆ B) : IsAddBasisOfOrder B k := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨m, hm, f, hf, hsum⟩ := hN n hn
  exact ⟨m, hm, f, fun i => hAB (hf i), hsum⟩

/-- A basis of `A` is a basis of any superset `B ⊇ A`. -/
theorem IsAddBasis.mono {A B : Set ℕ} (h : IsAddBasis A) (hAB : A ⊆ B) :
    IsAddBasis B := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, f, hf, hsum⟩ := hN n hn
  exact ⟨k, f, fun i => hAB (hf i), hsum⟩

/-! ## Extremal cases -/

/-- `ℕ` itself (the universal set) is an additive basis of order `1`:
    each `n` is the single summand `n`. -/
theorem isAddBasisOfOrder_univ_one : IsAddBasisOfOrder (Set.univ : Set ℕ) 1 := by
  refine ⟨0, fun n _ => ⟨1, le_refl 1, fun _ => n, fun _ => Set.mem_univ _, ?_⟩⟩
  simp

/-- `ℕ` itself is an additive basis. -/
theorem isAddBasis_univ : IsAddBasis (Set.univ : Set ℕ) :=
  isAddBasisOfOrder_univ_one.isAddBasis

/-- The empty set is not an additive basis: no large `n` is a sum of elements
    of `∅`. -/
theorem not_isAddBasis_empty : ¬ IsAddBasis (∅ : Set ℕ) := by
  rintro ⟨N, hN⟩
  obtain ⟨k, f, hf, hsum⟩ := hN (N + 1) (by omega)
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Fin.sum_univ_zero] at hsum
    omega
  · exact (Set.mem_empty_iff_false _).mp (hf ⟨0, hk⟩)

/-- No set is an additive basis of order `0`: with at most `0` summands only
    `0` is representable, but arbitrarily large `n` are required. -/
theorem not_isAddBasisOfOrder_zero (A : Set ℕ) : ¬ IsAddBasisOfOrder A 0 := by
  rintro ⟨N, hN⟩
  obtain ⟨m, hm, f, _, hsum⟩ := hN (N + 1) (by omega)
  have hm0 : m = 0 := Nat.le_zero.mp hm
  subst hm0
  simp only [Fin.sum_univ_zero] at hsum
  omega

/-! ## A concrete basis: the perfect squares (Lagrange) -/

/-- The set of perfect squares `{0, 1, 4, 9, …}`. -/
def Squares : Set ℕ := { n : ℕ | ∃ m : ℕ, n = m ^ 2 }

/-- **The perfect squares form an additive basis of order `4`.**  This is
Lagrange's four-square theorem (`Nat.sum_four_squares`): *every* natural number
is a sum of at most four squares.  It is the canonical concrete witness that the
`IsAddBasisOfOrder` predicate is non-vacuous, and the running example behind
Erdős #326 (whose growth question concerns order-`2` bases). -/
theorem isAddBasisOfOrder_squares_four : IsAddBasisOfOrder Squares 4 := by
  refine ⟨0, fun n _ => ?_⟩
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
  refine ⟨4, le_refl 4, ![a ^ 2, b ^ 2, c ^ 2, d ^ 2], ?_, ?_⟩
  · intro i; fin_cases i <;> exact ⟨_, rfl⟩
  · rw [Fin.sum_univ_four]; simpa using habcd

/-- The perfect squares form an additive basis (of some finite order). -/
theorem isAddBasis_squares : IsAddBasis Squares :=
  isAddBasisOfOrder_squares_four.isAddBasis

/-! ## The growth ratio and its limit -/

/-- The growth ratio `bₖ/k²` is nonnegative. -/
theorem growthRatio_nonneg (b : ℕ → ℕ) (k : ℕ) : 0 ≤ growthRatio b k :=
  div_nonneg (Nat.cast_nonneg _) (by positivity)

/-- At `k = 0` the growth ratio is `0` (division by `0² = 0`). -/
theorem growthRatio_zero (b : ℕ → ℕ) : growthRatio b 0 = 0 := by
  unfold growthRatio; simp

/-- The growth limit, when it exists, is unique. -/
theorem HasGrowthLimit.unique {b : ℕ → ℕ} {x y : ℝ}
    (hx : HasGrowthLimit b x) (hy : HasGrowthLimit b y) : x = y :=
  tendsto_nhds_unique hx hy

/-- If the growth ratio has a limit, it does not have "no growth limit". -/
theorem HasGrowthLimit.not_hasNoGrowthLimit {b : ℕ → ℕ} {x : ℝ}
    (h : HasGrowthLimit b x) : ¬ HasNoGrowthLimit b :=
  fun hno => hno x h

/-- `HasNoGrowthLimit` is exactly the non-existence of any growth limit. -/
theorem hasNoGrowthLimit_iff (b : ℕ → ℕ) :
    HasNoGrowthLimit b ↔ ¬ ∃ x, HasGrowthLimit b x := by
  unfold HasNoGrowthLimit
  rw [not_exists]

/-! ## Bounded-order bases are infinite -/

/-- **A basis of bounded order is infinite.**  Unlike `IsAddBasis` (which allows
arbitrarily many summands — so e.g. the singleton `{1}` qualifies, representing
`n` as `1 + ⋯ + 1`), a basis of a *fixed* order `k` must be infinite: a finite
set `A` is bounded by some `M`, so every sum of at most `k` of its elements is
`≤ k · M`, and finitely many such values cannot cover all sufficiently large `n`. -/
theorem IsAddBasisOfOrder.infinite {A : Set ℕ} {k : ℕ}
    (h : IsAddBasisOfOrder A k) : A.Infinite := by
  by_contra hfin
  rw [Set.not_infinite] at hfin
  obtain ⟨N, hN⟩ := h
  obtain ⟨M, hM⟩ := hfin.bddAbove
  -- the target `n` is chosen `≥ N` and strictly above the reachable ceiling `k · M`
  obtain ⟨m, hmk, f, hf, hsum⟩ := hN (max N (k * M + 1)) (le_max_left _ _)
  have hbound : ∑ i, f i ≤ k * M :=
    calc ∑ i, f i ≤ ∑ _i : Fin m, M := Finset.sum_le_sum (fun i _ => hM (hf i))
      _ = m * M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ k * M := by gcongr
  rw [hsum] at hbound
  have hge : k * M + 1 ≤ max N (k * M + 1) := le_max_right _ _
  omega

/-! ## The squares are a basis of order 4 but NOT of order 3 (mod-8 obstruction)

Lagrange's four-square theorem makes the squares an order-`4` basis
(`isAddBasisOfOrder_squares_four`).  Order `3` does **not** suffice: infinitely
many integers — those `≡ 7 (mod 8)` — are not sums of three squares.  This is the
*easy* (necessary) direction of Legendre's three-square theorem, needing only the
finite fact that squares are `0, 1, 4 (mod 8)` and no three of those sum to `7`
modulo `8` (a `decide` over `ZMod 8`); the full Legendre theorem is not required.
Consequently the four-square order is sharp. -/

/-- Every perfect square is `0`, `1`, or `4` modulo `8`. -/
theorem mem_squares_mod_eight {s : ℕ} (hs : s ∈ Squares) :
    (s : ZMod 8) = 0 ∨ (s : ZMod 8) = 1 ∨ (s : ZMod 8) = 4 := by
  obtain ⟨r, rfl⟩ := hs
  have hx : ∀ x : ZMod 8, x ^ 2 = 0 ∨ x ^ 2 = 1 ∨ x ^ 2 = 4 := by decide
  have hcast : ((r ^ 2 : ℕ) : ZMod 8) = (r : ZMod 8) ^ 2 := by push_cast; ring
  rw [hcast]; exact hx _

/-- **The perfect squares are not an additive basis of order `3`.**  If they were,
every sufficiently large `n` — in particular `n = 8N + 7` — would be a sum of at
most three squares.  But modulo `8` each square is `0, 1` or `4`, and no sum of at
most three of these equals `7 (mod 8)`, while `8N + 7 ≡ 7 (mod 8)`.  Contradiction.
Together with `isAddBasisOfOrder_squares_four` this shows the order of the squares
as an additive basis is exactly `4`. -/
theorem not_isAddBasisOfOrder_squares_three : ¬ IsAddBasisOfOrder Squares 3 := by
  rintro ⟨N, hN⟩
  obtain ⟨m, hm, f, hf, hsum⟩ := hN (8 * N + 7) (by omega)
  -- reduce the representation modulo 8
  have hcast : (∑ i, (f i : ZMod 8)) = 7 := by
    have h : ((∑ i, f i : ℕ) : ZMod 8) = 7 := by
      rw [hsum]; push_cast; rw [show (8 : ZMod 8) = 0 from by decide]; ring
    rwa [Nat.cast_sum] at h
  have hmod : ∀ i, (f i : ZMod 8) = 0 ∨ (f i : ZMod 8) = 1 ∨ (f i : ZMod 8) = 4 :=
    fun i => mem_squares_mod_eight (hf i)
  interval_cases m
  · rw [Fin.sum_univ_zero] at hcast; exact absurd hcast (by decide)
  · rw [Fin.sum_univ_one] at hcast
    rcases hmod 0 with h | h | h <;> rw [h] at hcast <;> revert hcast <;> decide
  · rw [Fin.sum_univ_two] at hcast
    rcases hmod 0 with h0 | h0 | h0 <;> rcases hmod 1 with h1 | h1 | h1 <;>
      rw [h0, h1] at hcast <;> revert hcast <;> decide
  · rw [Fin.sum_univ_three] at hcast
    rcases hmod 0 with h0 | h0 | h0 <;> rcases hmod 1 with h1 | h1 | h1 <;>
      rcases hmod 2 with h2 | h2 | h2 <;> rw [h0, h1, h2] at hcast <;> revert hcast <;> decide

/-- **The additive-basis order of the perfect squares is exactly `4`:** they form a
basis of order `4` (Lagrange) but of no smaller order (the `≡ 7 (mod 8)` obstruction
rules out order `3`, and `mono_order` propagates non-representability downward). -/
theorem not_isAddBasisOfOrder_squares_of_le_three {k : ℕ} (hk : k ≤ 3) :
    ¬ IsAddBasisOfOrder Squares k :=
  fun h => not_isAddBasisOfOrder_squares_three (h.mono_order hk)

end Erdos326
