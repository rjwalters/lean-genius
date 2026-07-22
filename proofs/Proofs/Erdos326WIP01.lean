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
* for an order-2 basis the growth ratio `bₖ/k²` of its increasing enumeration is
  bounded above — eventually by a constant `C`, and its full range is `BddAbove`
  (the `growthRatio` restatement of the `bₖ = O(k²)` bound);
* the growth limit is unique, and existence of a limit contradicts
  `HasNoGrowthLimit`;
* a **two-subsequence criterion** for non-convergence
  (`hasNoGrowthLimit_of_two_subseq_limits`): two strictly-monotone index
  subsequences along which the growth ratio tends to distinct limits force
  `HasNoGrowthLimit` — the reusable engine behind the oscillation direction;
* both growth-limit predicates are non-vacuous: an exactly-quadratic
  enumeration `bₖ = c·k²` has growth limit `c`, while an enumeration whose
  quadratic coefficient oscillates between `1` and `2` has **no** growth limit;
* the growth limit is a **tail invariant** (`hasGrowthLimit_congr'`: agreeing
  eventually ⟹ same growth-limit behaviour), and a **sub-quadratically**
  enumerated sequence `bₖ ≤ C·k` has growth limit `0`
  (`hasGrowthLimit_zero_of_linear_bound`, with the identity enumeration `bₖ = k`
  as concrete order-`1` witness) — so non-convergence requires honestly
  quadratic growth.

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

/-! ## A two-subsequence criterion for non-convergence

The standard route to `HasNoGrowthLimit` is to exhibit two subsequences of the
growth ratio converging to **different** limits: since a convergent sequence has
*every* subsequence converging to the same limit, two distinct subsequential
limits preclude convergence.  This is exactly the mechanism behind the oscillating
toy example below (`growthRatio_oscillating_odd`/`_even` give subsequential limits
`2` and `1`), and it is the reusable tool the open oscillation direction of #326
(building a sub-basis whose ratio does not converge) must ultimately consume. -/

/-- **Two-subsequence criterion for `HasNoGrowthLimit`.**  If the growth ratio
restricted to two subsequences `φ, ψ` (strictly monotone index maps, hence cofinal)
converges to distinct limits `L ≠ L'`, then `b` has no growth limit.  A growth limit
`x` would force *both* subsequences to converge to `x` (a subsequence of a convergent
sequence shares its limit), giving `L = x = L'`. -/
theorem hasNoGrowthLimit_of_two_subseq_limits {b : ℕ → ℕ} {φ ψ : ℕ → ℕ} {L L' : ℝ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hL : Tendsto (fun k => growthRatio b (φ k)) atTop (𝓝 L))
    (hL' : Tendsto (fun k => growthRatio b (ψ k)) atTop (𝓝 L'))
    (hLL' : L ≠ L') : HasNoGrowthLimit b := by
  intro x hx
  have e1 : Tendsto (fun k => growthRatio b (φ k)) atTop (𝓝 x) :=
    hx.comp hφ.tendsto_atTop
  have e2 : Tendsto (fun k => growthRatio b (ψ k)) atTop (𝓝 x) :=
    hx.comp hψ.tendsto_atTop
  exact hLL' ((tendsto_nhds_unique e1 hL).symm.trans (tendsto_nhds_unique e2 hL'))

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

/-! ## Order-2 bases are quadratically dense (Key Observation 1)

The parent file records as *Key Observation 1* that any order-`2` additive basis
must have density at least `√n` — there are `≥ c√n` elements up to `n`, hence the
`k`-th element is `≤ Ck²`.  This is the elementary counting fact underlying the
whole growth question of Erdős #326.  We formalize it here.

The mechanism: every `m ∈ [N, n]` is a sum of at most two elements of `A`, each
`≤ m ≤ n`.  Pad each representation to an ordered pair `(aₘ, bₘ)` with
`aₘ + bₘ = m` and `aₘ, bₘ ∈ A ∪ {0}`.  Because the sum recovers `m`, the map
`m ↦ (aₘ, bₘ)` is injective on `[N,n]`, so `[N,n]` injects into `(S ∪ {0})²`
where `S ⊆ A ∩ [0,n]` collects the nonzero coordinates.  Hence
`|[N,n]| ≤ (|S| + 1)²`, i.e. `|S| ≥ √(n+1−N) − 1`.  Axiom-free.  The deep
oscillation dichotomy (the open part of #326) is untouched. -/

/-- **An order-2 additive basis is quadratically dense.**  If `A` is an additive
basis of order `2`, there is a threshold `N` such that for every `n ≥ N` some
finite `S ⊆ A` of elements `≤ n` satisfies `|Icc N n| ≤ (|S| + 1)²`.  This is the
counting bound behind the standard `bₖ = O(k²)` growth estimate (Key Observation
1 of `Erdos326Problem`). -/
theorem IsAddBasisOfOrder.two_quadratic_density {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset ℕ, ↑S ⊆ A ∧ (∀ s ∈ S, s ≤ n) ∧
        (Finset.Icc N n).card ≤ (S.card + 1) ^ 2 := by
  classical
  obtain ⟨N, hN⟩ := h
  -- For each `m ≥ N`, choose an ordered `0`-padded summand pair from `A ∪ {0}`.
  have hpair : ∀ m : ℕ, N ≤ m → ∃ a b : ℕ,
      a + b = m ∧ (a ∈ A ∨ a = 0) ∧ (b ∈ A ∨ b = 0) ∧ a ≤ m ∧ b ≤ m := by
    intro m hm
    obtain ⟨k, hk, f, hf, hsum⟩ := hN m hm
    interval_cases k
    · simp only [Fin.sum_univ_zero] at hsum
      exact ⟨0, 0, by omega, Or.inr rfl, Or.inr rfl, by omega, by omega⟩
    · simp only [Fin.sum_univ_one] at hsum
      exact ⟨f 0, 0, by omega, Or.inl (hf 0), Or.inr rfl, by omega, by omega⟩
    · rw [Fin.sum_univ_two] at hsum
      exact ⟨f 0, f 1, hsum, Or.inl (hf 0), Or.inl (hf 1), by omega, by omega⟩
  choose! a b hsum hmemA hmemB hlea hleb using hpair
  refine ⟨N, fun n hn => ?_⟩
  set imgs : Finset ℕ :=
    (Finset.Icc N n).image a ∪ (Finset.Icc N n).image b with himgs
  set T : Finset ℕ := insert 0 imgs with hTdef
  have h0T : (0 : ℕ) ∈ T := Finset.mem_insert_self 0 imgs
  refine ⟨T.erase 0, ?_, ?_, ?_⟩
  · -- `S ⊆ A`
    intro s hs
    rw [Finset.mem_coe, Finset.mem_erase, hTdef, Finset.mem_insert, himgs,
      Finset.mem_union] at hs
    obtain ⟨hs0, hmem⟩ := hs
    rcases hmem with h0 | hmem
    · exact absurd h0 hs0
    rcases hmem with hima | himb
    · obtain ⟨m, hmIcc, rfl⟩ := Finset.mem_image.mp hima
      rw [Finset.mem_Icc] at hmIcc
      rcases hmemA m hmIcc.1 with h | h
      · exact h
      · exact absurd h hs0
    · obtain ⟨m, hmIcc, rfl⟩ := Finset.mem_image.mp himb
      rw [Finset.mem_Icc] at hmIcc
      rcases hmemB m hmIcc.1 with h | h
      · exact h
      · exact absurd h hs0
  · -- every element of `S` is `≤ n`
    intro s hs
    rw [Finset.mem_erase, hTdef, Finset.mem_insert, himgs, Finset.mem_union] at hs
    obtain ⟨_, hmem⟩ := hs
    rcases hmem with h0 | hmem
    · omega
    rcases hmem with hima | himb
    · obtain ⟨m, hmIcc, rfl⟩ := Finset.mem_image.mp hima
      rw [Finset.mem_Icc] at hmIcc
      exact (hlea m hmIcc.1).trans hmIcc.2
    · obtain ⟨m, hmIcc, rfl⟩ := Finset.mem_image.mp himb
      rw [Finset.mem_Icc] at hmIcc
      exact (hleb m hmIcc.1).trans hmIcc.2
  · -- the cardinality bound
    have hTcard : (T.erase 0).card + 1 = T.card := Finset.card_erase_add_one h0T
    have hle : (Finset.Icc N n).card ≤ (T ×ˢ T).card := by
      apply Finset.card_le_card_of_injOn (fun m => (a m, b m))
      · intro m hm
        rw [Finset.mem_coe, Finset.mem_Icc] at hm
        rw [Finset.mem_coe, Finset.mem_product]
        refine ⟨Finset.mem_insert_of_mem ?_, Finset.mem_insert_of_mem ?_⟩
        · exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr hm, rfl⟩)
        · exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr hm, rfl⟩)
      · intro m1 hm1 m2 hm2 hEq
        rw [Finset.mem_coe, Finset.mem_Icc] at hm1 hm2
        simp only [Prod.mk.injEq] at hEq
        have e1 := hsum m1 hm1.1
        have e2 := hsum m2 hm2.1
        omega
    calc (Finset.Icc N n).card
        ≤ (T ×ˢ T).card := hle
      _ = T.card * T.card := Finset.card_product T T
      _ = ((T.erase 0).card + 1) * ((T.erase 0).card + 1) := by rw [hTcard]
      _ = ((T.erase 0).card + 1) ^ 2 := by ring

/-- Counting-function form: for an order-2 basis there is a threshold `N` such
that for every `n ≥ N` the witnessing finite subset `S ⊆ A` of elements `≤ n`
satisfies `n + 1 − N ≤ (|S| + 1)²`.  Equivalently the number of basis elements
used up to `n` is `≥ √(n+1−N) − 1`, the `√n` density behind `bₖ = O(k²)`. -/
theorem IsAddBasisOfOrder.two_quadratic_density' {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ S : Finset ℕ, ↑S ⊆ A ∧ (∀ s ∈ S, s ≤ n) ∧
        n + 1 - N ≤ (S.card + 1) ^ 2 := by
  obtain ⟨N, hN⟩ := h.two_quadratic_density
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨S, hS, hSn, hcard⟩ := hN n hn
  rw [Nat.card_Icc] at hcard
  exact ⟨S, hS, hSn, hcard⟩

/-! ## The `bₖ = O(k²)` growth upper bound for order-2 bases

The `√n` density bound above turns into an *upper* bound on the enumeration
`bₖ = Nat.nth (· ∈ A) k` (the `k`-th smallest element of `A`, in increasing
order): a threshold `N` such that `bₖ ≤ N + (k+1)²` for every `k`, hence
`bₖ ≤ (N+4)·k²` for `k ≥ 1`.  This is the standard `bₖ = O(k²)` estimate that
Key Observation 1 exists to prove.

Mechanism: with `n := N + (k+1)²` the density bound `n+1−N ≤ (|S|+1)²` reads
`(k+1)²+1 ≤ (|S|+1)²`, forcing `k < |S|`; since `S ⊆ A` and every element of `S`
is `≤ n`, we get `k < |S| ≤ Nat.count (· ∈ A) (n+1)`, so
`Nat.nth (· ∈ A) k < n+1` by `Nat.nth_lt_of_lt_count`.  Axiom-free; no deep
input — the open oscillation dichotomy of #326 is untouched. -/

/-- **The `bₖ = O(k²)` upper bound.**  Enumerating an order-2 additive basis `A`
in increasing order via `Nat.nth (· ∈ A)`, the `k`-th element is at most
`N + (k+1)²` for the density threshold `N`. -/
theorem IsAddBasisOfOrder.two_nth_le_quadratic {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    ∃ N : ℕ, ∀ k : ℕ, Nat.nth (· ∈ A) k ≤ N + (k + 1) ^ 2 := by
  classical
  obtain ⟨N, hN⟩ := h.two_quadratic_density'
  refine ⟨N, fun k => ?_⟩
  set n : ℕ := N + (k + 1) ^ 2 with hn
  obtain ⟨S, hS, hSn, hcard⟩ := hN n (by omega)
  -- `(k+1)²+1 ≤ (|S|+1)²` forces `k < |S|`.
  have hcard' : (k + 1) ^ 2 + 1 ≤ (S.card + 1) ^ 2 := by
    have he : n + 1 - N = (k + 1) ^ 2 + 1 := by omega
    rwa [he] at hcard
  have hkS : k < S.card := by
    by_contra hc
    rw [not_lt] at hc
    have : (S.card + 1) ^ 2 ≤ (k + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  -- `S ⊆ {i < n+1 : i ∈ A}`, so `|S| ≤ count (· ∈ A) (n+1)`.
  have hsub : S ⊆ (Finset.range (n + 1)).filter (· ∈ A) := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := hSn s hs; omega, hS (Finset.mem_coe.mpr hs)⟩
  have hcount : k < Nat.count (· ∈ A) (n + 1) := by
    rw [Nat.count_eq_card_filter_range]
    exact lt_of_lt_of_le hkS (Finset.card_le_card hsub)
  have hlt := Nat.nth_lt_of_lt_count hcount
  omega

/-- The `k`-th element of an order-2 basis is `≤ C·k²` for `k ≥ 1`
(`bₖ = O(k²)`, the standard growth estimate of Key Observation 1). -/
theorem IsAddBasisOfOrder.two_nth_le_mul_sq {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    ∃ C N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k → Nat.nth (· ∈ A) k ≤ C * k ^ 2 := by
  obtain ⟨N, hN⟩ := h.two_nth_le_quadratic
  refine ⟨N + 4, 1, fun k hk => ?_⟩
  have e1 : (k + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith [hk]
  have e2 : N ≤ N * k ^ 2 := by nlinarith [hk]
  calc Nat.nth (· ∈ A) k
      ≤ N + (k + 1) ^ 2 := hN k
    _ ≤ N * k ^ 2 + 4 * k ^ 2 := by omega
    _ = (N + 4) * k ^ 2 := by ring

/-! ## The `bₖ = O(k²)` bound as `growthRatio` boundedness

The `two_nth_le_*` lemmas above bound the enumeration `bₖ = Nat.nth (· ∈ A) k`
of an order-2 basis by `C·k²`.  We translate that into the language of the
`growthRatio b k = bₖ/k²` object itself (until now only exercised on toy
sequences): the growth ratio of the actual basis enumeration is **bounded
above**.  This is the precise sense in which Key Observation 1 controls `bₖ`
from above — it does **not** touch non-convergence, the open part of #326. -/

/-- **The growth ratio of an order-2 basis is eventually bounded above.**  For an
order-2 additive basis `A`, enumerated increasingly by `bₖ = Nat.nth (· ∈ A) k`,
there are constants `C, N₀` with `bₖ/k² ≤ C` for all `k ≥ N₀`.  This is the
`growthRatio` restatement of `two_nth_le_mul_sq` (`bₖ ≤ C·k²`). -/
theorem IsAddBasisOfOrder.two_growthRatio_le {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    ∃ C N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k → growthRatio (Nat.nth (· ∈ A)) k ≤ (C : ℝ) := by
  obtain ⟨C, N₀, hC⟩ := h.two_nth_le_mul_sq
  refine ⟨C, max N₀ 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hkR : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    positivity
  have hb : (Nat.nth (· ∈ A) k : ℝ) ≤ (C : ℝ) * (k : ℝ) ^ 2 := by
    exact_mod_cast hC k (le_trans (le_max_left _ _) hk)
  unfold growthRatio
  rw [div_le_iff₀ hkR]
  exact hb

/-- The growth ratio of an order-2 basis eventually lies in `[0, C]`: it is
nonnegative (`growthRatio_nonneg`) and bounded above by `C`
(`two_growthRatio_le`). -/
theorem IsAddBasisOfOrder.two_growthRatio_mem_Icc {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    ∃ C N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      growthRatio (Nat.nth (· ∈ A)) k ∈ Set.Icc (0 : ℝ) (C : ℝ) := by
  obtain ⟨C, N₀, hC⟩ := h.two_growthRatio_le
  exact ⟨C, N₀, fun k hk => ⟨growthRatio_nonneg _ k, hC k hk⟩⟩

/-- **The full range of the growth ratio of an order-2 basis is bounded above.**
Removing the eventual-threshold from `two_growthRatio_le`: the finitely many
values on the initial segment `k < N₀` are absorbed into the (nonnegative) bound
`C + ∑_{j < N₀} growthRatio b j`, so `{bₖ/k² : k ∈ ℕ}` is `BddAbove`.  This is
`bₖ = O(k²)` expressed as literal boundedness of the ratio sequence. -/
theorem IsAddBasisOfOrder.two_growthRatio_bddAbove {A : Set ℕ}
    (h : IsAddBasisOfOrder A 2) :
    BddAbove (Set.range (growthRatio (Nat.nth (· ∈ A)))) := by
  obtain ⟨C, N₀, hC⟩ := h.two_growthRatio_le
  set b := Nat.nth (· ∈ A) with hbdef
  set S : ℝ := ∑ j ∈ Finset.range N₀, growthRatio b j with hSdef
  refine ⟨(C : ℝ) + S, ?_⟩
  rintro _ ⟨k, rfl⟩
  rcases Nat.lt_or_ge k N₀ with hk | hk
  · have hmem : k ∈ Finset.range N₀ := Finset.mem_range.mpr hk
    have hle : growthRatio b k ≤ S :=
      Finset.single_le_sum (fun j _ => growthRatio_nonneg b j) hmem
    have hCnonneg : (0 : ℝ) ≤ (C : ℝ) := by positivity
    linarith
  · have hCk : growthRatio b k ≤ (C : ℝ) := hC k hk
    have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun j _ => growthRatio_nonneg b j
    linarith

/-! ## The growth-limit predicates are non-vacuous (realizability)

The lemmas above about `HasGrowthLimit`/`HasNoGrowthLimit` (uniqueness of the
limit, and that having a limit excludes `HasNoGrowthLimit`) say nothing about
whether *either* predicate is ever satisfiable.  Here we exhibit explicit
enumerations realizing each side, so the predicates are not vacuous:

* an exactly-quadratic enumeration `bₖ = c·k²` has growth limit `c`
  (`hasGrowthLimit_quadratic`);
* an enumeration whose quadratic coefficient oscillates between `1` and `2`
  has **no** growth limit (`hasNoGrowthLimit_oscillating`).

The oscillating example is exactly the `bₖ/k²`-non-convergence phenomenon that
Erdős #326 conjectures must be attainable on a *sub-basis* of every order-2
basis; here it is realized by a bare sequence (with no basis constraint), which
is elementary.  All results remain `0`-axiom / `0`-sorry. -/

/-- The growth ratio of an exactly-quadratic enumeration `bₖ = c·k²` at any
`k ≠ 0` equals the coefficient `c`. -/
theorem growthRatio_eq (b : ℕ → ℕ) (c k : ℕ) (hk : k ≠ 0)
    (hval : b k = c * k ^ 2) : growthRatio b k = (c : ℝ) := by
  unfold growthRatio
  rw [hval]
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  rw [div_eq_iff (pow_ne_zero 2 hkR)]
  push_cast
  ring

/-- **A quadratic enumeration has a growth limit.**  If `bₖ = c·k²` exactly then
`bₖ/k² → c`, so `HasGrowthLimit` is non-vacuous (for every coefficient `c`, in
particular the positive ones, matching the flavour of Cassels' `aₖ/k² → x`
construction — though here `b` is a bare sequence, not a genuine basis). -/
theorem hasGrowthLimit_quadratic (c : ℕ) :
    HasGrowthLimit (fun k => c * k ^ 2) (c : ℝ) := by
  have hev : (fun k => growthRatio (fun k => c * k ^ 2) k) =ᶠ[atTop] fun _ => (c : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact growthRatio_eq _ c k (by omega) rfl
  exact tendsto_const_nhds.congr' hev.symm

/-- An explicit enumeration whose quadratic coefficient alternates: `bₖ = k²` for
even `k` and `bₖ = 2k²` for odd `k`.  Its growth ratio therefore oscillates
between `1` and `2`. -/
def oscillating (k : ℕ) : ℕ := (k % 2 + 1) * k ^ 2

/-- On odd indices the oscillating growth ratio is `2`. -/
theorem growthRatio_oscillating_odd (m : ℕ) :
    growthRatio oscillating (2 * m + 1) = 2 := by
  have hval : oscillating (2 * m + 1) = 2 * (2 * m + 1) ^ 2 := by
    unfold oscillating; rw [show (2 * m + 1) % 2 = 1 from by omega]
  have h := growthRatio_eq oscillating 2 (2 * m + 1) (by omega) hval
  simpa using h

/-- On even indices the oscillating growth ratio is `1`. -/
theorem growthRatio_oscillating_even (m : ℕ) :
    growthRatio oscillating (2 * m + 2) = 1 := by
  have hval : oscillating (2 * m + 2) = 1 * (2 * m + 2) ^ 2 := by
    unfold oscillating; rw [show (2 * m + 2) % 2 = 0 from by omega]
  have h := growthRatio_eq oscillating 1 (2 * m + 2) (by omega) hval
  simpa using h

/-- **`HasNoGrowthLimit` is non-vacuous.**  The oscillating enumeration has no
growth limit: its ratio equals `2` on the (unboundedly many) odd indices and `1`
on the even ones, so any candidate limit would have to be both `2` and `1`.  This
realizes the `bₖ/k²`-non-convergence phenomenon central to Erdős #326 (here for a
plain sequence, with the deep sub-basis existence question untouched). -/
theorem hasNoGrowthLimit_oscillating : HasNoGrowthLimit oscillating := by
  intro x hx
  -- the odd and even index maps both tend to `atTop`
  have godd : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have geven : Tendsto (fun m : ℕ => 2 * m + 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  -- along odd indices the ratio is the constant `2`, so `x = 2`
  have hodd : Tendsto (fun m : ℕ => growthRatio oscillating (2 * m + 1)) atTop (𝓝 x) :=
    hx.comp godd
  have hodd2 : Tendsto (fun m : ℕ => growthRatio oscillating (2 * m + 1)) atTop (𝓝 2) := by
    simp only [growthRatio_oscillating_odd]; exact tendsto_const_nhds
  have hx2 : x = 2 := tendsto_nhds_unique hodd hodd2
  -- along even indices the ratio is the constant `1`, so `x = 1`
  have heven : Tendsto (fun m : ℕ => growthRatio oscillating (2 * m + 2)) atTop (𝓝 x) :=
    hx.comp geven
  have heven1 : Tendsto (fun m : ℕ => growthRatio oscillating (2 * m + 2)) atTop (𝓝 1) := by
    simp only [growthRatio_oscillating_even]; exact tendsto_const_nhds
  have hx1 : x = 1 := tendsto_nhds_unique heven heven1
  rw [hx2] at hx1
  norm_num at hx1

/-! ## The growth limit is a tail invariant; sub-quadratic growth ⟹ limit `0`

Two structural facts complementing the convergent (`hasGrowthLimit_quadratic`)
and non-convergent (`hasNoGrowthLimit_oscillating`) examples above:

* the growth limit depends only on the **tail** of the enumeration — two
  sequences that agree eventually have the same growth-limit behaviour
  (`hasGrowthLimit_congr'`).  This is exactly what makes modifying a basis on a
  finite prefix irrelevant to its `bₖ/k²` limit, a prerequisite for any
  sub-basis argument;
* a **sub-quadratically** enumerated sequence converges — to `0`.  If `bₖ ≤ C·k`
  (linear growth, as for an order-`1` basis such as `ℕ` itself) then
  `bₖ/k² ≤ C/k → 0`, so `HasGrowthLimit b 0` (`hasGrowthLimit_zero_of_linear_bound`),
  realized concretely by the identity enumeration `bₖ = k`
  (`hasGrowthLimit_id_zero`).  So genuine non-convergence à la Erdős #326 can only
  arise from honestly quadratic growth — the ratio cannot oscillate while the
  numerator stays `o(k²)`.

All results remain `0`-axiom / `0`-sorry. -/

/-- **The growth limit is a tail invariant.**  If two enumerations agree
eventually (`b =ᶠ[atTop] b'`) then their growth ratios agree eventually, so one
has growth limit `x` iff the other does.  In particular modifying an enumeration
on finitely many indices leaves every growth-limit statement unchanged. -/
theorem hasGrowthLimit_congr' {b b' : ℕ → ℕ} {x : ℝ} (h : b =ᶠ[atTop] b') :
    HasGrowthLimit b x ↔ HasGrowthLimit b' x := by
  have hg : growthRatio b =ᶠ[atTop] growthRatio b' := by
    filter_upwards [h] with k hk
    simp only [growthRatio, hk]
  unfold HasGrowthLimit
  exact ⟨fun H => H.congr' hg, fun H => H.congr' hg.symm⟩

/-- **A sub-quadratically enumerated sequence has growth limit `0`.**  If
`bₖ ≤ C·k` for all `k` (linear growth), then `bₖ/k² ≤ C/k → 0`, and since the
ratio is nonnegative the squeeze gives `HasGrowthLimit b 0`.  This is the
convergent-to-`0` counterpart of `hasGrowthLimit_quadratic`: a numerator that is
`O(k)` cannot make the ratio oscillate or diverge. -/
theorem hasGrowthLimit_zero_of_linear_bound (b : ℕ → ℕ) (C : ℕ)
    (h : ∀ k, b k ≤ C * k) : HasGrowthLimit b 0 := by
  have hle : ∀ k, growthRatio b k ≤ (C : ℝ) / k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [growthRatio_zero]
    · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
      have hbk : (b k : ℝ) ≤ (C : ℝ) * k := by exact_mod_cast h k
      rw [growthRatio]
      calc (b k : ℝ) / (k : ℝ) ^ 2 ≤ (C : ℝ) * k / (k : ℝ) ^ 2 := by gcongr
        _ = (C : ℝ) / k := by rw [pow_two, mul_div_mul_right _ _ hkne]
  refine squeeze_zero (growthRatio_nonneg b) hle ?_
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **Concrete convergent order-`1` enumeration.**  The identity enumeration
`bₖ = k` — the increasing enumeration of `ℕ` itself, an order-`1` additive basis
(`isAddBasisOfOrder_univ_one`) — has growth ratio `k/k² = 1/k → 0`, hence growth
limit `0`.  Contrast `hasGrowthLimit_quadratic` (limit `c`) and
`hasNoGrowthLimit_oscillating` (no limit): sparser (linear) bases sit at the
`0` end of the growth spectrum. -/
theorem hasGrowthLimit_id_zero : HasGrowthLimit (fun k => k) 0 :=
  hasGrowthLimit_zero_of_linear_bound _ 1 (fun k => by simp)

end Erdos326
