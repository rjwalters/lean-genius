/-
  Property B via the First Moment Method (Erdős 1963)

  A hypergraph has *Property B* (is 2-colorable) if its vertices can be
  colored with two colors so that no edge is monochromatic.

  Erdős (1963): every k-uniform hypergraph with fewer than 2^(k-1) edges
  has Property B. The proof is the cleanest application of the first moment
  method: color each vertex independently and uniformly at random; the
  expected number of monochromatic edges is m · 2^(1-k) < 1 when
  m < 2^(k-1), so some coloring leaves no edge monochromatic.

  This file gives the genuine combinatorial argument over the *finite*
  sample space of all 2-colorings `V → Bool`. The crux is an exact count:
  the number of colorings monochromatic on a fixed k-set is 2 · 2^(n-k).

  Status: 0 sorries, 0 axioms. No `native_decide`.

  Contrast with the gallery's `ProbMethodApplications.property_b_lower`,
  which only asserts `2^(k-1) > 0` (a placeholder). Here we prove the
  actual existence of a proper 2-coloring.
-/
import Mathlib

namespace ProbMethod.PropertyB

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A coloring `c : V → Bool` is **monochromatic** on an edge `e` if all of
    `e`'s vertices receive the same color. -/
def Mono (e : Finset V) (c : V → Bool) : Prop := ∃ b : Bool, ∀ x ∈ e, c x = b

instance (e : Finset V) (c : V → Bool) : Decidable (Mono e c) := by
  unfold Mono; infer_instance

-- ═══════════════════════════════════════════════════
-- Part 0: First moment principle (self-contained)
-- ═══════════════════════════════════════════════════

/-- **First moment principle (existence of a zero).**
    If a nonnegative integer statistic sums to less than the number of
    outcomes, some outcome takes the value `0`. The probabilistic-method
    workhorse: if the expected number of "bad events" is `< 1`, a perfect
    outcome exists. -/
theorem exists_zero_of_sum_lt_card {α : Type*} {s : Finset α} {f : α → ℕ}
    (hlt : (∑ a ∈ s, f a) < s.card) : ∃ a ∈ s, f a = 0 := by
  by_contra h
  push_neg at h
  have h1 : ∀ a ∈ s, 1 ≤ f a := fun a ha => Nat.one_le_iff_ne_zero.mpr (h a ha)
  have hge : s.card ≤ ∑ a ∈ s, f a := by
    calc s.card = ∑ _a ∈ s, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ a ∈ s, f a := Finset.sum_le_sum h1
  omega

-- ═══════════════════════════════════════════════════
-- Part I: The counting crux
-- ═══════════════════════════════════════════════════

/-- **Counting colorings with a prescribed constant value on an edge.**
    The number of colorings `c : V → Bool` taking the fixed value `b` on
    every vertex of `e` is `2 ^ (n - |e|)`: the colors off `e` are free. -/
theorem card_const_on (e : Finset V) (b : Bool) :
    (univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = b)).card
      = 2 ^ (Fintype.card V - e.card) := by
  -- The filtered set is exactly a `piFinset`: value pinned to `{b}` on `e`,
  -- free (`univ`) off `e`.
  have hset :
      (univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = b))
        = Fintype.piFinset (fun x => if x ∈ e then ({b} : Finset Bool) else univ) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      by_cases hx : x ∈ e
      · simp [hx, h x hx]
      · simp [hx]
    · intro h x hx
      have hcx := h x
      simp [hx] at hcx
      exact hcx
  rw [hset, Fintype.card_piFinset]
  -- each factor: `#(if x∈e then {b} else univ) = 2 ^ (if x∈e then 0 else 1)`
  have hfac : ∀ x : V,
      ((if x ∈ e then ({b} : Finset Bool) else univ).card)
        = 2 ^ (if x ∈ e then 0 else 1) := by
    intro x; by_cases hx : x ∈ e <;> simp [hx]
  rw [Finset.prod_congr rfl (fun x _ => hfac x), Finset.prod_pow_eq_pow_sum]
  -- reduce to the exponent sum
  congr 1
  -- ∑ x, (if x ∈ e then 0 else 1) = n - |e|
  have hflip : (∑ x : V, (if x ∈ e then (0:ℕ) else 1))
      = ∑ x : V, (if x ∉ e then (1:ℕ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _; by_cases hx : x ∈ e <;> simp [hx]
  rw [hflip, ← Finset.card_filter, Finset.filter_not, Finset.card_univ_diff,
      Finset.filter_univ_mem]

-- ═══════════════════════════════════════════════════
-- Part II: Counting monochromatic colorings of an edge
-- ═══════════════════════════════════════════════════

/-- **Exact count of colorings monochromatic on a (nonempty) edge.**
    There are `2 · 2^(n-|e|)` such colorings: choose the common color (2
    ways) and the colors off `e` freely (`2^(n-|e|)` ways). -/
theorem card_mono (e : Finset V) (he : e.Nonempty) :
    (univ.filter (fun c : V → Bool => Mono e c)).card
      = 2 * 2 ^ (Fintype.card V - e.card) := by
  -- split monochromatic = (all-true on e) ⊔ (all-false on e)
  have hsplit : univ.filter (fun c : V → Bool => Mono e c)
      = univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = true)
        ∪ univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = false) := by
    ext c
    simp only [mem_union, mem_filter, mem_univ, true_and, Mono]
    constructor
    · rintro ⟨b, hb⟩; cases b
      · right; exact hb
      · left; exact hb
    · rintro (h | h)
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
  have hdisj :
      Disjoint (univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = true))
               (univ.filter (fun c : V → Bool => ∀ x ∈ e, c x = false)) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    obtain ⟨x, hx⟩ := he
    have ht := h1 x hx
    have hf := h2 x hx
    rw [ht] at hf
    exact Bool.noConfusion hf
  rw [hsplit, Finset.card_union_of_disjoint hdisj, card_const_on, card_const_on]
  ring

-- ═══════════════════════════════════════════════════
-- Part III: Erdős' Property B theorem
-- ═══════════════════════════════════════════════════

/-- **Erdős 1963: small uniform hypergraphs are 2-colorable.**
    A `k`-uniform hypergraph (edge family `E`, every edge of size `k ≥ 1`)
    with fewer than `2^(k-1)` edges has Property B: there is a 2-coloring
    `c : V → Bool` under which no edge is monochromatic.

    Proof: over the `2^n` uniform 2-colorings the total number of
    (coloring, monochromatic edge) incidences is `|E| · 2 · 2^(n-k)`. When
    `|E| < 2^(k-1)` this is `< 2^n`, so by the first moment principle some
    coloring has zero monochromatic edges. -/
theorem property_b_two_colorable
    (E : Finset (Finset V)) (k : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ E, e.card = k)
    (hsmall : E.card < 2 ^ (k - 1)) :
    ∃ c : V → Bool, ∀ e ∈ E, ¬ Mono e c := by
  rcases E.eq_empty_or_nonempty with hE | hE
  · exact ⟨fun _ => true, by simp [hE]⟩
  -- k ≤ n, from any edge ⊆ univ
  obtain ⟨e₀, he₀⟩ := hE
  have hkn : k ≤ Fintype.card V := by
    have hle : e₀.card ≤ Fintype.card V := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ e₀)
    rw [huniform e₀ he₀] at hle; exact hle
  -- first-moment sum: ∑_c (#mono edges) = |E| · 2 · 2^(n-k)
  have hsum :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        = E.card * (2 * 2 ^ (Fintype.card V - k)) := by
    have hinner : ∀ e ∈ E,
        (∑ c : V → Bool, ite (Mono e c) 1 0) = 2 * 2 ^ (Fintype.card V - k) := by
      intro e he
      rw [← Finset.card_filter]
      have hne : e.Nonempty := Finset.card_pos.mp (by rw [huniform e he]; omega)
      rw [card_mono e hne, huniform e he]
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm, Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  -- |Ω| = 2^n
  have hcard : (univ : Finset (V → Bool)).card = 2 ^ Fintype.card V := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  -- the strict inequality sum < |Ω|
  have h2nk : 0 < (2 : ℕ) ^ (Fintype.card V - k) := pow_pos (by norm_num) _
  have hlt :
      (∑ c : V → Bool, (E.filter (fun e => Mono e c)).card)
        < (univ : Finset (V → Bool)).card := by
    rw [hsum, hcard]
    have e1 : (2 : ℕ) ^ Fintype.card V = 2 ^ k * 2 ^ (Fintype.card V - k) := by
      rw [← pow_add]; congr 1; omega
    have ekey : E.card * 2 < 2 ^ k := by
      have e2 : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = 1 + (k - 1) by omega]
        rw [pow_add, pow_one]
      rw [e2]; omega
    calc E.card * (2 * 2 ^ (Fintype.card V - k))
          = (E.card * 2) * 2 ^ (Fintype.card V - k) := by ring
      _ < 2 ^ k * 2 ^ (Fintype.card V - k) := by
          exact (Nat.mul_lt_mul_right h2nk).mpr ekey
      _ = 2 ^ Fintype.card V := e1.symm
  -- first moment principle: some coloring has zero monochromatic edges
  obtain ⟨c, -, hc⟩ := exists_zero_of_sum_lt_card hlt
  refine ⟨c, ?_⟩
  have hempty : E.filter (fun e => Mono e c) = ∅ := Finset.card_eq_zero.mp hc
  intro e he
  exact (Finset.filter_eq_empty_iff.mp hempty) he

end ProbMethod.PropertyB
