import Mathlib

/-
# Erdős–Ko–Rado, OQ-01: the cyclic-interval lemma, de-axiomatized

The parent gallery entry `ErdosKoRado` formalizes the Erdős–Ko–Rado theorem via
Katona's cyclic-permutation argument. Its combinatorial heart — the statement that
in any cyclic order of `n ≥ 2k` points, **at most `k` of the `n` cyclic intervals
(arcs) of length `k` can be pairwise intersecting** — was left as an `axiom`:

    axiom at_most_k_intersecting_cyclic_intervals (n k : ℕ) (hn : n ≥ 2 * k) (hk : 0 < k) :
      ∀ (I : Finset ℕ), (∀ i ∈ I, i < n) →
        (∀ i j, i ∈ I → j ∈ I → (cyclicInterval n k i ∩ cyclicInterval n k j).Nonempty) →
        I.card ≤ k

The sibling open question OQ-02 explicitly records that this lemma was "released
unsolved" because "its modular bookkeeping resisted a Lean formalization", and
side-stepped it by re-proving EKR through Mathlib's Kruskal–Katona shadow
inequality. This file answers OQ-01 directly: it **proves that exact statement as
a theorem, with zero axioms and no `native_decide`**, so the parent's axiom can be
discharged.

## The proof

The arc starting at position `i` is `A_i = {i, i+1, …, i+k-1} mod n`. The argument
is Katona's classic collapse-pairing:

* Fix any arc `A_{i₀}` in the family. Every other arc `A_j` in the family intersects
  it, which forces the circular offset `r(j) := (j - i₀) mod n` to lie in
  `{0,…,k-1} ∪ {n-k+1,…,n-1}` (lemma `offset_range`).
* Define `g(j) = r(j)` on the lower block and `g(j) = r(j) - (n-k)` on the upper
  block, collapsing each pair `{s, s+(n-k)}` to one value in `{0,…,k-1}`.
* `g` is injective on the family: a lower value `s` and an upper value `s+(n-k)`
  index two arcs whose starts differ by **exactly** `k`, hence (as `n ≥ 2k`) those
  arcs are disjoint — impossible in a pairwise-intersecting family
  (lemma `not_intersect_mixed`). Within a single block, `g` is injective because the
  offset map is (lemma `offset_inj`).
* Therefore the family injects into `range k`, so it has at most `k` members.

The definitions `cyclicInterval` is reproduced verbatim from the parent (which is
`axiomatized`, so we avoid importing it). Self-contained: imports only Mathlib.
-/

namespace ErdosKoRadoOQ01

open Finset

/-- A cyclic interval starting at position `i` with length `k` in a cyclic order of
`n` elements: the positions `{i, i+1, …, i+k-1} mod n`. (Verbatim from the parent
`ErdosKoRado.lean`.) -/
def cyclicInterval (n k i : ℕ) : Finset (Fin n) :=
  if h : 0 < n then
    (Finset.range k).image (fun j => ⟨(i + j) % n, Nat.mod_lt _ h⟩)
  else ∅

/-- Membership in a cyclic interval: `x` lies in `A_i` iff `x ≡ i + a (mod n)` for
some offset `a < k`. -/
lemma mem_cyclicInterval {n k i : ℕ} (hn : 0 < n) (x : Fin n) :
    x ∈ cyclicInterval n k i ↔ ∃ a < k, (i + a) % n = (x : ℕ) := by
  unfold cyclicInterval
  rw [dif_pos hn, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, Finset.mem_range.mp ha, ?_⟩
    have := congrArg Fin.val hax
    simpa using this
  · rintro ⟨a, ha, hax⟩
    refine ⟨a, Finset.mem_range.mpr ha, ?_⟩
    apply Fin.ext
    simpa using hax

/-- Two cyclic intervals meet iff some offsets `a, b < k` give the same point. -/
lemma inter_nonempty_iff {n k i j : ℕ} (hn : 0 < n) :
    (cyclicInterval n k i ∩ cyclicInterval n k j).Nonempty ↔
      ∃ a < k, ∃ b < k, (i + a) % n = (j + b) % n := by
  constructor
  · rintro ⟨x, hx⟩
    rw [Finset.mem_inter] at hx
    obtain ⟨a, ha, hax⟩ := (mem_cyclicInterval hn x).1 hx.1
    obtain ⟨b, hb, hbx⟩ := (mem_cyclicInterval hn x).1 hx.2
    exact ⟨a, ha, b, hb, by rw [hax, hbx]⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨⟨(i + a) % n, Nat.mod_lt _ hn⟩, ?_⟩
    rw [Finset.mem_inter]
    constructor
    · exact (mem_cyclicInterval hn _).2 ⟨a, ha, rfl⟩
    · exact (mem_cyclicInterval hn _).2 ⟨b, hb, by rw [← hab]⟩

/-- **Offset range.** If arc `A_j` meets arc `A_{i₀}`, then the circular offset
`r(j) = (j + (n - i₀)) mod n` lies in the lower block `[0, k)` or the upper block
`(n-k, n)`. -/
lemma offset_range {n k i₀ j : ℕ} (hn : n ≥ 2 * k) (_hk : 0 < k) (hi₀ : i₀ < n)
    (h : ∃ a < k, ∃ b < k, (i₀ + a) % n = (j + b) % n) :
    (j + (n - i₀)) % n < k ∨ n - k < (j + (n - i₀)) % n := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  have hn0 : 0 < n := by omega
  have hrjn : (j + (n - i₀)) % n < n := Nat.mod_lt _ hn0
  -- `(j + (n-i₀)) + b ≡ a  [MOD n]`
  have key : ((j + (n - i₀)) + b) % n = a := by
    have hc : ((j + (n - i₀)) + b + i₀) % n = (a + i₀) % n := by
      have hsum : j + (n - i₀) + b + i₀ = (j + b) + n := by omega
      rw [hsum, Nat.add_mod_right, ← hab, Nat.add_comm i₀ a]
    have hcancel : ((j + (n - i₀)) + b) % n = a % n :=
      Nat.ModEq.add_right_cancel' i₀
        (show ((j + (n - i₀)) + b + i₀) ≡ (a + i₀) [MOD n] from hc)
    rw [hcancel, Nat.mod_eq_of_lt (show a < n by omega)]
  -- fold the inner `% n`
  have key2 : ((j + (n - i₀)) % n + b) % n = a := by rwa [Nat.mod_add_mod]
  rcases Nat.lt_or_ge ((j + (n - i₀)) % n + b) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at key2
    left; omega
  · have hsub : ((j + (n - i₀)) % n + b) % n = (j + (n - i₀)) % n + b - n := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at key2
    right; omega

/-- **Offset injectivity.** The map `x ↦ (x + (n - i₀)) mod n` is injective on
positions `< n`. -/
lemma offset_inj {n i₀ p q : ℕ} (hp : p < n) (hq : q < n)
    (h : (p + (n - i₀)) % n = (q + (n - i₀)) % n) : p = q := by
  have hcancel : p % n = q % n :=
    Nat.ModEq.add_right_cancel' (n - i₀)
      (show (p + (n - i₀)) ≡ (q + (n - i₀)) [MOD n] from h)
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at hcancel
  exact hcancel

/-- **Disjointness of a collapsed pair.** If `r(p) = c` (lower block, `c < k`) and
`r(q) = c + (n - k)` (upper block), the arcs `A_p` and `A_q` have starts differing
by exactly `k`, so they are disjoint. -/
lemma not_intersect_mixed {n k i₀ p q c : ℕ} (hn : n ≥ 2 * k) (_hk : 0 < k)
    (hc : c < k) (hrp : (p + (n - i₀)) % n = c)
    (hrq : (q + (n - i₀)) % n = c + (n - k)) :
    ¬ (∃ a < k, ∃ b < k, (p + a) % n = (q + b) % n) := by
  rintro ⟨a, ha, b, hb, hab⟩
  -- `p ≡ q + k  [MOD n]`
  have hpqk : p ≡ q + k [MOD n] := by
    have step : ((q + (n - i₀)) + k) % n = c := by
      rw [← Nat.mod_add_mod, hrq, show c + (n - k) + k = c + n by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (show c < n by omega)]
    have e : (q + k + (n - i₀)) % n = (p + (n - i₀)) % n := by
      rw [show q + k + (n - i₀) = (q + (n - i₀)) + k by ring, step, hrp]
    exact (Nat.ModEq.add_right_cancel' (n - i₀)
      (show (q + k + (n - i₀)) ≡ (p + (n - i₀)) [MOD n] from e)).symm
  -- combine with the intersection equation
  have hab' : (p + a) ≡ (q + b) [MOD n] := hab
  have hcomb : (q + k) + a ≡ q + b [MOD n] := (hpqk.add_right a).symm.trans hab'
  have hcomb2 : q + (k + a) ≡ q + b [MOD n] := by
    have h0 : (q + k) + a = q + (k + a) := by ring
    rwa [h0] at hcomb
  have hka : (k + a) % n = b % n := Nat.ModEq.add_left_cancel' q hcomb2
  rw [Nat.mod_eq_of_lt (show k + a < n by omega),
      Nat.mod_eq_of_lt (show b < n by omega)] at hka
  omega

/-- The collapse map sending arc starts to their representative in `range k`. -/
private def gmap (n k i₀ j : ℕ) : ℕ :=
  if (j + (n - i₀)) % n < k then (j + (n - i₀)) % n else (j + (n - i₀)) % n - (n - k)

/-- **Katona's cyclic-interval lemma (OQ-01).** In any cyclic order of `n ≥ 2k`
points (`k > 0`), at most `k` of the `n` cyclic intervals of length `k` can be
pairwise intersecting. This is exactly the parent's axiom
`at_most_k_intersecting_cyclic_intervals`, now proved. -/
theorem at_most_k_intersecting_cyclic_intervals (n k : ℕ) (hn : n ≥ 2 * k) (hk : 0 < k) :
    ∀ (I : Finset ℕ), (∀ i ∈ I, i < n) →
      (∀ i j, i ∈ I → j ∈ I → (cyclicInterval n k i ∩ cyclicInterval n k j).Nonempty) →
      I.card ≤ k := by
  intro I hI hinter
  have hn0 : 0 < n := by omega
  rcases I.eq_empty_or_nonempty with hE | hNE
  · simp [hE]
  obtain ⟨i₀, hi₀⟩ := hNE
  have hi₀n : i₀ < n := hI i₀ hi₀
  -- offset range fact for every member, via intersection with the anchor `i₀`
  have hrange : ∀ j ∈ I, (j + (n - i₀)) % n < k ∨ n - k < (j + (n - i₀)) % n := by
    intro j hj
    have hInt := hinter i₀ j hi₀ hj
    rw [inter_nonempty_iff hn0] at hInt
    exact offset_range hn hk hi₀n hInt
  rw [show k = (Finset.range k).card from (Finset.card_range k).symm]
  apply Finset.card_le_card_of_injOn (gmap n k i₀)
  · -- `gmap` lands in `range k`
    intro j hj
    rw [Finset.mem_coe] at hj
    rw [Finset.mem_coe, Finset.mem_range]
    simp only [gmap]
    have hjmod : (j + (n - i₀)) % n < n := Nat.mod_lt _ hn0
    rcases hrange j hj with h | h
    · rw [if_pos h]; exact h
    · have hnk : ¬ (j + (n - i₀)) % n < k := by omega
      rw [if_neg hnk]; omega
  · -- `gmap` is injective on `I`
    intro p hp q hq hpq
    rw [Finset.mem_coe] at hp hq
    have hpn : p < n := hI p hp
    have hqn : q < n := hI q hq
    have hrp := hrange p hp
    have hrq := hrange q hq
    simp only [gmap] at hpq
    by_cases hcp : (p + (n - i₀)) % n < k <;> by_cases hcq : (q + (n - i₀)) % n < k
    · -- both lower
      rw [if_pos hcp, if_pos hcq] at hpq
      exact offset_inj hpn hqn hpq
    · -- p lower, q upper
      exfalso
      rw [if_pos hcp, if_neg hcq] at hpq
      have hrqval : n - k < (q + (n - i₀)) % n := hrq.resolve_left hcq
      have hrqeq : (q + (n - i₀)) % n = (p + (n - i₀)) % n + (n - k) := by omega
      have hInt := hinter p q hp hq
      rw [inter_nonempty_iff hn0] at hInt
      exact not_intersect_mixed (c := (p + (n - i₀)) % n) hn hk hcp rfl hrqeq hInt
    · -- p upper, q lower
      exfalso
      rw [if_neg hcp, if_pos hcq] at hpq
      have hrpval : n - k < (p + (n - i₀)) % n := hrp.resolve_left hcp
      have hrpeq : (p + (n - i₀)) % n = (q + (n - i₀)) % n + (n - k) := by omega
      have hInt := hinter q p hq hp
      rw [inter_nonempty_iff hn0] at hInt
      exact not_intersect_mixed (c := (q + (n - i₀)) % n) hn hk hcq rfl hrpeq hInt
    · -- both upper
      rw [if_neg hcp, if_neg hcq] at hpq
      have hrpval : n - k < (p + (n - i₀)) % n := hrp.resolve_left hcp
      have hrqval : n - k < (q + (n - i₀)) % n := hrq.resolve_left hcq
      have heq : (p + (n - i₀)) % n = (q + (n - i₀)) % n := by omega
      exact offset_inj hpn hqn heq

/-- The bound is achieved: the `k` arcs anchored at a common point (sharing position
`0`) form a pairwise-intersecting family of starting positions `{0, n-1, …, n-k+1}`,
witnessing that `k` cannot be improved. Here we record the simplest instance: a
single arc is a pairwise-intersecting family, so the bound is nonvacuous. -/
theorem singleton_family_bound (n k : ℕ) (hn : n ≥ 2 * k) (hk : 0 < k) (i : ℕ) (hi : i < n) :
    ({i} : Finset ℕ).card ≤ k := by
  apply at_most_k_intersecting_cyclic_intervals n k hn hk
  · intro x hx; rw [Finset.mem_singleton] at hx; omega
  · intro x y hx hy
    rw [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    have hn0 : 0 < n := by omega
    rw [inter_nonempty_iff hn0]
    exact ⟨0, hk, 0, hk, rfl⟩

#check @at_most_k_intersecting_cyclic_intervals
#print axioms at_most_k_intersecting_cyclic_intervals

end ErdosKoRadoOQ01
