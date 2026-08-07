import Proofs.Erdos85PrimeConvolutionObstruction

/-!
# A mass terminal for the three-point parity pattern

In the exact-square family the relevant prime is `p = d + s`, with
`s ≥ 7`.  Consequently the weak statement that a projected anchor is odd
away from three exceptional residues already forces at least `p - 3 > d`
units of mass.  Since all diagonal anchor supports together have mass at
most the degree `d`, this closes the branch without using convolution and
without needing parity information at the exceptional residues.
-/

namespace Erdos85

noncomputable section

/-- A natural-valued function which is odd outside the three half-step
exceptions has total mass at least `p - 3`. -/
theorem threePoint_odd_pattern_mass_lower_bound
    {p : ℕ} [NeZero p] (hp7 : 7 ≤ p)
    (b : ZMod p) (hb : b + b = 1)
    (h : ZMod p → ℕ)
    (hodd : ∀ t, t ∉ ({0, b, -b} : Finset (ZMod p)) → Odd (h t)) :
    p - 3 ≤ ∑ t, h t := by
  classical
  let S : Finset (ZMod p) :=
    Finset.univ.filter (fun t ↦ t ∉ ({0, b, -b} : Finset (ZMod p)))
  have hthree : ({0, b, -b} : Finset (ZMod p)).card = 3 :=
    threePoint_card_of_modulus_ge_four (by omega) b hb
  have hScard : S.card = p - 3 := by
    have hSeq : S = Finset.univ \ ({0, b, -b} : Finset (ZMod p)) := by
      ext t
      simp [S]
    rw [hSeq, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.subset_univ _),
      Finset.card_univ, ZMod.card, hthree]
  have hpoint : ∀ t ∈ S, 1 ≤ h t := by
    intro t ht
    have htout : t ∉ ({0, b, -b} : Finset (ZMod p)) := by
      simpa [S] using ht
    exact (hodd t htout).pos
  have hrestricted : S.card ≤ ∑ t ∈ S, h t := by
    calc
      S.card = ∑ _t ∈ S, 1 := by simp
      _ ≤ ∑ t ∈ S, h t := by
        exact Finset.sum_le_sum fun t ht ↦ hpoint t ht
  have hsubset : ∑ t ∈ S, h t ≤ ∑ t, h t := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ ↦ Nat.zero_le _)
  rw [← hScard]
  exact hrestricted.trans hsubset

/-- In a gap family `p = d + s` with `s ≥ 4`, the preceding parity pattern
is incompatible with total mass at most `d`.  The square application has
the stronger bound `s ≥ 7`. -/
theorem false_of_threePoint_odd_pattern_of_mass_le_degree
    {p d s : ℕ} [NeZero p]
    (hp7 : 7 ≤ p) (hpEq : p = d + s) (hs4 : 4 ≤ s)
    (b : ZMod p) (hb : b + b = 1)
    (h : ZMod p → ℕ)
    (hodd : ∀ t, t ∉ ({0, b, -b} : Finset (ZMod p)) → Odd (h t))
    (hmass : ∑ t, h t ≤ d) : False := by
  have hlower := threePoint_odd_pattern_mass_lower_bound hp7 b hb h hodd
  omega

/-- Component-count form of the mass terminal.  If every selected diagonal
support has size at most two and twice the selected count fits below a bound
`N`, while `p` exceeds `N` by at least four, the nonexceptional odd pattern
is impossible. -/
theorem false_of_threePoint_odd_pattern_of_two_count_le
    {p N gap C : ℕ} [NeZero p]
    (hp7 : 7 ≤ p) (hpEq : p = N + gap) (hgap4 : 4 ≤ gap)
    (b : ZMod p) (hb : b + b = 1)
    (h : ZMod p → ℕ)
    (hodd : ∀ t, t ∉ ({0, b, -b} : Finset (ZMod p)) → Odd (h t))
    (hmass : ∑ t, h t ≤ 2 * C) (hcount : 2 * C ≤ N) : False := by
  exact false_of_threePoint_odd_pattern_of_mass_le_degree hp7 hpEq hgap4
    b hb h hodd (hmass.trans hcount)

/-- If `a ≥ 2` and `a*C ≤ N`, then the preceding count hypothesis follows
automatically.  This is the arithmetic shape of the exact-square minimum
layer: normalized component orders sum to `N`, so a minimum coefficient at
least two bounds twice the number of components by `N`. -/
theorem false_of_threePoint_odd_pattern_of_minCoefficient_two
    {p N gap C a : ℕ} [NeZero p]
    (hp7 : 7 ≤ p) (hpEq : p = N + gap) (hgap4 : 4 ≤ gap)
    (ha2 : 2 ≤ a) (hweightedCount : a * C ≤ N)
    (b : ZMod p) (hb : b + b = 1)
    (h : ZMod p → ℕ)
    (hodd : ∀ t, t ∉ ({0, b, -b} : Finset (ZMod p)) → Odd (h t))
    (hmass : ∑ t, h t ≤ 2 * C) : False := by
  apply false_of_threePoint_odd_pattern_of_two_count_le hp7 hpEq hgap4
    b hb h hodd hmass
  nlinarith

/-- If a finite family of positive weights has at most one weight below
two, then twice the number of indices is at most the total weight plus one.
This is the counting inequality needed for the unique-minimum `a = 1`
escape: the unique minimum coefficient may contribute only one, while every
other coefficient contributes at least two. -/
theorem two_mul_card_le_sum_add_one_of_atMostOne_unit
    {C : Type*} [DecidableEq C]
    (S : Finset C) (w : C → ℕ)
    (hpos : ∀ c ∈ S, 1 ≤ w c)
    (hunit : ∀ c ∈ S, ∀ e ∈ S, w c = 1 → w e = 1 → c = e) :
    2 * S.card ≤ (∑ c ∈ S, w c) + 1 := by
  classical
  by_cases hnone : ∀ c ∈ S, w c ≠ 1
  · have htwo : ∀ c ∈ S, 2 ≤ w c := by
      intro c hc
      have := hpos c hc
      have := hnone c hc
      omega
    calc
      2 * S.card = ∑ _c ∈ S, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ S, w c := Finset.sum_le_sum fun c hc ↦ htwo c hc
      _ ≤ (∑ c ∈ S, w c) + 1 := Nat.le_add_right _ _
  · push Not at hnone
    obtain ⟨c₀, hc₀, hw₀⟩ := hnone
    have htwo : ∀ c ∈ S.erase c₀, 2 ≤ w c := by
      intro c hc
      have hcS := Finset.mem_of_mem_erase hc
      have hcne := (Finset.mem_erase.mp hc).1
      have hcpos := hpos c hcS
      have hcnot : w c ≠ 1 := by
        intro hc1
        exact hcne (hunit c hcS c₀ hc₀ hc1 hw₀)
      omega
    have hsumLower :
        2 * (S.erase c₀).card ≤ ∑ c ∈ S.erase c₀, w c := by
      calc
        2 * (S.erase c₀).card = ∑ _c ∈ S.erase c₀, 2 := by
          simp [Nat.mul_comm]
        _ ≤ ∑ c ∈ S.erase c₀, w c :=
          Finset.sum_le_sum fun c hc ↦ htwo c hc
    have hcard : S.card = (S.erase c₀).card + 1 := by
      have hcardPos : 0 < S.card := Finset.card_pos.mpr ⟨c₀, hc₀⟩
      rw [Finset.card_erase_of_mem hc₀]
      omega
    have hsum : ∑ c ∈ S, w c = w c₀ + ∑ c ∈ S.erase c₀, w c := by
      calc
        ∑ c ∈ S, w c = (∑ c ∈ S.erase c₀, w c) + w c₀ :=
          (Finset.sum_erase_add _ _ hc₀).symm
        _ = w c₀ + ∑ c ∈ S.erase c₀, w c := Nat.add_comm _ _
    rw [hcard, hsum, hw₀]
    omega

/-- The unique-unit version of the mass terminal.  Allowing one normalized
component coefficient to equal one weakens `2*C ≤ N` only to
`2*C ≤ N+1`; a gap of five still gives a contradiction.  The exact-square
application has gap at least seven. -/
theorem false_of_threePoint_odd_pattern_of_atMostOne_unit
    {p N gap C : ℕ} [NeZero p]
    (hp7 : 7 ≤ p) (hpEq : p = N + gap) (hgap5 : 5 ≤ gap)
    (b : ZMod p) (hb : b + b = 1)
    (h : ZMod p → ℕ)
    (hodd : ∀ t, t ∉ ({0, b, -b} : Finset (ZMod p)) → Odd (h t))
    (hmass : ∑ t, h t ≤ 2 * C) (hcount : 2 * C ≤ N + 1) : False := by
  have hlower := threePoint_odd_pattern_mass_lower_bound hp7 b hb h hodd
  omega

end

end Erdos85
