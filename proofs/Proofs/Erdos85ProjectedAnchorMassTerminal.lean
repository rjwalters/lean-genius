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

end

end Erdos85
