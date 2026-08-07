import Proofs.Erdos85EqualBlockFiberParity

/-!
# Aggregate parity of mixed admissible fibers

For a nonexceptional residue modulo an odd prime, every odd cycle whose
length is divisible by that prime contributes an odd-sized admissible fiber.
Thus the aggregate parity is precisely the parity of the number of selected
cycle components.
-/

namespace Erdos85

noncomputable section

/-- Dividing an odd number by an odd divisor preserves oddness. -/
theorem odd_div_of_odd_of_dvd
    {p n : ℕ} (hnOdd : Odd n) (hpOdd : Odd p) (hpn : p ∣ n) :
    Odd (n / p) := by
  have hpPos : 0 < p := hpOdd.pos
  have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
  rw [← hmul, Nat.odd_mul] at hnOdd
  exact hnOdd.2

/-- Away from the three exceptional residues, aggregate admissible-fiber
parity depends only on the sum of the length quotients `ℓ c / p`; no parity
hypothesis on the individual component lengths is needed. -/
theorem odd_sum_admissibleFibers_iff_odd_quotientSum
    {C : Type*} [Fintype C] [DecidableEq C]
    (ℓ : C → ℕ) [∀ c, NeZero (ℓ c)]
    {p : ℕ} [NeZero p] (hp7 : 7 ≤ p)
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (t : ZMod p) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    Odd (∑ c ∈ Finset.univ.filter (fun c ↦ p ∣ ℓ c),
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) ↔
    Odd (∑ c ∈ Finset.univ.filter (fun c ↦ p ∣ ℓ c), ℓ c / p) := by
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ ℓ c)
  have hterm : ∀ c ∈ S,
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card = ℓ c / p := by
    intro c hc
    have hpc : p ∣ ℓ c := by simpa [S] using hc
    have hfilt : (admissibleDifferences (ℓ c)).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t) =
        (admissibleDifferences (ℓ c)).filter (fun δ ↦
          ZMod.castHom hpc (ZMod p) δ = t) := by
      ext δ
      simp only [Finset.mem_filter]
      have hcast : ZMod.castHom hpc (ZMod p) δ =
          ((δ.val : ℕ) : ZMod p) := by
        calc
          ZMod.castHom hpc (ZMod p) δ =
              ZMod.castHom hpc (ZMod p)
                ((δ.val : ℕ) : ZMod (ℓ c)) :=
            congrArg _ (ZMod.natCast_zmod_val δ).symm
          _ = ((δ.val : ℕ) : ZMod p) := map_natCast _ _
      rw [hcast]
    rw [hfilt, card_admissible_fiber (hℓ3 c) hpc hp7 t,
      if_neg ht0, if_neg ht1, if_neg htm1]
    simp
  have hsum :
      (∑ c ∈ S, ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) =
      ∑ c ∈ S, ℓ c / p := by
    apply Finset.sum_congr rfl
    intro c hc
    exact hterm c hc
  change Odd (∑ c ∈ S, ((admissibleDifferences (ℓ c)).filter (fun δ ↦
    ((δ.val : ℕ) : ZMod p) = t)).card) ↔ Odd (∑ c ∈ S, ℓ c / p)
  rw [hsum]

/-- At an exceptional residue, each selected component loses exactly one
point from its projection fiber.  Hence odd total quotient mass together
with an odd number of selected components makes the aggregate admissible
fiber even, again without individual length-parity assumptions. -/
theorem even_sum_admissibleFibers_of_exceptional_of_odd_totals
    {C : Type*} [Fintype C] [DecidableEq C]
    (ℓ : C → ℕ) [∀ c, NeZero (ℓ c)]
    {p : ℕ} [NeZero p] (hp7 : 7 ≤ p)
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (t : ZMod p) (ht : t ∈ ({0, 1, -1} : Finset (ZMod p)))
    (hmassOdd : Odd (∑ c ∈ Finset.univ.filter (fun c ↦ p ∣ ℓ c),
      ℓ c / p))
    (hcountOdd : Odd (Finset.univ.filter (fun c ↦ p ∣ ℓ c)).card) :
    Even (∑ c ∈ Finset.univ.filter (fun c ↦ p ∣ ℓ c),
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) := by
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ ℓ c)
  have hp1 : (1 : ZMod p) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hpm0 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr hp1
  have hpm1 : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h
    have := Nat.le_of_dvd (by norm_num)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
    omega
  have hterm : ∀ c ∈ S,
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card + 1 = ℓ c / p := by
    intro c hc
    have hpc : p ∣ ℓ c := by simpa [S] using hc
    have hpPos : 0 < p := by omega
    have hqPos : 0 < ℓ c / p :=
      Nat.div_pos (Nat.le_of_dvd (by have := hℓ3 c; omega) hpc) hpPos
    have hfilt : (admissibleDifferences (ℓ c)).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t) =
        (admissibleDifferences (ℓ c)).filter (fun δ ↦
          ZMod.castHom hpc (ZMod p) δ = t) := by
      ext δ
      simp only [Finset.mem_filter]
      have hcast : ZMod.castHom hpc (ZMod p) δ =
          ((δ.val : ℕ) : ZMod p) := by
        calc
          ZMod.castHom hpc (ZMod p) δ =
              ZMod.castHom hpc (ZMod p)
                ((δ.val : ℕ) : ZMod (ℓ c)) :=
            congrArg _ (ZMod.natCast_zmod_val δ).symm
          _ = ((δ.val : ℕ) : ZMod p) := map_natCast _ _
      rw [hcast]
    rw [hfilt, card_admissible_fiber (hℓ3 c) hpc hp7 t]
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · simp [hp1.symm, hpm0.symm]
      omega
    · simp [hp1, hpm1.symm]
      omega
    · simp [hpm0, hpm1]
      omega
  have hsum :
      (∑ c ∈ S, ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) + S.card =
      ∑ c ∈ S, ℓ c / p := by
    calc
      (∑ c ∈ S, ((admissibleDifferences (ℓ c)).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t)).card) + S.card =
          ∑ c ∈ S, (((admissibleDifferences (ℓ c)).filter (fun δ ↦
            ((δ.val : ℕ) : ZMod p) = t)).card + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ c ∈ S, ℓ c / p := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hterm c hc
  change Odd (∑ c ∈ S, ℓ c / p) at hmassOdd
  change Odd S.card at hcountOdd
  change Even (∑ c ∈ S, ((admissibleDifferences (ℓ c)).filter (fun δ ↦
    ((δ.val : ℕ) : ZMod p) = t)).card)
  rw [Nat.even_iff]
  have hmod := congrArg (fun n : ℕ ↦ n % 2) hsum
  rw [Nat.add_mod, Nat.odd_iff.mp hcountOdd,
    Nat.odd_iff.mp hmassOdd] at hmod
  omega

/-- The total admissible fiber over the `p`-divisible odd components is odd
exactly when the number of those components is odd, away from `0, ±1`. -/
theorem odd_sum_admissibleFibers_iff_odd_componentCount
    {C : Type*} [Fintype C] [DecidableEq C]
    (ℓ : C → ℕ) [∀ c, NeZero (ℓ c)]
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hodd : ∀ c, p ∣ ℓ c → Odd (ℓ c))
    (t : ZMod p) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htm1 : t ≠ -1) :
    Odd (∑ c ∈ Finset.univ.filter (fun c ↦ p ∣ ℓ c),
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) ↔
    Odd (Finset.univ.filter (fun c ↦ p ∣ ℓ c)).card := by
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ ℓ c)
  have hterm : ∀ c ∈ S, Odd
      (((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) := by
    intro c hc
    have hpc : p ∣ ℓ c := by simpa [S] using hc
    have hfilt : (admissibleDifferences (ℓ c)).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t) =
        (admissibleDifferences (ℓ c)).filter (fun δ ↦
          ZMod.castHom hpc (ZMod p) δ = t) := by
      ext δ
      simp only [Finset.mem_filter]
      have hcast : ZMod.castHom hpc (ZMod p) δ =
          ((δ.val : ℕ) : ZMod p) := by
        calc
          ZMod.castHom hpc (ZMod p) δ =
              ZMod.castHom hpc (ZMod p) ((δ.val : ℕ) : ZMod (ℓ c)) :=
            congrArg _ (ZMod.natCast_zmod_val δ).symm
          _ = ((δ.val : ℕ) : ZMod p) := map_natCast _ _
      rw [hcast]
    rw [hfilt, card_admissible_fiber (hℓ3 c) hpc hp7 t,
      if_neg ht0, if_neg ht1, if_neg htm1]
    simp only [zero_add, Nat.sub_zero]
    exact odd_div_of_odd_of_dvd (hodd c hpc)
      (hp.odd_of_ne_two (by omega)) hpc
  change Odd (∑ c ∈ S,
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) ↔
    Odd S.card
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfilter : S.filter (fun c ↦ Odd
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) = S := by
    ext c
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hc
      exact ⟨hc, hterm c hc⟩
  rw [hfilter]

/-- At any of the three exceptional residues `0, ±1`, every odd target
cycle contributes an even admissible-fiber count (`odd quotient - 1`). -/
theorem even_sum_admissibleFibers_of_exceptional
    {C : Type*} [Fintype C] [DecidableEq C]
    (ℓ : C → ℕ) [∀ c, NeZero (ℓ c)]
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hodd : ∀ c, p ∣ ℓ c → Odd (ℓ c))
    (t : ZMod p) (ht : t ∈ ({0, 1, -1} : Finset (ZMod p))) :
    Even (∑ c ∈ Finset.univ.filter (fun c ↦ p ∣ ℓ c),
      ((admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t)).card) := by
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ ℓ c)
  apply Finset.even_sum
  intro c hc
  have hpc : p ∣ ℓ c := by simpa [S] using hc
  have hfilt : (admissibleDifferences (ℓ c)).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t) =
      (admissibleDifferences (ℓ c)).filter (fun δ ↦
        ZMod.castHom hpc (ZMod p) δ = t) := by
    ext δ
    simp only [Finset.mem_filter]
    have hcast : ZMod.castHom hpc (ZMod p) δ =
        ((δ.val : ℕ) : ZMod p) := by
      calc
        ZMod.castHom hpc (ZMod p) δ =
            ZMod.castHom hpc (ZMod p) ((δ.val : ℕ) : ZMod (ℓ c)) :=
          congrArg _ (ZMod.natCast_zmod_val δ).symm
        _ = ((δ.val : ℕ) : ZMod p) := map_natCast _ _
    rw [hcast]
  rw [hfilt, card_admissible_fiber (hℓ3 c) hpc hp7 t]
  have hqOdd := odd_div_of_odd_of_dvd (hodd c hpc)
    (hp.odd_of_ne_two (by omega)) hpc
  have hp1 : (1 : ZMod p) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hpm0 : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr hp1
  have hpm1 : (-1 : ZMod p) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h
    have := Nat.le_of_dvd (by norm_num)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · simp only [if_pos, if_neg hp1.symm, if_neg hpm0.symm]
    obtain ⟨k, hk⟩ := hqOdd
    refine ⟨k, by omega⟩
  · simp only [if_neg hp1, if_pos, if_neg hpm1.symm, zero_add]
    obtain ⟨k, hk⟩ := hqOdd
    refine ⟨k, by omega⟩
  · simp only [if_neg hpm0, if_neg hpm1, if_pos, zero_add]
    obtain ⟨k, hk⟩ := hqOdd
    refine ⟨k, by omega⟩

end

end Erdos85
