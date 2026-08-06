import Proofs.Erdos85MixedParityComplete
import Proofs.Erdos85PrimeSectorSize
import Proofs.Erdos85MixedSelection

/-!
# The parity terminal is self-terminating at large primes

The three-point parity terminal says that under `hodd` and an odd
selected count, `mixedProjectedAnchor G u p s` is odd — in particular
positive — at every `s` outside `{0, b, -b}`.  Summing over frequencies,
the sector anchor mass is at least `p - 3`.  But the mass is bounded by
twice the sector count, and the sector occupies at least `p` vertices
per member, so `p(p-3) ≤ 2·|V| = 2(d(d-1)+3)`.

Hence **an odd `p`-divisible count is impossible at any prime with
`p(p-3) > 2(d(d-1)+3)`** — with no quadratic-residue hypothesis at all.
Together with the determinant obstruction (nonresidue primes force even
counts), the entire odd-count/parity program is confined to the finite
window `7 ≤ p ≲ √2·d`, and every large prime has an even sector.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The parity-terminal mass floor.**  Whenever the three-point parity
terminal fires — `hodd` plus an odd `p`-divisible count at any prime
`p ≥ 7` — the selected anchor mass is at least `p - 3`: the projected
anchor count is odd, hence positive, at every frequency outside the
three exceptional points.  This is the quantitative output of the
terminal for the small-prime window. -/
theorem le_pDivisibleAnchorMass_of_countOdd
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hcountOdd : Odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card) :
    p - 3 ≤ pDivisibleAnchorMass G u p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hpne : p ≠ 2 := by omega
    intro h20
    have h2n : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h20
    exact hpne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2n))
  have hb : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by
    rw [← two_mul]
    exact mul_inv_cancel₀ h2
  have hterm := odd_mixedProjectedAnchor_iff_threePoint G hfree hd heven
    hmin hcard hp hp7 u hu huRange huD hℓ3 hodd hcountOdd
    ((2 : ZMod p)⁻¹) hb
  have hlower : p - 3 ≤ pDivisibleAnchorMass G u p := by
    have hTcard : ({0, (2 : ZMod p)⁻¹, -(2 : ZMod p)⁻¹} :
        Finset (ZMod p)).card ≤ 3 := by
      apply le_trans (Finset.card_insert_le _ _)
      have h1 := Finset.card_insert_le ((2 : ZMod p)⁻¹)
        ({-(2 : ZMod p)⁻¹} : Finset (ZMod p))
      simp only [Finset.card_singleton] at h1 ⊢
      omega
    have hcompl : p - 3 ≤ ((Finset.univ : Finset (ZMod p)) \
        ({0, (2 : ZMod p)⁻¹, -(2 : ZMod p)⁻¹} : Finset (ZMod p))).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      have hzp : (Finset.univ : Finset (ZMod p)).card = p := by
        rw [Finset.card_univ, ZMod.card]
      omega
    calc
      p - 3 ≤ ((Finset.univ : Finset (ZMod p)) \
          ({0, (2 : ZMod p)⁻¹, -(2 : ZMod p)⁻¹} :
            Finset (ZMod p))).card := hcompl
      _ = ∑ _s ∈ (Finset.univ : Finset (ZMod p)) \
          ({0, (2 : ZMod p)⁻¹, -(2 : ZMod p)⁻¹} : Finset (ZMod p)), 1 := by
        rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ s ∈ (Finset.univ : Finset (ZMod p)) \
          ({0, (2 : ZMod p)⁻¹, -(2 : ZMod p)⁻¹} : Finset (ZMod p)),
          mixedProjectedAnchor G u p s := by
        apply Finset.sum_le_sum
        intro s hs
        have hsnot := (Finset.mem_sdiff.mp hs).2
        rcases (hterm s).mpr hsnot with ⟨k, hk⟩
        omega
      _ ≤ ∑ s : ZMod p, mixedProjectedAnchor G u p s :=
        Finset.sum_le_sum_of_subset Finset.sdiff_subset
      _ = pDivisibleAnchorMass G u p :=
        sum_mixedProjectedAnchor_eq_mass G u
  exact hlower

/-- **Large-prime parity contradiction.**  At the exact even boundary,
`hodd` together with an odd `p`-divisible component count is impossible
once `p(p-3) > 2(d(d-1)+3)`: the three-point parity forces anchor mass at
least `p-3`, while the sector size bounds it by `2(d(d-1)+3)/p`. -/
theorem false_of_secondOrder_countOdd_of_large_prime
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hbig : 2 * (d * (d - 1) + 3) < p * (p - 3))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard)
    (hcountOdd : Odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card) :
    False := by
  have hlower := le_pDivisibleAnchorMass_of_countOdd G hfree hd heven
    hmin hcard hp hp7 u hu huRange huD hℓ3 hodd hcountOdd
  have hupper := pDivisibleAnchorMass_le_two_mul_component_card
    G hfree hd heven hmin hcard u hu huRange huD hℓ3 hodd
  have hsize := prime_mul_pDivisible_component_card_le_card
    (secondOrderDefectGraph G) (p := p) hp.pos
  rw [hcard] at hsize
  have hfinal : p * (p - 3) ≤ 2 * (d * (d - 1) + 3) := by
    calc
      p * (p - 3) ≤ p * (2 * (Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard)).card) :=
        Nat.mul_le_mul_left p (by omega)
      _ = 2 * (p * (Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard)).card) := by ring
      _ ≤ 2 * (d * (d - 1) + 3) := Nat.mul_le_mul_left 2 hsize
  exact Nat.lt_irrefl _ (lt_of_le_of_lt hfinal hbig)

/-- **Large primes have even sectors.**  Under `hodd`, every prime with
`p(p-3) > 2(d(d-1)+3)` selects an even number of `p`-divisible defect
components — the odd-count branch self-destructs, independent of the
quadratic character of `d-3`. -/
theorem even_pDivisible_filter_card_of_large_prime
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p) (hp7 : 7 ≤ p)
    (hbig : 2 * (d * (d - 1) + 3) < p * (p - 3))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hodd : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard → Odd c.supp.ncard) :
    Even (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card := by
  rcases Nat.even_or_odd (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card with he | ho
  · exact he
  · exact (false_of_secondOrder_countOdd_of_large_prime G hfree hd heven
      hmin hcard hp hp7 hbig u hu huRange huD hℓ3 hodd ho).elim

/-- **The selection window is finite.**  At the exact even boundary with a
cycle labeling, either some prime in the window
`7 ≤ p`, `p(p-3) ≤ 2(d(d-1)+3)` satisfies both parity-terminal
hypotheses, or the length family is selection-obstructed: usable primes
beyond the window are annihilated by the large-prime parity terminal. -/
theorem exists_window_selection_or_obstructed
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard) :
    (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧
      p * (p - 3) ≤ 2 * (d * (d - 1) + 3) ∧
      (∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        p ∣ c.supp.ncard → Odd c.supp.ncard) ∧
      Odd (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard)).card) ∨
    SelectionObstructed (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦ c.supp.ncard) := by
  rcases exists_selection_or_obstructed (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦ c.supp.ncard) with
    ⟨p, hp, hp7, hodd, hcountOdd⟩ | hobs
  · left
    refine ⟨p, hp, hp7, ?_, hodd, hcountOdd⟩
    rcases Nat.le_or_lt (p * (p - 3)) (2 * (d * (d - 1) + 3)) with hle | hgt
    · exact hle
    · exact (false_of_secondOrder_countOdd_of_large_prime G hfree hd heven
        hmin hcard hp hp7 hgt u hu huRange huD hℓ3 hodd hcountOdd).elim
  · right
    exact hobs

end

end Erdos85
