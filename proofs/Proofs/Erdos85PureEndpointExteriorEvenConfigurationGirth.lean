import Proofs.Erdos101ProblemOQ02
import Proofs.Erdos85PureEndpointExteriorIncidenceKernel

/-!
# Girth of an even configuration in a linear uniform incidence system

The generic counting lemma here is the circuit-size input for the pure
endpoint exterior block design.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

private theorem le_two_mul_choose_two_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    n ≤ 2 * n.choose 2 := by
  have hid := Erdos101OQ02ST.sq_eq_self_add_two_mul_choose_two n
  have hprod : n * n = n + n * (n - 1) := by
    calc
      n * n = n * ((n - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = n + n * (n - 1) := by ring
  have heq : 2 * n.choose 2 = n * (n - 1) := by
    rw [show n ^ 2 = n * n by ring, hprod] at hid
    omega
  rw [heq]
  have hpred : 1 ≤ n - 1 := by omega
  simpa using Nat.mul_le_mul_left n hpred

/-- A nonempty even configuration in a linear `m`-uniform incidence system
contains at least `m+1` blocks. -/
theorem linear_uniform_even_configuration_card_ge
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (P : Finset α) (L : Finset β) (m : ℕ)
    (hP : P.Nonempty)
    (huniform : ∀ p ∈ P, (L.filter fun l => Inc p l).card = m)
    (heven : ∀ l ∈ L, Even (Erdos101OQ02ST.pointsOn Inc P l).card)
    (hlinear : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∀ l₁ ∈ L, ∀ l₂ ∈ L,
        Inc p l₁ → Inc q l₁ → Inc p l₂ → Inc q l₂ → l₁ = l₂) :
    m + 1 ≤ P.card := by
  classical
  have hpoint : ∀ l ∈ L,
      (Erdos101OQ02ST.pointsOn Inc P l).card ≤
        2 * (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2 := by
    intro l hl
    let d := (Erdos101OQ02ST.pointsOn Inc P l).card
    rcases heven l hl with ⟨k, hk⟩
    by_cases hd : d = 0
    · change d ≤ 2 * d.choose 2
      simp [hd]
    · apply le_two_mul_choose_two_of_two_le
      change d = k + k at hk
      omega
  have hincidence : Erdos101OQ02ST.incidences Inc P L = m * P.card := by
    unfold Erdos101OQ02ST.incidences Erdos101OQ02ST.pointsOn
    calc
      (∑ l ∈ L, #(P.filter fun p => Inc p l)) =
          ∑ l ∈ L, ∑ p ∈ P, if Inc p l then 1 else 0 := by
            apply sum_congr rfl
            intro l hl
            rw [card_filter]
      _ = ∑ p ∈ P, ∑ l ∈ L, if Inc p l then 1 else 0 := by
            rw [sum_comm]
      _ = ∑ p ∈ P, #(L.filter fun l => Inc p l) := by
            apply sum_congr rfl
            intro p hp
            rw [card_filter]
      _ = ∑ _p ∈ P, m := by
            apply sum_congr rfl
            intro p hp
            exact huniform p hp
      _ = m * P.card := by simp [mul_comm]
  have hincChoose : Erdos101OQ02ST.incidences Inc P L ≤
      2 * ∑ l ∈ L,
        (Erdos101OQ02ST.pointsOn Inc P l).card.choose 2 := by
    unfold Erdos101OQ02ST.incidences
    rw [Finset.mul_sum]
    exact sum_le_sum (fun l hl => hpoint l hl)
  have hchoose := Erdos101OQ02ST.sum_choose_two_le Inc P L hlinear
  have hmul : m * P.card ≤ 2 * P.card.choose 2 := by omega
  have hpos : 0 < P.card := card_pos.mpr hP
  have hprod : 2 * P.card.choose 2 = P.card * (P.card - 1) := by
    have hid := Erdos101OQ02ST.sq_eq_self_add_two_mul_choose_two P.card
    have hsquare : P.card * P.card =
        P.card + P.card * (P.card - 1) := by
      calc
        P.card * P.card = P.card * ((P.card - 1) + 1) := by
          rw [Nat.sub_add_cancel hpos]
        _ = P.card + P.card * (P.card - 1) := by ring
    rw [show P.card ^ 2 = P.card * P.card by ring, hsquare] at hid
    omega
  rw [hprod] at hmul
  have hcancel : m ≤ P.card - 1 := by
    exact Nat.le_of_mul_le_mul_right (by simpa [mul_comm] using hmul) hpos
  omega

/-- The pure endpoint exterior design contains a nonempty even row
configuration, and every such extracted configuration has at least `m+1`
rows. -/
theorem c4Free_binarySquare_pureEndpoint_exists_large_even_exteriorRowConfiguration
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      ∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  obtain ⟨T, hT, heven⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_even_exteriorRowConfiguration
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ∀ w ∈ T,
      ((univ : Finset P).filter fun y => Inc w y).card = m := by
    intro w hwT
    have himage : (((univ : Finset P).filter fun y => Inc w y).image
        fun y => y.1) = G.neighborFinset w.1 ∩ S := by
      ext y
      constructor
      · intro hy
        obtain ⟨yy, hyy, rfl⟩ := mem_image.mp hy
        exact mem_inter.mpr ⟨
          (G.mem_neighborFinset w.1 yy.1).mpr (mem_filter.mp hyy).2, yy.2⟩
      · intro hy
        let yy : P := ⟨y, (mem_inter.mp hy).2⟩
        exact mem_image.mpr ⟨yy, mem_filter.mpr ⟨mem_univ _,
          (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hy).1⟩, rfl⟩
    calc
      ((univ : Finset P).filter fun y => Inc w y).card =
          ((((univ : Finset P).filter fun y => Inc w y).image
            fun y => y.1).card) :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = (G.neighborFinset w.1 ∩ S).card := congrArg card himage
      _ = m := hdesign.1 w.1 (by
        have hwF : w.1 ∉ F := mem_compl.mp w.2
        simpa [F] using hwF)
  have hlinear : ∀ w ∈ T, ∀ w' ∈ T, w ≠ w' →
      ∀ y ∈ (univ : Finset P), ∀ z ∈ (univ : Finset P),
        Inc w y → Inc w' y → Inc w z → Inc w' z → y = z := by
    intro w hw w' hw' hww' y _hy z _hz hwy hw'y hwz hw'z
    have hwwVal : w.1 ≠ w'.1 := fun h => hww' (Subtype.ext h)
    have hwF : w.1 ∉ F := mem_compl.mp w.2
    have hw'F : w'.1 ∉ F := mem_compl.mp w'.2
    have hinter := hdesign.2.1 w.1 (by simpa [F] using hwF)
      w'.1 (by simpa [F] using hw'F) hwwVal
    apply Subtype.ext
    apply card_le_one.mp hinter
    · exact mem_inter.mpr ⟨mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y.1).mpr hwy, y.2⟩,
        mem_inter.mpr ⟨(G.mem_neighborFinset w'.1 y.1).mpr hw'y, y.2⟩⟩
    · exact mem_inter.mpr ⟨mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 z.1).mpr hwz, z.2⟩,
        mem_inter.mpr ⟨(G.mem_neighborFinset w'.1 z.1).mpr hw'z, z.2⟩⟩
  have hlarge := linear_uniform_even_configuration_card_ge
    Inc T (univ : Finset P) m hT huniform
    (by intro y _hy; exact heven y) hlinear
  exact ⟨T, hT, hlarge, heven⟩

end

end Erdos85

#print axioms Erdos85.linear_uniform_even_configuration_card_ge
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_large_even_exteriorRowConfiguration
