import Proofs.Erdos85BinarySquareBipartiteDefectComponentSpectralResidue
import Proofs.Erdos85BinarySquareBipartiteSizeTwoAlternatingExclusion

/-! # Bipartite exclusions in the `[4,2,2]` and `[3,3,2]` strata

The q-generic signed-residue theorem makes the two remaining size-two-containing
order-64 consumers short.  An odd normalized component has an odd, hence
nonzero, exterior residue.  An even component whose only exterior components
are already known nonbipartite has zero exterior residue, forcing the
impossible equation `lambda^2 = 14`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem component_mem_not_of_ne
    {V : Type*} (D : SimpleGraph V)
    (c d : D.ConnectedComponent) (hcd : c ≠ d) {x : V}
    (hx : x ∈ d.supp) : x ∉ c.supp := by
  intro hxc
  apply hcd
  exact ((ConnectedComponent.mem_supp_iff c x).mp hxc).symm.trans
    ((ConnectedComponent.mem_supp_iff d x).mp hx)

private theorem nonzero_on_connectedComponent_of_edge_neg
    {V : Type*} (D : SimpleGraph V)
    (d : D.ConnectedComponent) (w : V → ℤ)
    (hflip : ∀ x y, x ∈ d.supp → D.Adj x y → w y = -w x)
    {x : V} (hx : x ∈ d.supp) (hwx : w x ≠ 0) :
    ∀ y, y ∈ d.supp → w y ≠ 0 := by
  intro y hy
  have hreach : D.Reachable x y :=
    ConnectedComponent.exact
      (((ConnectedComponent.mem_supp_iff d x).mp hx).trans
        ((ConnectedComponent.mem_supp_iff d y).mp hy).symm)
  obtain ⟨p⟩ := hreach
  have key : ∀ {u v : V} (p : D.Walk u v), u ∈ d.supp → w u ≠ 0 → w v ≠ 0 := by
    intro u v p
    induction p with
    | nil => intro _ hu; exact hu
    | cons hadj _ ih =>
        intro hu hwu
        rename_i u' v' z _
        have hv : v' ∈ d.supp := by
          rw [ConnectedComponent.mem_supp_iff d]
          rw [← (ConnectedComponent.mem_supp_iff d u').mp hu]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
        apply ih hv
        rw [hflip u' v' hu hadj]
        omega
  exact key p hx hwx

private theorem bool_sign_coloring_of_nonzero_edge_neg
    {V : Type*} (D : SimpleGraph V) (d : D.ConnectedComponent)
    (w : V → ℤ) (hnonzero : ∀ x, x ∈ d.supp → w x ≠ 0)
    (hflip : ∀ x y, x ∈ d.supp → D.Adj x y → w y = -w x) :
    ∀ x y, x ∈ d.supp → y ∈ d.supp → D.Adj x y →
      decide (0 < w x) ≠ decide (0 < w y) := by
  intro x y hx _hy hxy
  have hneg := hflip x y hx hxy
  have hnx := hnonzero x hx
  by_cases hp : 0 < w x
  · have hnpy : ¬ 0 < w y := by rw [hneg]; omega
    simp [hp, hnpy]
  · have hpy : 0 < w y := by rw [hneg]; omega
    simp [hp, hpy]

/-- In the order-64 `[3,3,2]` shape, a normalized size-three component cannot
be bipartite.  Its exterior residue is odd everywhere, so its sign gives a
bipartition of the size-two component, contradicting the q-generic size-two
exclusion. -/
theorem orderSixtyFour_regular_threeThreeTwo_sizeThree_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d) (hc : c.supp.ncard = 8 * 3)
    (hd : d.supp.ncard = 8 * 2)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) : False := by
  have hcard' : Fintype.card V = 8 * 8 := by norm_num [hcard]
  have hnoUnit : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      e.supp.ncard ≠ 8 := fun e =>
    binarySquare_regular_no_sizeQ_defectComponent_of_even
      G hfree (q := 8) (by omega) (by norm_num) hreg hcard' e
  obtain ⟨lam, w, _hlamEven, _hlamAbs, _hAs, _hwIn, _hwOut,
      hwParity, hflip, _hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree (q := 8) (by omega) hreg hcard' c (m := 3) hc col hbip
  have hdout : ∀ x, x ∈ d.supp → x ∉ c.supp :=
    fun x hx => component_mem_not_of_ne (secondOrderDefectGraph G) c d hcd hx
  have hnonzero : ∀ x, x ∈ d.supp → w x ≠ 0 := by
    intro x hx hwx
    obtain ⟨k, hk⟩ := (hwParity x (hdout x hx)).1
    rw [hwx] at hk
    omega
  let dcol : V → Bool := fun x => decide (0 < w x)
  have hbipd : ∀ x y, x ∈ d.supp → y ∈ d.supp →
      (secondOrderDefectGraph G).Adj x y → dcol x ≠ dcol y := by
    intro x y hx hy hxy
    exact bool_sign_coloring_of_nonzero_edge_neg
      (secondOrderDefectGraph G) d w hnonzero
      (fun u v hu huv => hflip u v (hdout u hu) huv) x y hx hy hxy
  exact binarySquare_regular_sizeTwoPart_bipartite_false
    G hfree (q := 8) (by omega) hreg hcard' d hd
      (fun a _ => hnoUnit a) dcol hbipd

/-- In the order-64 `[4,2,2]` shape, a normalized size-four component cannot
be bipartite.  Any nonzero residue on either size-two component would color it
bipartitely; hence the residue vanishes everywhere and forces `lambda^2=14`.-/
theorem orderSixtyFour_regular_fourTwoTwo_sizeFour_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d) (hce : c ≠ e)
    (hc : c.supp.ncard = 8 * 4)
    (hd : d.supp.ncard = 8 * 2) (he : e.supp.ncard = 8 * 2)
    (hcover : ∀ x, x ∉ c.supp → x ∈ d.supp ∨ x ∈ e.supp)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) : False := by
  have hcard' : Fintype.card V = 8 * 8 := by norm_num [hcard]
  have hnoUnit : ∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      a.supp.ncard ≠ 8 := fun a =>
    binarySquare_regular_no_sizeQ_defectComponent_of_even
      G hfree (q := 8) (by omega) (by norm_num) hreg hcard' a
  obtain ⟨lam, w, _hlamEven, hlamAbs, _hAs, hwIn, _hwOut,
      _hwParity, hflip, hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree (q := 8) (by omega) hreg hcard' c (m := 4) hc col hbip
  have zero_on_sizeTwo : ∀ (a : (secondOrderDefectGraph G).ConnectedComponent),
      c ≠ a → a.supp.ncard = 8 * 2 →
      (∀ b : (secondOrderDefectGraph G).ConnectedComponent,
        b ≠ a → b.supp.ncard ≠ 8) → ∀ x, x ∈ a.supp → w x = 0 := by
    intro a hca ha hnoUnit x hx
    by_contra hwx
    have haout : ∀ u, u ∈ a.supp → u ∉ c.supp :=
      fun u hu => component_mem_not_of_ne (secondOrderDefectGraph G) c a hca hu
    have hflipA : ∀ u v, u ∈ a.supp →
        (secondOrderDefectGraph G).Adj u v → w v = -w u :=
      fun u v hu huv => hflip u v (haout u hu) huv
    have hnonzero := nonzero_on_connectedComponent_of_edge_neg
      (secondOrderDefectGraph G) a w hflipA hx hwx
    let acol : V → Bool := fun u => decide (0 < w u)
    have hbipa : ∀ u v, u ∈ a.supp → v ∈ a.supp →
        (secondOrderDefectGraph G).Adj u v → acol u ≠ acol v := by
      intro u v hu hv huv
      exact bool_sign_coloring_of_nonzero_edge_neg
        (secondOrderDefectGraph G) a w hnonzero hflipA u v hu hv huv
    exact binarySquare_regular_sizeTwoPart_bipartite_false
      G hfree (q := 8) (by omega) hreg hcard' a ha hnoUnit acol hbipa
  have hwd := zero_on_sizeTwo d hcd hd (fun a _ => hnoUnit a)
  have hwe := zero_on_sizeTwo e hce he (fun a _ => hnoUnit a)
  have hwzero : ∀ x, w x = 0 := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact hwIn x hx
    · rcases hcover x hx with hxd | hxe
      · exact hwd x hxd
      · exact hwe x hxe
  obtain ⟨z, hz⟩ : c.supp.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have : c.supp.ncard = 0 := by rw [hempty, Set.ncard_empty]
    omega
  have hsnonzero : bipartiteSignVector G c col z ≠ 0 := by
    simp only [bipartiteSignVector,
      if_pos ((ConnectedComponent.mem_supp_iff c z).mp hz)]
    cases col z <;> norm_num
  have hlamSq : lam * lam = 14 := by
    have hzrow := hrow z hz
    simp only [hwzero, Finset.sum_const_zero] at hzrow
    have hfactor : 2 * ((8 : ℤ) - 1) - lam * lam = 0 :=
      (mul_eq_zero.mp hzrow.symm).resolve_right hsnonzero
    norm_num at hfactor ⊢
    linarith
  have hlamLower : -4 ≤ lam := (abs_le.mp hlamAbs).1
  have hlamUpper : lam ≤ 4 := (abs_le.mp hlamAbs).2
  interval_cases lam <;> norm_num at hlamSq

end

#print axioms Erdos85.orderSixtyFour_regular_threeThreeTwo_sizeThree_not_bipartite
#print axioms Erdos85.orderSixtyFour_regular_fourTwoTwo_sizeFour_not_bipartite

end Erdos85
