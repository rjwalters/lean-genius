import Proofs.Erdos85BinarySquareBipartiteDefectComponentSpectralResidue
import Proofs.Erdos85BinarySquareBipartiteSizeTwoAlternatingExclusion

/-!
# Stratum consumers of the bipartite signed-vector residue

Consumers of `binarySquare_regular_bipartite_defectComponent_signed_residue`.
The alternation `w y = −w x` along defect edges off the bipartite component `c`
means: on every other defect component `c₁`, either `w ≡ 0` or `|w|` is a
nonzero constant and `c₁` is itself bipartite (colour by the sign of `w`).

Two q-generic consequences:

* **(A)** if every other defect component is non-bipartite, then `w ≡ 0` off
  `c`, and the row identity forces `λ² = 2(q−1)`; so a bipartite `c` is
  impossible whenever `2(q−1)` is not a perfect square;
* **(B)** if `c` has odd size `m`, then `w` is odd hence nonzero off `c`, so
  **every** other defect component is bipartite.

At `q = 8` (`2(q−1) = 14`, not a square), combined with the size-two exclusion
`binarySquare_regular_sizeTwoPart_bipartite_false`, these close every
stratum: `[8]`, `[6,2]` (both parts), `[4,2,2]` (all parts), `[3,3,2]` (all
parts), `[2,2,2,2]`, and — with two short arithmetic arguments — `[4,4]` and
`[5,3]`.  Hence **no defect component of an 8-regular `C₄`-free graph on 64
vertices is bipartite.**
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Along an alternating function (`w y = −w x` on every edge leaving `c₁`),
`|w|` is constant on the component `c₁`. -/
theorem abs_eq_on_component_of_alternating {V : Type*}
    (D : SimpleGraph V) (c₁ : D.ConnectedComponent) (w : V → ℤ)
    (halt : ∀ x y, x ∈ c₁.supp → D.Adj x y → w y = -w x) :
    ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp → |w x| = |w y| := by
  intro x y hx hy
  have hreach : D.Reachable x y :=
    ConnectedComponent.exact
      (((ConnectedComponent.mem_supp_iff c₁ x).mp hx).trans
        ((ConnectedComponent.mem_supp_iff c₁ y).mp hy).symm)
  have := reachable_induction_of_adj_closed D (fun u => u ∈ c₁.supp ∧ |w u| = |w x|)
    (fun u v huv hu => by
      refine ⟨?_, ?_⟩
      · rw [ConnectedComponent.mem_supp_iff] at hu ⊢
        rw [← hu.1]
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
      · rw [halt u v hu.1 huv, abs_neg, hu.2])
    hreach ⟨hx, rfl⟩
  exact this.2.symm

/-- If an alternating function is nonzero somewhere on `c₁`, then `c₁` is
bipartite (coloured by the sign of `w`). -/
theorem bipartite_of_alternating_of_ne_zero {V : Type*}
    (D : SimpleGraph V) (c₁ : D.ConnectedComponent) (w : V → ℤ)
    (halt : ∀ x y, x ∈ c₁.supp → D.Adj x y → w y = -w x)
    {x₀ : V} (hx₀ : x₀ ∈ c₁.supp) (hw₀ : w x₀ ≠ 0) :
    ∃ col₁ : V → Bool, ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp → D.Adj x y →
      col₁ x ≠ col₁ y := by
  refine ⟨fun x => decide (0 < w x), ?_⟩
  intro x y hx _ hxy
  have hxne : w x ≠ 0 := by
    intro h
    have := abs_eq_on_component_of_alternating D c₁ w halt x x₀ hx hx₀
    rw [h, abs_zero] at this
    exact hw₀ (abs_eq_zero.mp this.symm)
  have hy := halt x y hx hxy
  by_cases h : 0 < w x
  · have hny : ¬ 0 < w y := by rw [hy]; omega
    simp [h, hny]
  · have hpy : 0 < w y := by rw [hy]; omega
    simp [h, hpy]

/-- **(A)** A bipartite defect component all of whose fellow components are
non-bipartite forces `λ² = 2(q−1)`; impossible when `2(q−1)` is not a square. -/
theorem binarySquare_regular_bipartite_defectComponent_false_of_others_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hns : ∀ t : ℤ, t * t ≠ 2 * ((q : ℤ) - 1))
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (hothers : ∀ c₁ : (secondOrderDefectGraph G).ConnectedComponent, c₁ ≠ c →
      ∀ col₁ : V → Bool, ¬ (∀ x y, x ∈ c₁.supp → y ∈ c₁.supp →
        (secondOrderDefectGraph G).Adj x y → col₁ x ≠ col₁ y)) :
    False := by
  obtain ⟨lam, w, -, -, -, hw_in, -, -, halt, hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree hq hreg hcard c hc col hbip
  -- `w` vanishes off `c`
  have hw_out : ∀ x, x ∉ c.supp → w x = 0 := by
    intro x hx
    by_contra hne
    set c₁ := (secondOrderDefectGraph G).connectedComponentMk x with hc₁
    have hc₁ne : c₁ ≠ c := fun h => hx ((ConnectedComponent.mem_supp_iff c x).mpr h)
    have hxc₁ : x ∈ c₁.supp := (ConnectedComponent.mem_supp_iff c₁ x).mpr rfl
    have halt₁ : ∀ u v, u ∈ c₁.supp → (secondOrderDefectGraph G).Adj u v → w v = -w u := by
      intro u v hu huv
      apply halt u v _ huv
      intro huc
      exact hc₁ne (((ConnectedComponent.mem_supp_iff c₁ u).mp hu).symm.trans
        ((ConnectedComponent.mem_supp_iff c u).mp huc))
    obtain ⟨col₁, hcol₁⟩ := bipartite_of_alternating_of_ne_zero
      (secondOrderDefectGraph G) c₁ w halt₁ hxc₁ hne
    exact hothers c₁ hc₁ne col₁ hcol₁
  -- read the row identity at a vertex of `c`
  obtain ⟨z₀, hz₀⟩ := c.exists_rep
  have hz₀' : (secondOrderDefectGraph G).connectedComponentMk z₀ = c := hz₀
  have hz₀c : z₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c z₀).mpr hz₀'
  have hzero : ∑ y ∈ G.neighborFinset z₀, w y = 0 := by
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y ∈ c.supp
    · exact hw_in y hy
    · exact hw_out y hy
  have h := hrow z₀ hz₀c
  rw [hzero] at h
  have hs : bipartiteSignVector G c col z₀ = 1 ∨ bipartiteSignVector G c col z₀ = -1 := by
    unfold bipartiteSignVector
    rw [if_pos hz₀']
    cases col z₀ <;> simp
  apply hns lam
  rcases hs with hs | hs <;> rw [hs] at h <;> linarith

/-- **(B)** A bipartite defect component of odd size forces every other defect
component to be bipartite. -/
theorem binarySquare_regular_bipartite_defectComponent_odd_forces_others_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) (hodd : Odd m)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (c₁ : (secondOrderDefectGraph G).ConnectedComponent) (hc₁ : c₁ ≠ c) :
    ∃ col₁ : V → Bool, ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp →
      (secondOrderDefectGraph G).Adj x y → col₁ x ≠ col₁ y := by
  obtain ⟨lam, w, -, -, -, -, -, hw_par, halt, -⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree hq hreg hcard c hc col hbip
  obtain ⟨x₀, hx₀⟩ := c₁.exists_rep
  have hx₀' : (secondOrderDefectGraph G).connectedComponentMk x₀ = c₁ := hx₀
  have hx₀c₁ : x₀ ∈ c₁.supp := (ConnectedComponent.mem_supp_iff c₁ x₀).mpr hx₀'
  have hnotc : ∀ u, u ∈ c₁.supp → u ∉ c.supp := by
    intro u hu huc
    exact hc₁ (((ConnectedComponent.mem_supp_iff c₁ u).mp hu).symm.trans
      ((ConnectedComponent.mem_supp_iff c u).mp huc))
  have halt₁ : ∀ u v, u ∈ c₁.supp → (secondOrderDefectGraph G).Adj u v → w v = -w u :=
    fun u v hu huv => halt u v (hnotc u hu) huv
  have hne : w x₀ ≠ 0 := by
    intro h0
    have hpar := (hw_par x₀ (hnotc x₀ hx₀c₁)).1
    rw [h0, zero_add] at hpar
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨j, hj⟩ := hpar
    omega
  exact bipartite_of_alternating_of_ne_zero (secondOrderDefectGraph G) c₁ w halt₁ hx₀c₁ hne

/-- **(A′)** For even `q`: an even-sized bipartite defect component all of whose
fellow components are non-bipartite or even-sized is impossible (no
"not a square" hypothesis needed).  Mod 4: `w ≡ 0` on non-bipartite parts and
`w = ±t₁` with `t₁` even on even bipartite parts, so every part contributes a
multiple of `4` to `Σ_{y ∼ z} w y`, whereas `2(q−1) − λ² ≡ 2 (mod 4)`. -/
theorem binarySquare_regular_bipartite_evenPart_false_of_others_even_or_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqeven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) (hmeven : Even m)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (hothers : ∀ c₁ : (secondOrderDefectGraph G).ConnectedComponent, c₁ ≠ c →
      (∀ col₁ : V → Bool, ¬ (∀ x y, x ∈ c₁.supp → y ∈ c₁.supp →
        (secondOrderDefectGraph G).Adj x y → col₁ x ≠ col₁ y)) ∨
      ∃ m₁ : ℕ, Even m₁ ∧ c₁.supp.ncard = q * m₁) :
    False := by
  obtain ⟨lam, w, hlam_par, -, -, hw_in, -, hw_par, halt, hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree hq hreg hcard c hc col hbip
  obtain ⟨z₀, hz₀⟩ := c.exists_rep
  have hz₀' : (secondOrderDefectGraph G).connectedComponentMk z₀ = c := hz₀
  have hz₀c : z₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c z₀).mpr hz₀'
  -- split the neighbourhood sum by defect component
  have hfib : ∑ y ∈ G.neighborFinset z₀, w y =
      ∑ c₁ : (secondOrderDefectGraph G).ConnectedComponent,
        ∑ y ∈ (G.neighborFinset z₀).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c₁), w y :=
    (Finset.sum_fiberwise (G.neighborFinset z₀)
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y) w).symm
  have hdvd : (4 : ℤ) ∣ ∑ y ∈ G.neighborFinset z₀, w y := by
    rw [hfib]
    apply Finset.dvd_sum
    intro c₁ _
    by_cases hc₁ : c₁ = c
    · subst hc₁
      have : ∑ y ∈ (G.neighborFinset z₀).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c₁), w y = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        exact hw_in y ((ConnectedComponent.mem_supp_iff c₁ y).mpr (Finset.mem_filter.mp hy).2)
      rw [this]
      exact dvd_zero _
    · have hnotc : ∀ u, u ∈ c₁.supp → u ∉ c.supp := by
        intro u hu huc
        exact hc₁ (((ConnectedComponent.mem_supp_iff c₁ u).mp hu).symm.trans
          ((ConnectedComponent.mem_supp_iff c u).mp huc))
      have halt₁ : ∀ u v, u ∈ c₁.supp → (secondOrderDefectGraph G).Adj u v → w v = -w u :=
        fun u v hu huv => halt u v (hnotc u hu) huv
      have hmemF : ∀ y ∈ (G.neighborFinset z₀).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c₁), y ∈ c₁.supp :=
        fun y hy => (ConnectedComponent.mem_supp_iff c₁ y).mpr (Finset.mem_filter.mp hy).2
      rcases hothers c₁ hc₁ with hnb | ⟨m₁, hm₁e, hm₁⟩
      · -- non-bipartite: `w ≡ 0` on `c₁`
        have hzero : ∀ y ∈ (G.neighborFinset z₀).filter
            (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c₁), w y = 0 := by
          intro y hy
          by_contra hne
          obtain ⟨col₁, hcol₁⟩ := bipartite_of_alternating_of_ne_zero
            (secondOrderDefectGraph G) c₁ w halt₁ (hmemF y hy) hne
          exact hnb col₁ hcol₁
        rw [Finset.sum_eq_zero hzero]
        exact dvd_zero _
      · -- even part: `w = ±t` with `t` even on `m₁` (even) neighbours
        set F := (G.neighborFinset z₀).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c₁) with hF
        have hFcard : F.card = m₁ := by
          have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
            G hfree hq hreg hcard c c₁ (x := z₀) hz₀c
          rw [hm₁] at h
          change q * F.card = q * m₁ at h
          exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h
        by_cases hFne : F.Nonempty
        · obtain ⟨y₀, hy₀⟩ := hFne
          set t := |w y₀| with ht
          have habs : ∀ y ∈ F, |w y| = t := fun y hy =>
            abs_eq_on_component_of_alternating (secondOrderDefectGraph G) c₁ w halt₁
              y y₀ (hmemF y hy) (hmemF y₀ hy₀)
          have hteven : Even t := by
            have hwe : Even (w y₀) := by
              obtain ⟨k, hk⟩ := (hw_par y₀ (hnotc y₀ (hmemF y₀ hy₀))).1
              obtain ⟨r, hr⟩ := hmeven
              exact ⟨k - r, by push_cast at hk; omega⟩
            rw [ht]
            rcases abs_choice (w y₀) with h | h <;> rw [h]
            · exact hwe
            · exact hwe.neg
          obtain ⟨k, hk⟩ := hteven
          have h1 : (4 : ℤ) ∣ ∑ y ∈ F, (w y + t) := by
            apply Finset.dvd_sum
            intro y hy
            rcases abs_eq (by positivity : (0 : ℤ) ≤ t) |>.mp (habs y hy) with h | h
            · rw [h, hk]; exact ⟨k, by ring⟩
            · rw [h]; simp
          have h2 : (4 : ℤ) ∣ (F.card : ℤ) * t := by
            obtain ⟨r, hr⟩ := hm₁e
            rw [hFcard, hr, hk]
            exact ⟨r * k, by push_cast; ring⟩
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
          exact (Int.dvd_add_right h2).mp (by rwa [add_comm] at h1)
        · rw [Finset.not_nonempty_iff_eq_empty] at hFne
          rw [hFne, Finset.sum_empty]
          exact dvd_zero _
  -- the row identity: `2(q−1) − λ² ≡ 2 (mod 4)` for even `q`, even `λ`
  rw [hrow z₀ hz₀c] at hdvd
  have hs : bipartiteSignVector G c col z₀ = 1 ∨ bipartiteSignVector G c col z₀ = -1 := by
    unfold bipartiteSignVector
    rw [if_pos hz₀']
    cases col z₀ <;> simp
  have hlam_even : Even lam := by
    obtain ⟨k, hk⟩ := hlam_par
    obtain ⟨r, hr⟩ := hmeven
    exact ⟨k - r, by push_cast at hk; omega⟩
  obtain ⟨k, hk⟩ := hlam_even
  obtain ⟨r, hr⟩ := hqeven
  have hsq : lam * lam = 4 * (k * k) := by rw [hk]; ring
  rw [hsq, hr] at hdvd
  obtain ⟨a, ha⟩ := hdvd
  push_cast at ha
  rcases hs with hs | hs <;> rw [hs] at ha <;> omega

/-! ### Order 64 (`q = 8`) -/

/-- `14` is not a perfect square. -/
theorem fourteen_not_square (t : ℤ) : t * t ≠ 14 := by
  intro h
  have h1 : t ≤ 3 ∨ 4 ≤ t := by omega
  have h2 : -3 ≤ t ∨ t ≤ -4 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> nlinarith [h]

/-- At order 64, a defect component all of whose fellow components have order
`16` is not bipartite.  Covers `[8]`, the size-six part of `[6,2]`, the
size-four part of `[4,2,2]`, and `[2,2,2,2]`. -/
theorem orderSixtyFour_bipartite_false_of_others_sizeTwo
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = 8 * m)
    (hothers : ∀ c₁ : (secondOrderDefectGraph G).ConnectedComponent, c₁ ≠ c →
      c₁.supp.ncard = 8 * 2)
    (col : Fin 64 → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by simp
  apply binarySquare_regular_bipartite_defectComponent_false_of_others_not_bipartite
    G hfree (q := 8) (by norm_num) hreg hcard
    (fun t => by have := fourteen_not_square t; norm_num; exact this) c hc col hbip
  intro c₁ hc₁ col₁ hcol₁
  -- `c₁` is a size-two component; the size-two exclusion applies since no
  -- component has order exactly `8`
  apply binarySquare_regular_sizeTwoPart_bipartite_false G hfree (q := 8) (by norm_num)
    hreg hcard c₁ (hothers c₁ hc₁) _ col₁ hcol₁
  intro c₂ hc₂ h8
  by_cases hc₂c : c₂ = c
  · subst hc₂c
    -- `c` has order `8 m`; `8 m = 8` forces `m = 1`, but then `c` is a size-one
    -- part, excluded because its own fellows all have order 16 and the total is 64
    rw [hc] at h8
    have hm : m = 1 := by omega
    -- count: `8 + 16 k = 64` has no solution
    have hsum := sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
    have htot : (∑ c' : (secondOrderDefectGraph G).ConnectedComponent, c'.supp.ncard) = 64 := by
      simpa [Nat.card_eq_fintype_card] using hsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c₂)] at htot
    have hrest : ∀ c' ∈ Finset.univ.erase c₂, c'.supp.ncard = 16 := by
      intro c' hc'
      exact hothers c' (Finset.ne_of_mem_erase hc')
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, smul_eq_mul, hc, hm] at htot
    omega
  · rw [hothers c₂ hc₂c] at h8
    omega

/-- At order 64, a bipartite defect component of odd size `m` together with a
size-two fellow component (in a stratum without size-one parts) is impossible.
Covers the size-three parts of `[3,3,2]`. -/
theorem orderSixtyFour_odd_bipartite_false_of_exists_sizeTwo
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = 8 * m) (hodd : Odd m)
    (c₂ : (secondOrderDefectGraph G).ConnectedComponent) (hc₂ : c₂ ≠ c)
    (hc₂size : c₂.supp.ncard = 8 * 2)
    (hno1 : ∀ c₃ : (secondOrderDefectGraph G).ConnectedComponent, c₃ ≠ c₂ →
      c₃.supp.ncard ≠ 8)
    (col : Fin 64 → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by simp
  obtain ⟨col₂, hcol₂⟩ :=
    binarySquare_regular_bipartite_defectComponent_odd_forces_others_bipartite
      G hfree (q := 8) (by norm_num) hreg hcard c hc hodd col hbip c₂ hc₂
  exact binarySquare_regular_sizeTwoPart_bipartite_false G hfree (q := 8) (by norm_num)
    hreg hcard c₂ hc₂size hno1 col₂ hcol₂

/-- `[4,4]`: at order 64, a bipartite defect component of order 32 whose
complement is a single component (necessarily of order 32) is impossible. -/
theorem orderSixtyFour_fourFour_not_bipartite
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) (hcc' : c' ≠ c)
    (hc : c.supp.ncard = 8 * 4) (hc' : c'.supp.ncard = 8 * 4)
    (hcompl : ∀ x, x ∉ c.supp → x ∈ c'.supp)
    (col : Fin 64 → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by simp
  obtain ⟨lam, w, hlam_par, hlam_abs, -, hw_in, -, hw_par, halt, hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree (q := 8) (by norm_num) hreg hcard c hc col hbip
  -- base vertex of `c`
  obtain ⟨z₀, hz₀⟩ := c.exists_rep
  have hz₀' : (secondOrderDefectGraph G).connectedComponentMk z₀ = c := hz₀
  have hz₀c : z₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c z₀).mpr hz₀'
  -- the four outside neighbours of `z₀` all lie in `c'`
  have hnotc : ∀ u, u ∈ c'.supp → u ∉ c.supp := by
    intro u hu huc
    exact hcc' (((ConnectedComponent.mem_supp_iff c' u).mp hu).symm.trans
      ((ConnectedComponent.mem_supp_iff c u).mp huc))
  have halt' : ∀ u v, u ∈ c'.supp → (secondOrderDefectGraph G).Adj u v → w v = -w u :=
    fun u v hu huv => halt u v (hnotc u hu) huv
  set T := (G.neighborFinset z₀).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c') with hT
  have hTcard : T.card = 4 := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg hcard c c' (x := z₀) hz₀c
    rw [hc'] at h
    change 8 * T.card = 8 * 4 at h
    omega
  have hrowT : ∑ y ∈ T, w y = (2 * (((8 : ℕ) : ℤ) - 1) - lam * lam) * bipartiteSignVector G c col z₀ := by
    rw [← hrow z₀ hz₀c]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z₀)
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c')]
    have hzero : ∑ y ∈ (G.neighborFinset z₀).filter
        (fun y => ¬ (secondOrderDefectGraph G).connectedComponentMk y = c'), w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      apply hw_in y
      by_contra hyc
      exact hy' ((ConnectedComponent.mem_supp_iff c' y).mp (hcompl y hyc))
    rw [hzero, add_zero]
  -- all `w y`, `y ∈ T`, are even with a common absolute value `t`
  have hTc' : ∀ y ∈ T, y ∈ c'.supp := fun y hy =>
    (ConnectedComponent.mem_supp_iff c' y).mpr (Finset.mem_filter.mp hy).2
  have hTpos : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]; norm_num
  obtain ⟨y₀, hy₀⟩ := hTpos
  set t := |w y₀| with ht
  have habs : ∀ y ∈ T, |w y| = t := fun y hy =>
    (abs_eq_on_component_of_alternating (secondOrderDefectGraph G) c' w halt'
      y y₀ (hTc' y hy) (hTc' y₀ hy₀))
  have hteven : Even t := by
    have := (hw_par y₀ (hnotc y₀ (hTc' y₀ hy₀))).1
    -- `w y₀ + 4` even ⇒ `w y₀` even ⇒ `|w y₀|` even
    have hwe : Even (w y₀) := by
      obtain ⟨k, hk⟩ := this
      exact ⟨k - 2, by push_cast at hk; omega⟩
    rw [ht]
    rcases abs_choice (w y₀) with h | h <;> rw [h]
    · exact hwe
    · exact hwe.neg
  -- `Σ_T w ≡ 0 (mod 4)`: each term is `±t` with `t` even
  have hdvd : (4 : ℤ) ∣ ∑ y ∈ T, (w y + t) := by
    apply Finset.dvd_sum
    intro y hy
    obtain ⟨k, hk⟩ := hteven
    rcases abs_eq (by positivity : (0 : ℤ) ≤ t) |>.mp (habs y hy) with h | h
    · rw [h, hk]; exact ⟨k, by ring⟩
    · rw [h]; simp
  rw [Finset.sum_add_distrib, Finset.sum_const, hTcard, nsmul_eq_mul, hrowT] at hdvd
  -- `λ` is even, so `λ² ≡ 0 (mod 4)`, whereas `14 − λ²` must be `≡ 0 (mod 4)`
  have hlam_even : Even lam := by
    obtain ⟨k, hk⟩ := hlam_par
    exact ⟨k - 2, by push_cast at hk; omega⟩
  obtain ⟨k, hk⟩ := hlam_even
  have hs : bipartiteSignVector G c col z₀ = 1 ∨ bipartiteSignVector G c col z₀ = -1 := by
    unfold bipartiteSignVector
    rw [if_pos hz₀']
    cases col z₀ <;> simp
  have hsq : lam * lam = 4 * (k * k) := by rw [hk]; ring
  rw [hsq] at hdvd
  obtain ⟨a, ha⟩ := hdvd
  rcases hs with hs | hs <;> rw [hs] at ha <;> omega

/-- `[5,3]`: at order 64, a bipartite defect component of order 24 whose
complement is a single component (of order 40) is impossible. -/
theorem orderSixtyFour_fiveThree_sizeThree_not_bipartite
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) (hcc' : c' ≠ c)
    (hc : c.supp.ncard = 8 * 3) (hc' : c'.supp.ncard = 8 * 5)
    (hcompl : ∀ x, x ∉ c.supp → x ∈ c'.supp)
    (col : Fin 64 → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by simp
  obtain ⟨lam, w, hlam_par, hlam_abs, -, hw_in, hw_out, hw_par, halt, hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree (q := 8) (by norm_num) hreg hcard c hc col hbip
  have hnotc : ∀ u, u ∈ c'.supp → u ∉ c.supp := by
    intro u hu huc
    exact hcc' (((ConnectedComponent.mem_supp_iff c' u).mp hu).symm.trans
      ((ConnectedComponent.mem_supp_iff c u).mp huc))
  have halt' : ∀ u v, u ∈ c'.supp → (secondOrderDefectGraph G).Adj u v → w v = -w u :=
    fun u v hu huv => halt u v (hnotc u hu) huv
  have hmem : ∀ x, x ∈ c.supp ↔ (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  -- signed indicator facts
  have hs_val : ∀ z ∈ c.supp, bipartiteSignVector G c col z = 1 ∨
      bipartiteSignVector G c col z = -1 := by
    intro z hz
    unfold bipartiteSignVector
    rw [if_pos ((hmem z).mp hz)]
    cases col z <;> simp
  have hs_out : ∀ z, z ∉ c.supp → bipartiteSignVector G c col z = 0 := by
    intro z hz
    unfold bipartiteSignVector
    rw [if_neg (fun h => hz ((hmem z).mpr h))]
  -- outside neighbourhoods of vertices of `c`: five vertices, all in `c'`
  have hext : ∀ z ∈ c.supp,
      ((G.neighborFinset z).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c')).card = 5 := by
    intro z hz
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg hcard c c' (x := z) hz
    rw [hc'] at h
    change 8 * ((G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c')).card = 8 * 5 at h
    omega
  have hrowT : ∀ z ∈ c.supp,
      ∑ y ∈ (G.neighborFinset z).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'), w y =
      (2 * (((8 : ℕ) : ℤ) - 1) - lam * lam) * bipartiteSignVector G c col z := by
    intro z hz
    rw [← hrow z hz]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z)
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c')]
    have hzero : ∑ y ∈ (G.neighborFinset z).filter
        (fun y => ¬ (secondOrderDefectGraph G).connectedComponentMk y = c'), w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      apply hw_in y
      by_contra hyc
      exact hy' ((ConnectedComponent.mem_supp_iff c' y).mp (hcompl y hyc))
    rw [hzero, add_zero]
  -- `|w|` is a constant `t ∈ {1, 3}` on `c'`; `λ ∈ {±1, ±3}`
  obtain ⟨y₀, hy₀⟩ := c'.exists_rep
  have hy₀' : (secondOrderDefectGraph G).connectedComponentMk y₀ = c' := hy₀
  have hy₀c' : y₀ ∈ c'.supp := (ConnectedComponent.mem_supp_iff c' y₀).mpr hy₀'
  set t := |w y₀| with ht
  have habs : ∀ y ∈ c'.supp, |w y| = t := fun y hy =>
    abs_eq_on_component_of_alternating (secondOrderDefectGraph G) c' w halt' y y₀ hy hy₀c'
  have ht_odd : Odd t := by
    have := (hw_par y₀ (hnotc y₀ hy₀c')).1
    have hwo : Odd (w y₀) := by
      obtain ⟨k, hk⟩ := this
      exact ⟨k - 2, by push_cast at hk; omega⟩
    rw [ht]
    rcases abs_choice (w y₀) with h | h <;> rw [h]
    · exact hwo
    · exact hwo.neg
  have ht_le : t ≤ 3 := by
    rw [ht]; exact (hw_par y₀ (hnotc y₀ hy₀c')).2
  have ht_nonneg : 0 ≤ t := by rw [ht]; exact abs_nonneg _
  have hlam_odd : Odd lam := by
    obtain ⟨k, hk⟩ := hlam_par
    exact ⟨k - 2, by push_cast at hk; omega⟩
  have hlam_sq : lam * lam = 1 ∨ lam * lam = 9 := by
    obtain ⟨k, hk⟩ := hlam_odd
    have h3 : |lam| ≤ 3 := by exact_mod_cast hlam_abs
    have h1 : lam ≤ 3 := (abs_le.mp h3).2
    have h2 : -3 ≤ lam := (abs_le.mp h3).1
    have : lam = -3 ∨ lam = -1 ∨ lam = 1 ∨ lam = 3 := by omega
    rcases this with h | h | h | h <;> rw [h] <;> norm_num
  -- `t = 3` is impossible: `3 ∣ Σ_T w = ±(14 − λ²) ∈ {±13, ±5}`
  have ht_one : t = 1 := by
    have : t = 1 ∨ t = 3 := by
      obtain ⟨k, hk⟩ := ht_odd
      omega
    rcases this with h | h
    · exact h
    · exfalso
      obtain ⟨z₀, hz₀⟩ := c.exists_rep
      have hz₀c : z₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c z₀).mpr hz₀
      have hdvd : (3 : ℤ) ∣ ∑ y ∈ (G.neighborFinset z₀).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'), w y := by
        apply Finset.dvd_sum
        intro y hy
        have hyc' : y ∈ c'.supp :=
          (ConnectedComponent.mem_supp_iff c' y).mpr (Finset.mem_filter.mp hy).2
        have := habs y hyc'
        rw [h] at this
        rcases abs_eq (by norm_num : (0:ℤ) ≤ 3) |>.mp this with h' | h' <;> rw [h'] <;> norm_num
      rw [hrowT z₀ hz₀c] at hdvd
      obtain ⟨a, ha⟩ := hdvd
      rcases hs_val z₀ hz₀c with hs | hs <;> rw [hs] at ha <;>
        rcases hlam_sq with hl | hl <;> rw [hl] at ha <;> omega
  -- with `t = 1`: every outside neighbour `y` of `z ∈ c` has `w y = s z`
  have hlam9 : lam * lam = 9 := by
    -- from the row identity with `|w| = 1` on five terms: `|14 − λ²| ≤ 5`
    obtain ⟨z₀, hz₀⟩ := c.exists_rep
    have hz₀c : z₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c z₀).mpr hz₀
    have hle : |∑ y ∈ (G.neighborFinset z₀).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'), w y| ≤ 5 := by
      calc
        _ ≤ ∑ y ∈ (G.neighborFinset z₀).filter
              (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'), |w y| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = 5 := by
            rw [Finset.sum_congr rfl (fun y hy => by
              rw [habs y ((ConnectedComponent.mem_supp_iff c' y).mpr
                (Finset.mem_filter.mp hy).2), ht_one])]
            rw [Finset.sum_const, hext z₀ hz₀c]; simp
    rw [hrowT z₀ hz₀c] at hle
    rcases hs_val z₀ hz₀c with hs | hs <;> rw [hs] at hle <;>
      rcases hlam_sq with hl | hl <;> rw [hl] at hle <;> norm_num at hle <;> omega
  have hforce : ∀ z ∈ c.supp, ∀ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'),
      w y = bipartiteSignVector G c col z := by
    intro z hz
    have hsum := hrowT z hz
    rw [hlam9] at hsum
    -- `Σ_T (s z * w y) = 5` with each term `≤ 1` and five terms ⇒ each term `= 1`
    have hprod : ∀ y ∈ (G.neighborFinset z).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'),
        bipartiteSignVector G c col z * w y ≤ 1 := by
      intro y hy
      have hy1 : |w y| = 1 := by
        rw [habs y ((ConnectedComponent.mem_supp_iff c' y).mpr (Finset.mem_filter.mp hy).2)]
        exact ht_one
      rcases hs_val z hz with hs | hs <;> rcases abs_eq (by norm_num : (0:ℤ) ≤ 1) |>.mp hy1
        with h | h <;> rw [hs, h] <;> norm_num
    have hnonneg : ∀ y ∈ (G.neighborFinset z).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'),
        0 ≤ 1 - bipartiteSignVector G c col z * w y := fun y hy => by linarith [hprod y hy]
    have hsum' : ∑ y ∈ (G.neighborFinset z).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c'),
        (1 - bipartiteSignVector G c col z * w y) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, hext z hz]
      rcases hs_val z hz with hs | hs <;> rw [hs] <;> norm_num
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum'
    intro y hy
    have := hall y hy
    rcases hs_val z hz with hs | hs <;> rw [hs] at this ⊢ <;> linarith
  -- pick a vertex `z₀ ∈ c` and an outside neighbour `y₀`; `w y₀ = s z₀`
  obtain ⟨z₀, hz₀⟩ := c.exists_rep
  have hz₀c : z₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c z₀).mpr hz₀
  have hTne : ((G.neighborFinset z₀).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c')).Nonempty := by
    rw [← Finset.card_pos, hext z₀ hz₀c]; norm_num
  obtain ⟨y₁, hy₁⟩ := hTne
  have hy₁c' : y₁ ∈ c'.supp :=
    (ConnectedComponent.mem_supp_iff c' y₁).mpr (Finset.mem_filter.mp hy₁).2
  have hy₁c : y₁ ∉ c.supp := hnotc y₁ hy₁c'
  have hwy₁ : w y₁ = bipartiteSignVector G c col z₀ := hforce z₀ hz₀c y₁ hy₁
  -- `w y₁ = Σ_{u ∈ N(y₁)} s u` is a sum of three signs equal to `s z₀`, so some
  -- neighbour `u ∈ c` of `y₁` has `s u = −s z₀`
  have hw_eq : w y₁ = ∑ u ∈ G.neighborFinset y₁, bipartiteSignVector G c col u :=
    hw_out y₁ hy₁c
  have hexists : ∃ u ∈ G.neighborFinset y₁, u ∈ c.supp ∧
      bipartiteSignVector G c col u = - bipartiteSignVector G c col z₀ := by
    by_contra hnone
    push Not at hnone
    -- then every neighbour `u ∈ c` of `y₁` has `s u = s z₀`, so the sum is `3 s z₀`
    have h3 : ((G.neighborFinset y₁).filter
        (fun u => (secondOrderDefectGraph G).connectedComponentMk u = c)).card = 3 := by
      have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
        G hfree (q := 8) (by norm_num) hreg hcard
        ((secondOrderDefectGraph G).connectedComponentMk y₁) c (x := y₁)
        ((ConnectedComponent.mem_supp_iff _ y₁).mpr rfl)
      rw [hc] at h
      change 8 * ((G.neighborFinset y₁).filter
        (fun u => (secondOrderDefectGraph G).connectedComponentMk u = c)).card = 8 * 3 at h
      omega
    have hsplit : ∑ u ∈ G.neighborFinset y₁, bipartiteSignVector G c col u =
        ∑ u ∈ (G.neighborFinset y₁).filter
          (fun u => (secondOrderDefectGraph G).connectedComponentMk u = c),
          bipartiteSignVector G c col u := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : (secondOrderDefectGraph G).connectedComponentMk u = c
      · simp [hu]
      · rw [if_neg hu, hs_out u (fun h => hu ((hmem u).mp h))]
    have hall : ∀ u ∈ (G.neighborFinset y₁).filter
        (fun u => (secondOrderDefectGraph G).connectedComponentMk u = c),
        bipartiteSignVector G c col u = bipartiteSignVector G c col z₀ := by
      intro u hu
      have huN := (Finset.mem_filter.mp hu).1
      have huc : u ∈ c.supp := (hmem u).mpr (Finset.mem_filter.mp hu).2
      have hne := hnone u huN huc
      rcases hs_val u huc with h | h <;> rcases hs_val z₀ hz₀c with h' | h' <;>
        simp only [h, h'] at hne ⊢ <;> norm_num at hne
    rw [hw_eq, hsplit, Finset.sum_congr rfl hall, Finset.sum_const, h3, nsmul_eq_mul] at hwy₁
    rcases hs_val z₀ hz₀c with h | h <;> rw [h] at hwy₁ <;> norm_num at hwy₁
  obtain ⟨u, huN, huc, hsu⟩ := hexists
  -- `y₁` is an outside neighbour of `u`, so `w y₁ = s u = −s z₀`: contradiction
  have hy₁u : y₁ ∈ (G.neighborFinset u).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c') := by
    rw [Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset u y₁).mpr ((G.mem_neighborFinset y₁ u).mp huN).symm,
      (ConnectedComponent.mem_supp_iff c' y₁).mp hy₁c'⟩
  have := hforce u huc y₁ hy₁u
  rw [hsu, hwy₁] at this
  rcases hs_val z₀ hz₀c with h | h <;> rw [h] at this <;> norm_num at this

end

end Erdos85
