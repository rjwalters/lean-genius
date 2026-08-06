import Proofs.Erdos85UnequalBlockFiberParity
import Proofs.Erdos85EqualBlockFiberParity

/-!
# Global parity of mixed complement fibers
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- An ordered off-diagonal sum is even whenever each unordered pair has
even combined weight. -/
theorem even_sum_erase_of_pair_even
    {C : Type*} [DecidableEq C] (S : Finset C) (F : C → C → ℕ)
    (hpair : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Even (F c e + F e c)) :
    Even (∑ c ∈ S, ∑ e ∈ S.erase c, F c e) := by
  let Q : C → C → ℕ := fun c e ↦ if c = e then 0 else F c e
  have hprincipal : Even (∑ c ∈ S, ∑ e ∈ S, Q c e) := by
    apply even_principal_sum_of_pair_even S Q
    · intro c hc
      simp [Q]
    · intro c hc e he hce
      simpa [Q, hce, hce.symm] using hpair c hc e he hce
  have heq : (∑ c ∈ S, ∑ e ∈ S, Q c e) =
      ∑ c ∈ S, ∑ e ∈ S.erase c, F c e := by
    apply Finset.sum_congr rfl
    intro c hc
    calc
      ∑ e ∈ S, Q c e = (∑ e ∈ S.erase c, Q c e) + Q c c :=
        (Finset.sum_erase_add _ _ hc).symm
      _ = ∑ e ∈ S.erase c, F c e := by
        simp only [Q, if_pos, add_zero]
        apply Finset.sum_congr rfl
        intro e he
        simp [(Finset.mem_erase.mp he).1.symm]
  rw [heq] at hprincipal
  exact hprincipal

/-- Two equal-length off-diagonal blocks contribute an even total in every
projection fiber. -/
theorem even_equalBlock_pair_fullMass_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d n p : ℕ} [NeZero n] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hn3 : 3 ≤ n) (hnOdd : Odd n) (hpn : p ∣ n)
    (u v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ x, (secondOrderDefectGraph G).neighborFinset (v x) =
      {v (x - 1), v (x + 1)})
    (t : ZMod p) :
    Even (((admissibleDifferences n).filter (fun δ ↦
        ZMod.castHom hpn (ZMod p) δ = t ∧
          (∑ x : ZMod n, anchorPairMultiplicity G (u x) v δ) = n)).card +
      ((admissibleDifferences n).filter (fun δ ↦
        ZMod.castHom hpn (ZMod p) δ = t ∧
          (∑ x : ZMod n, anchorPairMultiplicity G (v x) u δ) = n)).card) := by
  let w : Bool → ZMod n → V := fun b ↦ if b then v else u
  have hw : ∀ b, Function.Injective (w b) := by
    intro b
    cases b <;> simp [w, hu, hv]
  have hwD : ∀ b x, (secondOrderDefectGraph G).neighborFinset (w b x) =
      {w b (x - 1), w b (x + 1)} := by
    intro b x
    cases b
    · change (secondOrderDefectGraph G).neighborFinset (u x) =
        {u (x - 1), u (x + 1)}
      exact huD x
    · change (secondOrderDefectGraph G).neighborFinset (v x) =
        {v (x - 1), v (x + 1)}
      exact hvD x
  have h := even_sum_equalBlock_fullMass_fiber G hfree hd heven hmin hcard
    hn3 hnOdd hpn w hw hwD Finset.univ t
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  have heraseF : ({false, true} : Finset Bool).erase false = {true} := by decide
  have heraseT : ({false, true} : Finset Bool).erase true = {false} := by decide
  simp [huniv, heraseF, heraseT, w] at h
  simpa [add_comm] using h

/-- Heterogeneously indexed wrapper for the preceding theorem.  Keeping the
two lengths as explicit variables lets Lean eliminate their equality before
they are instantiated by dependent component-cardinality expressions. -/
theorem even_equalLength_pair_fullMass_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r n p : ℕ}
    [NeZero r] [NeZero n] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r) (hpr : p ∣ r)
    (hrn : r = n) (u : ZMod r → V) (v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ x, (secondOrderDefectGraph G).neighborFinset (v x) =
      {v (x - 1), v (x + 1)})
    (t : ZMod p) :
    Even (((admissibleDifferences n).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t ∧
          (∑ x : ZMod r, anchorPairMultiplicity G (u x) v δ) = n)).card +
      ((admissibleDifferences r).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t ∧
          (∑ x : ZMod n, anchorPairMultiplicity G (v x) u δ) = r)).card) := by
  cases hrn
  have h := even_equalBlock_pair_fullMass_fibers G hfree hd heven hmin
    hcard hr3 hrOdd hpr u v hu hv huD hvD t
  simpa [zmod_castHom_eq_val_cast hpr] using h

/-- The total full-mass contribution between selected components is even:
equal-length pairs cancel by transpose symmetry, while unequal pairs are
individually even. -/
theorem even_selectedComponent_fullMass_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero a.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p)
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
    (t : ZMod p) :
    Even (∑ e ∈ Finset.univ.filter (fun e :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ e.supp.ncard),
      ∑ c ∈ (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard)).erase e,
        ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t ∧
            (∑ z : ZMod c.supp.ncard,
              anchorPairMultiplicity G (u c z) (u e) δ) =
                e.supp.ncard)).card) := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let S : Finset C := Finset.univ.filter (fun c ↦ p ∣ c.supp.ncard)
  let F : C → C → ℕ := fun e c ↦
    ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard)).card
  change Even (∑ e ∈ S, ∑ c ∈ S.erase e, F e c)
  apply even_sum_erase_of_pair_even S F
  intro e he c hc hec
  have hpe : p ∣ e.supp.ncard := by simpa [S] using he
  have hpc : p ∣ c.supp.ncard := by simpa [S] using hc
  by_cases hlen : e.supp.ncard = c.supp.ncard
  · exact even_equalLength_pair_fullMass_fibers G hfree hd heven hmin
      hcard (hℓ3 c) (hodd c hpc) hpc hlen.symm (u c) (u e) (hu c)
        (hu e) (huD c) (huD e) t
  · have hevenEC := even_unequal_selected_fullMass_fiber G hfree hd
      heven hmin hcard hp u hu huRange huD hℓ3 hodd c e
        (fun h ↦ hlen h.symm) hpc hpe t
    have hevenCE := even_unequal_selected_fullMass_fiber G hfree hd
      heven hmin hcard hp u hu huRange huD hℓ3 hodd e c hlen hpe hpc t
    exact hevenEC.add hevenCE

/-- Positivity of the component quotient is symmetric, by detailed balance
and positivity of component orders. -/
theorem secondOrder_componentQuotientMatrix_pos_iff_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    0 < componentQuotientMatrix G (secondOrderDefectGraph G) c e ↔
      0 < componentQuotientMatrix G (secondOrderDefectGraph G) e c := by
  have hb := secondOrder_componentQuotientMatrix_balance G hfree hd heven
    hmin hcard c e
  change c.supp.ncard * componentQuotientMatrix G (secondOrderDefectGraph G) c e =
    e.supp.ncard * componentQuotientMatrix G (secondOrderDefectGraph G) e c at hb
  constructor
  · intro hpos
    by_contra hnpos
    have hz : componentQuotientMatrix G (secondOrderDefectGraph G) e c = 0 :=
      Nat.eq_zero_of_not_pos hnpos
    rw [hz, mul_zero] at hb
    exact (Nat.ne_of_gt (Nat.mul_pos c.nonempty_supp.ncard_pos hpos)) hb
  · intro hpos
    by_contra hnpos
    have hz : componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 :=
      Nat.eq_zero_of_not_pos hnpos
    rw [hz, mul_zero] at hb
    exact (Nat.ne_of_gt (Nat.mul_pos e.nonempty_supp.ncard_pos hpos)) hb.symm

/-- The total full-mass contribution from nonselected sources into selected
targets is even.  At residue zero every block is even; away from zero, its
parity is exactly positivity of the corresponding quotient block, and the
positive prime-divisibility cut has even cardinality. -/
theorem even_residualComponent_fullMass_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero a.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p)
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
    (t : ZMod p) :
    Even (∑ e ∈ Finset.univ.filter (fun e :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ e.supp.ncard),
      ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦ ¬p ∣ c.supp.ncard),
        ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t ∧
            (∑ z : ZMod c.supp.ncard,
              anchorPairMultiplicity G (u c z) (u e) δ) =
                e.supp.ncard)).card) := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let S : Finset C := Finset.univ.filter (fun e ↦ p ∣ e.supp.ncard)
  let T : Finset C := Finset.univ.filter (fun c ↦ ¬p ∣ c.supp.ncard)
  let F : C × C → ℕ := fun q ↦
    ((admissibleDifferences q.1.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod q.2.supp.ncard,
          anchorPairMultiplicity G (u q.2 z) (u q.1) δ) =
            q.1.supp.ncard)).card
  change Even (∑ e ∈ S, ∑ c ∈ T, F (e, c))
  rw [← Finset.sum_product]
  by_cases ht : t = 0
  · subst t
    apply Finset.even_sum
    intro q hq
    have hmem := Finset.mem_product.mp hq
    have hpe : p ∣ q.1.supp.ncard := by simpa [S] using hmem.1
    have hpc : ¬p ∣ q.2.supp.ncard := by simpa [T] using hmem.2
    have hlen : q.2.supp.ncard ≠ q.1.supp.ncard := by
      intro h
      exact hpc (h ▸ hpe)
    exact even_unequal_fullMass_zeroFiber G hfree hd heven hmin hcard hp
      u hu huRange huD hℓ3 hodd q.2 q.1 hlen hpe
  · have hfilter : (S ×ˢ T).filter (fun q ↦ Odd (F q)) =
        (S ×ˢ T).filter (fun q ↦ 0 < componentQuotientMatrix G
          (secondOrderDefectGraph G) q.1 q.2) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq, hF⟩
        refine ⟨hq, ?_⟩
        have hmem := Finset.mem_product.mp hq
        have hpe : p ∣ q.1.supp.ncard := by simpa [S] using hmem.1
        have hpc : ¬p ∣ q.2.supp.ncard := by simpa [T] using hmem.2
        have hlen : q.2.supp.ncard ≠ q.1.supp.ncard := by
          intro h
          exact hpc (h ▸ hpe)
        have hsource := (odd_unequal_residual_fullMass_fiber_iff_quotient_pos G
          hfree hd heven hmin hcard hp u hu huRange huD hℓ3 hodd q.2 q.1
            hlen hpc hpe t ht).mp hF
        exact (secondOrder_componentQuotientMatrix_pos_iff_transpose G
          hfree hd heven hmin hcard q.2 q.1).mp hsource
      · rintro ⟨hq, hpos⟩
        refine ⟨hq, ?_⟩
        have hmem := Finset.mem_product.mp hq
        have hpe : p ∣ q.1.supp.ncard := by simpa [S] using hmem.1
        have hpc : ¬p ∣ q.2.supp.ncard := by simpa [T] using hmem.2
        have hlen : q.2.supp.ncard ≠ q.1.supp.ncard := by
          intro h
          exact hpc (h ▸ hpe)
        have hsource := (secondOrder_componentQuotientMatrix_pos_iff_transpose G
          hfree hd heven hmin hcard q.2 q.1).mpr hpos
        exact (odd_unequal_residual_fullMass_fiber_iff_quotient_pos G
          hfree hd heven hmin hcard hp u hu huRange huD hℓ3 hodd q.2 q.1
            hlen hpc hpe t ht).mpr hsource
    rw [← Nat.not_odd_iff_even, Finset.odd_sum_iff_odd_card_odd, hfilter]
    exact Nat.not_odd_iff_even.mpr (by
      simpa [S, T] using
        (secondOrder_pDivisible_positive_cut_card_even G hfree hd heven
          hmin hcard hodd))

/-- **Global mixed-complement parity.** For every residue, the aggregate
complement fiber over the odd `p`-divisible defect components is even. -/
theorem even_sum_mixedComplementFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ a : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero a.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ} [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : Nat.Prime p)
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
    (t : ZMod p) :
    Even (∑ e ∈ Finset.univ.filter (fun e :
        (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ e.supp.ncard),
      ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
        ((δ.val : ℕ) : ZMod p) = t ∧
          δ ∉ orderedDifferenceSet
            (mixedAnchorSupport G (u e 0) (u e)))).card) := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let S : Finset C := Finset.univ.filter (fun e ↦ p ∣ e.supp.ncard)
  let T : Finset C := Finset.univ.filter (fun c ↦ ¬p ∣ c.supp.ncard)
  let F : C → C → ℕ := fun e c ↦
    ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
      ((δ.val : ℕ) : ZMod p) = t ∧
        (∑ z : ZMod c.supp.ncard,
          anchorPairMultiplicity G (u c z) (u e) δ) = e.supp.ncard)).card
  have hcomponents :
      (∑ e ∈ S,
        ((admissibleDifferences e.supp.ncard).filter (fun δ ↦
          ((δ.val : ℕ) : ZMod p) = t ∧
            δ ∉ orderedDifferenceSet
              (mixedAnchorSupport G (u e 0) (u e)))).card) =
        ∑ e ∈ S, ∑ c ∈ Finset.univ.erase e, F e c := by
    apply Finset.sum_congr rfl
    intro e he
    have hpe : p ∣ e.supp.ncard := by simpa [S] using he
    simpa [F] using
      (card_mixedComplementFiber_eq_sum_component_fullMass_fibers G hfree
        hd heven hmin hcard u hu huRange huD hℓ3 e (hodd e hpe) t)
  have hsplit : (∑ e ∈ S, ∑ c ∈ Finset.univ.erase e, F e c) =
      (∑ e ∈ S, ∑ c ∈ S.erase e, F e c) +
        (∑ e ∈ S, ∑ c ∈ T, F e c) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    have heP : p ∣ e.supp.ncard := by simpa [S] using he
    have hdisj : Disjoint (S.erase e) T := by
      rw [Finset.disjoint_left]
      intro c hcS hcT
      have hpc : p ∣ c.supp.ncard := by simpa [S] using
        (Finset.mem_erase.mp hcS).2
      have hnpc : ¬p ∣ c.supp.ncard := by simpa [T] using hcT
      exact hnpc hpc
    calc
      ∑ c ∈ Finset.univ.erase e, F e c =
          ∑ c ∈ (S.erase e) ∪ T, F e c := by
        apply Finset.sum_congr
        · ext c
          simp only [S, T, Finset.mem_erase, Finset.mem_univ, true_and,
            Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hce
            by_cases hpc : p ∣ c.supp.ncard
            · exact Or.inl ⟨hce.1, hpc⟩
            · exact Or.inr hpc
          · rintro (⟨hce, _⟩ | hnpc)
            · exact ⟨hce, trivial⟩
            · refine ⟨?_, trivial⟩
              intro hce
              subst c
              exact hnpc heP
        · intro c hc
          rfl
      _ = (∑ c ∈ S.erase e, F e c) + ∑ c ∈ T, F e c :=
        Finset.sum_union hdisj
  rw [hcomponents, hsplit]
  exact (even_selectedComponent_fullMass_fibers G hfree hd heven hmin
    hcard hp u hu huRange huD hℓ3 hodd t).add
      (even_residualComponent_fullMass_fibers G hfree hd heven hmin hcard
        hp u hu huRange huD hℓ3 hodd t)

end

end Erdos85
