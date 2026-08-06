import Proofs.Erdos85OrientedMassBounds

/-!
# Classification of forward diagonal supports

A forward-oriented diagonal block is circulant with a symmetric loopless
connection set of size at most two.  Symmetry forces the support to be
empty, an inverse pair `{t, -t}` with `t ≠ -t`, or the *antipodal
singleton* `{r/2}` — and a cyclic group has at most one nonzero
involution, so the two-singleton configuration is impossible.  The
antipodal case forces the cycle length to be even.

Consequently the oriented anchor mass is congruent modulo two to the
number of selected components with diagonal quotient exactly one — all
of which have even length.  This reduces the aggregate antipodal-parity
question to counting antipodal components.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A nonzero solution of `x = -x` in `ZMod r` doubles to the modulus. -/
theorem val_add_self_eq_of_self_eq_neg {r : ℕ} [NeZero r] {x : ZMod r}
    (hx : x = -x) (hx0 : x ≠ 0) : x.val + x.val = r := by
  have hadd : x + x = 0 := eq_neg_iff_add_eq_zero.mp hx
  have hcast : ((x.val + x.val : ℕ) : ZMod r) = 0 := by
    push_cast
    rw [ZMod.natCast_rightInverse x]
    exact hadd
  have hdvd : r ∣ x.val + x.val := (ZMod.natCast_eq_zero_iff _ r).mp hcast
  have hxlt : x.val < r := ZMod.val_lt x
  have hxne : x.val ≠ 0 := fun h ↦
    hx0 (by rw [← ZMod.natCast_rightInverse x, h, Nat.cast_zero])
  rcases hdvd with ⟨k, hk⟩
  have hklt : r * k < r * 2 := by omega
  have hk2 : k < 2 := Nat.lt_of_mul_lt_mul_left hklt
  interval_cases k
  · omega
  · omega

/-- `ZMod r` has at most one nonzero involution. -/
theorem zmod_eq_of_self_eq_neg {r : ℕ} [NeZero r] {x y : ZMod r}
    (hx : x = -x) (hy : y = -y) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x = y := by
  have hxr := val_add_self_eq_of_self_eq_neg hx hx0
  have hyr := val_add_self_eq_of_self_eq_neg hy hy0
  have hval : x.val = y.val := by omega
  calc
    x = ((x.val : ℕ) : ZMod r) := (ZMod.natCast_rightInverse x).symm
    _ = ((y.val : ℕ) : ZMod r) := by rw [hval]
    _ = y := ZMod.natCast_rightInverse y

/-- A nonzero involution forces an even modulus. -/
theorem even_of_self_eq_neg {r : ℕ} [NeZero r] {x : ZMod r}
    (hx : x = -x) (hx0 : x ≠ 0) : Even r :=
  ⟨x.val, (val_add_self_eq_of_self_eq_neg hx hx0).symm⟩

/-- Membership in the diagonal zero-row support is adjacency to the
anchor. -/
theorem mem_graphCycleBlockZeroSupport_iff_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u w : ZMod r → V) (t : ZMod r) :
    t ∈ graphCycleBlockZeroSupport G u w ↔ G.Adj (u 0) (w t) := by
  rw [graphCycleBlockZeroSupport, mem_zeroRowSupport_iff]
  simp [SimpleGraph.adjMatrix_apply]

/-- The diagonal support of a forward-oriented block is symmetric. -/
theorem neg_mem_graphCycleBlockZeroSupport_of_forward
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u : ZMod r → V)
    (hfwd : ∀ x y : ZMod r,
      G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y))
    {t : ZMod r} (ht : t ∈ graphCycleBlockZeroSupport G u u) :
    -t ∈ graphCycleBlockZeroSupport G u u := by
  have htrans : ∀ x z : ZMod r,
      G.adjMatrix ℤ (u (x + 1)) (u (z + 1)) =
        G.adjMatrix ℤ (u x) (u z) := by
    intro x z
    simp only [SimpleGraph.adjMatrix_apply, hfwd x z]
  obtain ⟨A, hA⟩ :=
    exists_connectionSet_of_translationInvariantBlock G u u htrans
  rw [mem_graphCycleBlockZeroSupport_iff_adj] at ht ⊢
  have h2 : G.Adj (u t) (u 0) := ht.symm
  have h3 : (0 : ZMod r) - t ∈ A := (hA t 0).mp h2
  refine (hA 0 (-t)).mpr ?_
  simpa using h3

/-- No loops: zero is never in the diagonal support. -/
theorem zero_not_mem_graphCycleBlockZeroSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u : ZMod r → V) :
    (0 : ZMod r) ∉ graphCycleBlockZeroSupport G u u := by
  rw [mem_graphCycleBlockZeroSupport_iff_adj]
  exact G.irrefl

/-- **Classification of forward diagonal supports.**  A symmetric
loopless support of size at most two is empty, the antipodal singleton,
or an inverse pair. -/
theorem forward_support_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u : ZMod r → V)
    (hfwd : ∀ x y : ZMod r,
      G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y))
    (hcard : (graphCycleBlockZeroSupport G u u).card ≤ 2) :
    graphCycleBlockZeroSupport G u u = ∅ ∨
      (∃ t : ZMod r, t ≠ 0 ∧ t = -t ∧
        graphCycleBlockZeroSupport G u u = {t}) ∨
      (∃ t : ZMod r, t ≠ -t ∧
        graphCycleBlockZeroSupport G u u = {t, -t}) := by
  have hsymm := fun {t} ht ↦
    neg_mem_graphCycleBlockZeroSupport_of_forward G u hfwd (t := t) ht
  have h0 := zero_not_mem_graphCycleBlockZeroSupport G u
  rcases (by omega : (graphCycleBlockZeroSupport G u u).card = 0 ∨
      (graphCycleBlockZeroSupport G u u).card = 1 ∨
      (graphCycleBlockZeroSupport G u u).card = 2) with h | h | h
  · exact Or.inl (Finset.card_eq_zero.mp h)
  · obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h
    have htm : t ∈ graphCycleBlockZeroSupport G u u :=
      ht ▸ Finset.mem_singleton_self t
    have ht0 : t ≠ 0 := fun h0t ↦ h0 (h0t ▸ htm)
    have htneg : t = -t := by
      have hn := hsymm htm
      rw [ht, Finset.mem_singleton] at hn
      exact hn.symm
    exact Or.inr (Or.inl ⟨t, ht0, htneg, ht⟩)
  · obtain ⟨a, b, hab, hSab⟩ := Finset.card_eq_two.mp h
    have ha : a ∈ graphCycleBlockZeroSupport G u u := by
      rw [hSab]
      simp
    have hb : b ∈ graphCycleBlockZeroSupport G u u := by
      rw [hSab]
      simp
    have hna := hsymm ha
    rw [hSab, Finset.mem_insert, Finset.mem_singleton] at hna
    rcases hna with h1 | h1
    · have hnb := hsymm hb
      rw [hSab, Finset.mem_insert, Finset.mem_singleton] at hnb
      rcases hnb with h2 | h2
      · have hba : b = a := by
          rw [← neg_neg b, h2]
          exact h1
        exact absurd hba.symm hab
      · have ha0 : a ≠ 0 := fun h ↦ h0 (h ▸ ha)
        have hb0 : b ≠ 0 := fun h ↦ h0 (h ▸ hb)
        exact absurd
          (zmod_eq_of_self_eq_neg h1.symm h2.symm ha0 hb0) hab
    · refine Or.inr (Or.inr ⟨a, ?_, ?_⟩)
      · exact fun h ↦ hab (h.trans h1)
      · rw [hSab, ← h1]

/-- A singleton forward support is antipodal: the cycle length is even. -/
theorem even_of_forward_support_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u : ZMod r → V)
    (hfwd : ∀ x y : ZMod r,
      G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y))
    (hone : (graphCycleBlockZeroSupport G u u).card = 1) :
    Even r := by
  rcases forward_support_classification G u hfwd (by omega) with
    hempty | ⟨t, ht0, htneg, _⟩ | ⟨t, htneg, hpair⟩
  · rw [hempty] at hone
    simp at hone
  · exact even_of_self_eq_neg htneg ht0
  · rw [hpair, Finset.card_insert_of_notMem (by
      simpa using fun h ↦ htneg h), Finset.card_singleton] at hone
    omega

/-- **Oriented mass parity.**  The canonical oriented anchor mass is
congruent mod `2` to the number of selected forward components with
diagonal quotient exactly one — the antipodal components. -/
theorem orientedAnchorMass_forwardOriented_modTwo_eq_antipodal_card
    {V : Type*} [Fintype V] [DecidableEq V]
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
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    orientedAnchorMass G u (forwardOriented G u) p ≡
      ((Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard ∧ forwardOriented G u c)).filter
        (fun c ↦ componentQuotientMatrix G (secondOrderDefectGraph G)
          c c = 1)).card [MOD 2] := by
  classical
  rw [orientedAnchorMass_eq_sum_diagonalQuotient G hfree hd heven hmin
    hcard u hu huRange]
  have hle2 : ∀ c ∈ Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard ∧ forwardOriented G u c),
      componentQuotientMatrix G (secondOrderDefectGraph G) c c ≤ 2 :=
    fun c hc ↦ forwardComponent_diagonalQuotient_le_two G hfree hd heven
      hmin hcard c (u c) (hu c) (huRange c)
      (Finset.mem_filter.mp hc).2.2
  have hsum : (∑ c ∈ Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard ∧ forwardOriented G u c),
      componentQuotientMatrix G (secondOrderDefectGraph G) c c % 2) =
      ((Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard ∧ forwardOriented G u c)).filter
        (fun c ↦ componentQuotientMatrix G (secondOrderDefectGraph G)
          c c = 1)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro c hc
    have h2 := hle2 c hc
    rcases (by omega :
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 1 ∨
        componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2)
      with h | h | h <;> simp [h]
  unfold Nat.ModEq
  rw [Finset.sum_nat_mod, hsum]

/-- **Antipodal components are even.**  A selected forward component with
diagonal quotient one has even order. -/
theorem even_supp_ncard_of_forwardOriented_diagonalQuotient_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
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
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod c.supp.ncard → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (hfwd : ∀ x y : ZMod c.supp.ncard,
      G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y))
    (hone : componentQuotientMatrix G (secondOrderDefectGraph G) c c
      = 1) :
    Even c.supp.ncard := by
  have hbridge := card_graphCycleBlockZeroSupport_eq_componentQuotient
    G hfree hd heven hmin hcard c c u u hu huRange huRange
  exact even_of_forward_support_card_eq_one G u hfwd
    (by rw [hbridge, hone])

/-- Reverse-oriented diagonal supports avoid the doubling image: the
anti-diagonal normal form sends `B 0 (x+x)` to the loop `B x x`. -/
theorem add_self_not_mem_graphCycleBlockZeroSupport_of_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (u : ZMod r → V)
    (hrev : ∀ x y : ZMod r,
      G.Adj (u (x + 1)) (u (y - 1)) ↔ G.Adj (u x) (u y))
    (x : ZMod r) : x + x ∉ graphCycleBlockZeroSupport G u u := by
  have h := reverse_block_apply_eq_zero_row
    (Matrix.of fun a b : ZMod r ↦ G.adjMatrix ℤ (u a) (u b))
    (fun a b ↦ by
      simp only [Matrix.of_apply, SimpleGraph.adjMatrix_apply, hrev a b])
    x x
  simp only [Matrix.of_apply, SimpleGraph.adjMatrix_apply] at h
  rw [mem_graphCycleBlockZeroSupport_iff_adj]
  intro hadj
  rw [if_neg G.irrefl, if_pos hadj] at h
  exact one_ne_zero h.symm

/-- On an odd cycle, a reverse-oriented diagonal block is empty: doubling
is surjective. -/
theorem graphCycleBlockZeroSupport_eq_empty_of_reverse_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ} [NeZero r]
    (hrOdd : Odd r) (u : ZMod r → V)
    (hrev : ∀ x y : ZMod r,
      G.Adj (u (x + 1)) (u (y - 1)) ↔ G.Adj (u x) (u y)) :
    graphCycleBlockZeroSupport G u u = ∅ := by
  ext t
  simp only [Finset.notMem_empty, iff_false]
  have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hrOdd
  have hunit : IsUnit ((2 : ℕ) : ZMod r) :=
    (ZMod.isUnit_iff_coprime 2 r).mpr hcop
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hx : (w * t) + (w * t) = t := by
    have h2 : ((2 : ℕ) : ZMod r) * (w * t) = t := by
      rw [← mul_assoc, mul_comm ((2 : ℕ) : ZMod r) w, hw, one_mul]
    calc
      (w * t) + (w * t) = ((2 : ℕ) : ZMod r) * (w * t) := by
        push_cast
        ring
      _ = t := h2
  intro ht
  exact add_self_not_mem_graphCycleBlockZeroSupport_of_reverse G u hrev
    (w * t) (hx ▸ ht)

end

end Erdos85
