import Proofs.Erdos85QuotientGramIdentity
import Proofs.Erdos85MinimumSectorAssemblyArithmetic
import Proofs.Erdos85MinimumSectorAssemblyInterface
import Proofs.Erdos85UnitMinimumLayerTerminal
import Proofs.Erdos85DoubleCoverTargetUniqueness

/-!
# The large-prime sector capstone

At the exact even boundary `|V| = d(d-1) + 3 = N·p` with `p > d` prime
dividing every defect-component order, the minimum-layer cross-pair
identity, the leakage bound, and the assembly squeeze force a solitary
unit minimum — which dies on the diagonal collapse of the equal-size
excess — unless every component has the same order, which is the
equal-cycle boundary and forces `d ∈ {4, 12}`.

Hence for even `d ∉ {4, 12}` no such graph exists: the entire large-prime
sector of the exact boundary is closed, with no parity or convolution
input and no square/nonsquare split.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Larger components see the minimum layer at most once.**  For a
component `f` strictly larger than the minimum order, the quotient row
restricted to the minimum layer sums to at most one. -/
theorem secondOrder_largerComponent_minLayerRow_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (f : (secondOrderDefectGraph G).ConnectedComponent)
    (hflt : c₀.supp.ncard < f.supp.ncard) :
    (∑ e ∈ Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
          c.supp.ncard = c₀.supp.ncard),
      componentQuotientMatrix G (secondOrderDefectGraph G) f e) ≤ 1 := by
  classical
  have hreg : ∀ x : V, (secondOrderDefectGraph G).degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree hd heven hmin hcard
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard) with hM
  set Q := componentQuotientMatrix G (secondOrderDefectGraph G) with hQ
  have hmemSize : ∀ e ∈ M, e.supp.ncard = c₀.supp.ncard := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hmemMin : ∀ e ∈ M,
      ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard ≤ l.supp.ncard := by
    intro e he l
    rw [hmemSize e he]
    exact hc₀min l
  -- Positivity transfers across detailed balance.
  have htransfer : ∀ e ∈ M, 0 < Q f e → 0 < Q e f := by
    intro e he hpos
    have hbal := componentQuotientMatrix_balance
      G (secondOrderDefectGraph G) 2 hreg hcomm f e
    have hfpos : 0 < f.supp.ncard := f.nonempty_supp.ncard_pos
    by_contra h0
    have hzero : Q e f = 0 := by omega
    have hzero' : componentQuotientMatrix G
        (secondOrderDefectGraph G) e f = 0 := by
      simpa [hQ] using hzero
    rw [hzero', mul_zero] at hbal
    have : f.supp.ncard * componentQuotientMatrix G
        (secondOrderDefectGraph G) f e = 0 := hbal
    have hQpos : 0 < componentQuotientMatrix G
        (secondOrderDefectGraph G) f e := by
      simpa [hQ] using hpos
    exact absurd this (by positivity)
  -- Any positive entry equals one.
  have hval : ∀ e ∈ M, 0 < Q f e → Q f e = 1 := by
    intro e he hpos
    have helt : e.supp.ncard < f.supp.ncard := by
      rw [hmemSize e he]
      exact hflt
    have := secondOrder_minimumComponent_larger_reverseEntry_eq_one
      G hfree hd heven hmin hcard e f helt
        (by simpa [hQ] using htransfer e he hpos)
    simpa [hQ] using this
  -- At most one minimum-layer component has a positive entry.
  have huniq : ∀ e₁ ∈ M, ∀ e₂ ∈ M,
      0 < Q f e₁ → 0 < Q f e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ hp₁ hp₂
    have h₁lt : e₁.supp.ncard < f.supp.ncard := by
      rw [hmemSize e₁ he₁]; exact hflt
    exact secondOrder_minimum_largerTarget_source_unique
      G hfree hd heven hmin hcard e₁ e₂ f (hmemMin e₁ he₁)
        ((hmemSize e₂ he₂).trans (hmemSize e₁ he₁).symm) h₁lt
        (by simpa [hQ] using htransfer e₁ he₁ hp₁)
        (by simpa [hQ] using htransfer e₂ he₂ hp₂)
  -- Collapse the sum to the positive-entry subset.
  have hfilter : (∑ e ∈ M, Q f e) =
      ∑ e ∈ M.filter (fun e ↦ 0 < Q f e), Q f e := by
    symm
    apply Finset.sum_filter_of_ne
    intro e he hne
    omega
  have hcardP : (M.filter (fun e ↦ 0 < Q f e)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro e₁ he₁ e₂ he₂
    obtain ⟨he₁M, he₁pos⟩ := Finset.mem_filter.mp he₁
    obtain ⟨he₂M, he₂pos⟩ := Finset.mem_filter.mp he₂
    exact huniq e₁ he₁M e₂ he₂M he₁pos he₂pos
  rw [hfilter]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcardP with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
    omega
  · obtain ⟨ep, hep⟩ := Finset.card_eq_one.mp h1
    rw [hep, Finset.sum_singleton]
    have hepmem : ep ∈ M.filter (fun e ↦ 0 < Q f e) := by
      rw [hep]; exact Finset.mem_singleton_self ep
    obtain ⟨hepM, heppos⟩ := Finset.mem_filter.mp hepmem
    rw [hval ep hepM heppos]

/-- **Leakage bound.**  The minimum layer's total quotient mass toward
strictly larger components, scaled by the normalized minimum coefficient,
plus the minimum layer's own coefficient mass, is at most `N`. -/
theorem secondOrder_minLayer_leakage_add_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    (c₀.supp.ncard / p) *
        (∑ e ∈ Finset.univ.filter
            (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
              c.supp.ncard = c₀.supp.ncard),
          ∑ f ∈ Finset.univ \ Finset.univ.filter
            (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
              c.supp.ncard = c₀.supp.ncard),
            componentQuotientMatrix G (secondOrderDefectGraph G) e f) +
      (Finset.univ.filter
        (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
          c.supp.ncard = c₀.supp.ncard)).card * (c₀.supp.ncard / p) ≤
      N := by
  classical
  have hreg : ∀ x : V, (secondOrderDefectGraph G).degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree hd heven hmin hcard
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard) with hM
  set Q := componentQuotientMatrix G (secondOrderDefectGraph G) with hQ
  set a := c₀.supp.ncard / p with ha
  set m : (secondOrderDefectGraph G).ConnectedComponent → ℕ :=
    fun f ↦ f.supp.ncard / p with hm
  have hpPos : 0 < p := hp.pos
  have hsize : ∀ f : (secondOrderDefectGraph G).ConnectedComponent,
      f.supp.ncard = m f * p := by
    intro f
    rw [hm]
    rw [Nat.div_mul_cancel (hall f)]
  have hc₀size : c₀.supp.ncard = a * p := hsize c₀
  have hmemSize : ∀ e ∈ M, e.supp.ncard = c₀.supp.ncard := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hmemM : ∀ e ∈ M, m e = a := by
    intro e he
    show e.supp.ncard / p = c₀.supp.ncard / p
    rw [hmemSize e he]
  have hmemMin : ∀ e ∈ M,
      ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard ≤ l.supp.ncard := by
    intro e he l
    rw [hmemSize e he]
    exact hc₀min l
  -- Total coefficient mass is `N`.
  have hcoeffSum :
      (∑ f : (secondOrderDefectGraph G).ConnectedComponent, m f) = N := by
    have hsumSizes :
        (∑ f : (secondOrderDefectGraph G).ConnectedComponent,
          f.supp.ncard) = N * p := by
      rw [sum_connectedComponent_supp_ncard (secondOrderDefectGraph G),
        hcard]
      exact hboundary
    have hmul : (∑ f : (secondOrderDefectGraph G).ConnectedComponent,
        m f) * p = N * p := by
      calc
        (∑ f : (secondOrderDefectGraph G).ConnectedComponent, m f) * p =
            ∑ f : (secondOrderDefectGraph G).ConnectedComponent,
              m f * p := by rw [Finset.sum_mul]
        _ = ∑ f : (secondOrderDefectGraph G).ConnectedComponent,
              f.supp.ncard := by
            apply Finset.sum_congr rfl
            intro f _
            exact (hsize f).symm
        _ = N * p := hsumSizes
    exact Nat.eq_of_mul_eq_mul_right hpPos hmul
  -- Coefficient mass of the minimum layer.
  have hMcoeff : (∑ e ∈ M, m e) = M.card * a := by
    rw [Finset.sum_congr rfl hmemM, Finset.sum_const, smul_eq_mul]
  -- Per larger component, the scaled minimum-layer column sums to `≤ m f`.
  have hcol : ∀ f ∈ Finset.univ \ M,
      (∑ e ∈ M, a * Q e f) ≤ m f := by
    intro f hf
    have hfM : f ∉ M := (Finset.mem_sdiff.mp hf).2
    have hfne : f.supp.ncard ≠ c₀.supp.ncard := by
      intro h
      exact hfM (Finset.mem_filter.mpr ⟨Finset.mem_univ f, h⟩)
    have hflt : c₀.supp.ncard < f.supp.ncard :=
      lt_of_le_of_ne (hc₀min f) (Ne.symm hfne)
    have hval : ∀ e ∈ M, 0 < Q e f → a * Q e f = m f := by
      intro e he hpos
      have helt : e.supp.ncard < f.supp.ncard := by
        rw [hmemSize e he]
        exact hflt
      have hrev := secondOrder_minimumComponent_larger_reverseEntry_eq_one
        G hfree hd heven hmin hcard e f helt (by simpa [hQ] using hpos)
      have := componentQuotientMatrix_normalized_balance
        G (secondOrderDefectGraph G) 2 hreg hcomm e f p a (m f) hpPos
          (by rw [hmemSize e he]; exact hc₀size) (hsize f) hrev
      simpa [hQ] using this
    have huniq : ∀ e₁ ∈ M, ∀ e₂ ∈ M,
        0 < Q e₁ f → 0 < Q e₂ f → e₁ = e₂ := by
      intro e₁ he₁ e₂ he₂ hp₁ hp₂
      have h₁lt : e₁.supp.ncard < f.supp.ncard := by
        rw [hmemSize e₁ he₁]; exact hflt
      exact secondOrder_minimum_largerTarget_source_unique
        G hfree hd heven hmin hcard e₁ e₂ f (hmemMin e₁ he₁)
          ((hmemSize e₂ he₂).trans (hmemSize e₁ he₁).symm) h₁lt
          (by simpa [hQ] using hp₁) (by simpa [hQ] using hp₂)
    have hfilter : (∑ e ∈ M, a * Q e f) =
        ∑ e ∈ M.filter (fun e ↦ 0 < Q e f), a * Q e f := by
      symm
      apply Finset.sum_filter_of_ne
      intro e he hne
      by_contra h0
      have : Q e f = 0 := by omega
      apply hne
      rw [this, mul_zero]
    have hcardP : (M.filter (fun e ↦ 0 < Q e f)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro e₁ he₁ e₂ he₂
      obtain ⟨he₁M, he₁pos⟩ := Finset.mem_filter.mp he₁
      obtain ⟨he₂M, he₂pos⟩ := Finset.mem_filter.mp he₂
      exact huniq e₁ he₁M e₂ he₂M he₁pos he₂pos
    rw [hfilter]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcardP with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]
      exact Nat.zero_le _
    · obtain ⟨ep, hep⟩ := Finset.card_eq_one.mp h1
      rw [hep, Finset.sum_singleton]
      have hepmem : ep ∈ M.filter (fun e ↦ 0 < Q e f) := by
        rw [hep]; exact Finset.mem_singleton_self ep
      obtain ⟨hepM, heppos⟩ := Finset.mem_filter.mp hepmem
      rw [hval ep hepM heppos]
  -- Assemble.
  have hswap : a * (∑ e ∈ M, ∑ f ∈ Finset.univ \ M, Q e f) =
      ∑ f ∈ Finset.univ \ M, ∑ e ∈ M, a * Q e f := by
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.mul_sum]
  calc
    a * (∑ e ∈ M, ∑ f ∈ Finset.univ \ M, Q e f) + M.card * a =
        (∑ f ∈ Finset.univ \ M, ∑ e ∈ M, a * Q e f) + M.card * a := by
      rw [hswap]
    _ ≤ (∑ f ∈ Finset.univ \ M, m f) + M.card * a := by
      exact Nat.add_le_add_right (Finset.sum_le_sum hcol) _
    _ = (∑ f ∈ Finset.univ \ M, m f) + ∑ e ∈ M, m e := by rw [hMcoeff]
    _ = ∑ f : (secondOrderDefectGraph G).ConnectedComponent, m f :=
      Finset.sum_sdiff (Finset.subset_univ M)
    _ = N := hcoeffSum

/-- **The large-prime sector is empty.**  No `C4`-free graph of even
minimum degree `d ∉ {4, 12}` exists at the exact boundary
`d(d-1) + 3 = N·p` when a prime `p > d` divides every second-order defect
component order. -/
theorem false_of_secondOrder_largePrime_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hdp : d < p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard)
    (hd4 : d ≠ 4) (hd12 : d ≠ 12) : False := by
  classical
  -- A minimum component exists.
  have hVpos : 0 < Fintype.card V := by
    rw [hcard]
    positivity
  have hVne : Nonempty V := Fintype.card_pos_iff.mp hVpos
  obtain ⟨v₀⟩ := hVne
  obtain ⟨c₀, -, hc₀min'⟩ := Finset.exists_min_image
    (Finset.univ :
      Finset (secondOrderDefectGraph G).ConnectedComponent)
    (fun c ↦ c.supp.ncard)
    ⟨(secondOrderDefectGraph G).connectedComponentMk v₀,
      Finset.mem_univ _⟩
  have hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard :=
    fun e ↦ hc₀min' e (Finset.mem_univ e)
  -- All-equal orders is the equal-cycle boundary.
  by_cases hallEq : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
    e.supp.ncard = c₀.supp.ncard
  · rcases equalCycle_degree_eq_four_or_twelve G hfree hd heven hmin
        hcard hallEq with h4 | h12
    · exact hd4 h4
    · exact hd12 h12
  -- Otherwise a strictly larger component exists.
  push Not at hallEq
  obtain ⟨f₀, hf₀ne⟩ := hallEq
  set M : Finset (secondOrderDefectGraph G).ConnectedComponent :=
    Finset.univ.filter
      (fun c ↦ c.supp.ncard = c₀.supp.ncard) with hM
  set QM := componentQuotientMatrix G (secondOrderDefectGraph G) with hQM
  have hpPos : 0 < p := hp.pos
  set a := c₀.supp.ncard / p with ha
  have hc₀size : c₀.supp.ncard = a * p := by
    rw [ha, Nat.div_mul_cancel (hall c₀)]
  have haPos : 1 ≤ a := by
    have hcPos : 0 < c₀.supp.ncard := c₀.nonempty_supp.ncard_pos
    have := Nat.le_of_dvd hcPos (hall c₀)
    rw [ha]
    exact Nat.div_pos this hpPos
  have hc₀M : c₀ ∈ M := by
    rw [hM]
    simp
  have huPos : 1 ≤ M.card := Finset.card_pos.mpr ⟨c₀, hc₀M⟩
  have hmemSize : ∀ e ∈ M, e.supp.ncard = c₀.supp.ncard := by
    intro e he
    exact (Finset.mem_filter.mp he).2
  have hmemMin : ∀ e ∈ M,
      ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard ≤ l.supp.ncard := by
    intro e he l
    rw [hmemSize e he]
    exact hc₀min l
  have hnotM : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ∉ M → c₀.supp.ncard < e.supp.ncard := by
    intro e he
    have : e.supp.ncard ≠ c₀.supp.ncard := by
      intro h
      exact he (by rw [hM]; simp [h])
    exact lt_of_le_of_ne (hc₀min e) (Ne.symm this)
  -- Integer row pieces.
  set S : (secondOrderDefectGraph G).ConnectedComponent → ℤ :=
    fun e ↦ ∑ c ∈ M, (QM e c : ℤ) with hS
  set L : (secondOrderDefectGraph G).ConnectedComponent → ℤ :=
    fun e ↦ ∑ f ∈ Finset.univ \ M, (QM e f : ℤ) with hL
  have hLnonneg : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      0 ≤ L e := by
    intro e
    rw [hL]
    positivity
  have hSnonneg : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      0 ≤ S e := by
    intro e
    rw [hS]
    positivity
  -- Row split: `S e + L e = d`.
  have hrowSplit : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      S e + L e = (d : ℤ) := by
    intro e
    have hrow := sum_secondOrder_componentQuotientMatrix_row_eq_degree
      G hfree hd heven hmin hcard e
    rw [← hQM] at hrow
    have hsplit : (∑ f ∈ Finset.univ \ M, QM e f) + ∑ c ∈ M, QM e c =
        ∑ c : (secondOrderDefectGraph G).ConnectedComponent, QM e c :=
      Finset.sum_sdiff (Finset.subset_univ M)
    rw [hrow] at hsplit
    have hcast : (((∑ f ∈ Finset.univ \ M, QM e f) +
        ∑ c ∈ M, QM e c : ℕ) : ℤ) = (d : ℤ) := by
      exact_mod_cast hsplit
    push_cast at hcast
    rw [hS, hL]
    linarith
  -- The equal-size excess identity on each minimum-layer component.
  have hsqE : ∀ e ∈ M,
      (∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) =
        ((c₀.supp.ncard : ℤ) - 3) + S e := by
    intro e he
    have hex := secondOrder_minimumComponent_equalSize_excess
      G hfree hd heven hmin hcard e (hmemMin e he)
    rw [← hQM] at hex
    have hcond : ∀ e' : (secondOrderDefectGraph G).ConnectedComponent,
        (e'.supp.ncard = e.supp.ncard) =
          (e'.supp.ncard = c₀.supp.ncard) := by
      intro e'
      rw [hmemSize e he]
    simp only [hcond, hmemSize e he] at hex
    have hfold :
        (∑ e' : (secondOrderDefectGraph G).ConnectedComponent,
          if e'.supp.ncard = c₀.supp.ncard then
            (QM e e' : ℤ) * ((QM e e' : ℤ) - 1) else 0) =
          ∑ c ∈ M, (QM e c : ℤ) * ((QM e c : ℤ) - 1) := by
      simp only [hM, Finset.sum_filter]
    rw [hfold] at hex
    have hexpand : (∑ c ∈ M, (QM e c : ℤ) * ((QM e c : ℤ) - 1)) =
        (∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) - S e := by
      rw [hS, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hexpand] at hex
    linarith
  -- Larger components contribute nothing to the pair sum.
  have hbracket0 : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ∉ M → S e * S e - (∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) = 0 := by
    intro e he
    have hlt := hnotM e he
    have hrow := secondOrder_largerComponent_minLayerRow_le_one
      G hfree hd heven hmin hcard c₀ hc₀min e hlt
    rw [← hQM, ← hM] at hrow
    have hSle : S e ≤ 1 := by
      simp only [hS]
      exact_mod_cast hrow
    have hentry : ∀ c ∈ M, QM e c ≤ 1 := by
      intro c hc
      calc
        QM e c ≤ ∑ c' ∈ M, QM e c' :=
          Finset.single_le_sum (fun c' _ ↦ Nat.zero_le _) hc
        _ ≤ 1 := hrow
    have hsq : (∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) = S e := by
      rw [hS]
      apply Finset.sum_congr rfl
      intro c hc
      have hle := hentry c hc
      have h01 : QM e c = 0 ∨ QM e c = 1 := by omega
      rcases h01 with h | h <;> rw [h] <;> norm_num
    rw [hsq]
    have hS0 : 0 ≤ S e := hSnonneg e
    have : S e = 0 ∨ S e = 1 := by omega
    rcases this with h | h <;> rw [h] <;> ring
  -- The Gram identity summed over ordered distinct minimum pairs.
  have hGramPair : ∀ c ∈ M, ∀ c' ∈ M.erase c,
      (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
        (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
        (c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ) := by
    intro c hc c' hc'
    have hne : c ≠ c' := (Finset.ne_of_mem_erase hc').symm
    have hnat := sum_ncard_mul_componentQuotient_eq_of_ne
      G hfree hd heven hmin hcard c c' hne
    rw [← hQM] at hnat
    rw [hmemSize c hc, hmemSize c' (Finset.mem_of_mem_erase hc')] at hnat
    calc
      (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
          ((∑ e : (secondOrderDefectGraph G).ConnectedComponent,
            e.supp.ncard * (QM e c * QM e c') : ℕ) : ℤ) := by
        push_cast
        rfl
      _ = ((c₀.supp.ncard * c₀.supp.ncard : ℕ) : ℤ) := by
        exact_mod_cast hnat
      _ = (c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ) := by push_cast; ring
  -- Total over ordered pairs.
  have hpairTotal :
      (∑ c ∈ M, ∑ c' ∈ M.erase c,
        ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
        (M.card : ℤ) * ((M.card : ℤ) - 1) *
          ((c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ)) := by
    calc
      (∑ c ∈ M, ∑ c' ∈ M.erase c,
          ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
            (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
          ∑ c ∈ M, ∑ c' ∈ M.erase c,
            (c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact Finset.sum_congr rfl (fun c' hc' ↦ hGramPair c hc c' hc')
      _ = ∑ c ∈ M, ((M.erase c).card : ℤ) *
            ((c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ)) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_const, nsmul_eq_mul]
      _ = ∑ c ∈ M, ((M.card : ℤ) - 1) *
            ((c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ)) := by
        apply Finset.sum_congr rfl
        intro c hc
        congr 1
        rw [Finset.card_erase_of_mem hc]
        have : 1 ≤ M.card := huPos
        push_cast [Nat.cast_sub this]
        ring
      _ = (M.card : ℤ) * ((M.card : ℤ) - 1) *
            ((c₀.supp.ncard : ℤ) * (c₀.supp.ncard : ℤ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  -- Swap the summation order and evaluate componentwise.
  have hswapPair :
      (∑ c ∈ M, ∑ c' ∈ M.erase c,
        ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
        ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          (e.supp.ncard : ℤ) *
            (S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) := by
    calc
      (∑ c ∈ M, ∑ c' ∈ M.erase c,
          ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
            (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
          ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
            ∑ c ∈ M, ∑ c' ∈ M.erase c,
              (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_comm]
      _ = ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
            (e.supp.ncard : ℤ) *
              (S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) := by
        apply Finset.sum_congr rfl
        intro e _
        have hinner : (∑ c ∈ M, ∑ c' ∈ M.erase c,
            (QM e c : ℤ) * (QM e c' : ℤ)) =
              S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ) := by
          calc
            (∑ c ∈ M, ∑ c' ∈ M.erase c,
                (QM e c : ℤ) * (QM e c' : ℤ)) =
                ∑ c ∈ M, (QM e c : ℤ) * (S e - (QM e c : ℤ)) := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hc]
            _ = (∑ c ∈ M, (QM e c : ℤ) * S e) -
                  ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro c _
              ring
            _ = S e * S e -
                  ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ) := by
              congr 1
              rw [← Finset.sum_mul]
        calc
          (∑ c ∈ M, ∑ c' ∈ M.erase c,
              (e.supp.ncard : ℤ) * ((QM e c : ℤ) * (QM e c' : ℤ))) =
              (e.supp.ncard : ℤ) * ∑ c ∈ M, ∑ c' ∈ M.erase c,
                (QM e c : ℤ) * (QM e c' : ℤ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.mul_sum]
          _ = (e.supp.ncard : ℤ) *
                (S e * S e -
                  ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) := by
            rw [hinner]
  -- Only minimum-layer components survive; divide by the common order.
  have hidentityRaw :
      (∑ e ∈ M, ((( d : ℤ) - L e) * ((d : ℤ) - L e) - ((d : ℤ) - L e) -
          ((c₀.supp.ncard : ℤ) - 3))) =
        (M.card : ℤ) * ((M.card : ℤ) - 1) * (c₀.supp.ncard : ℤ) := by
    have hcombined := hswapPair.symm.trans hpairTotal
    have hsplitE :
        (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          (e.supp.ncard : ℤ) *
            (S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ))) =
          ∑ e ∈ M, (e.supp.ncard : ℤ) *
            (S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ)) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ M)]
      have hzero :
          (∑ e ∈ Finset.univ \ M, (e.supp.ncard : ℤ) *
            (S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ))) = 0 := by
        apply Finset.sum_eq_zero
        intro e he
        rw [hbracket0 e (Finset.mem_sdiff.mp he).2, mul_zero]
      rw [hzero, zero_add]
    have hMeval :
        (∑ e ∈ M, (e.supp.ncard : ℤ) *
          (S e * S e - ∑ c ∈ M, (QM e c : ℤ) * (QM e c : ℤ))) =
          (c₀.supp.ncard : ℤ) *
            ∑ e ∈ M, (((d : ℤ) - L e) * ((d : ℤ) - L e) -
              ((d : ℤ) - L e) - ((c₀.supp.ncard : ℤ) - 3)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hSe : S e = (d : ℤ) - L e := by
        have := hrowSplit e
        linarith
      rw [hmemSize e he, hsqE e he, hSe]
      ring
    rw [hsplitE, hMeval] at hcombined
    have hwpos : (0 : ℤ) < (c₀.supp.ncard : ℤ) := by
      exact_mod_cast c₀.nonempty_supp.ncard_pos
    have hfactored :
        (c₀.supp.ncard : ℤ) *
          (∑ e ∈ M, (((d : ℤ) - L e) * ((d : ℤ) - L e) -
            ((d : ℤ) - L e) - ((c₀.supp.ncard : ℤ) - 3))) =
          (c₀.supp.ncard : ℤ) *
            ((M.card : ℤ) * ((M.card : ℤ) - 1) * (c₀.supp.ncard : ℤ)) := by
      rw [hcombined]
      ring
    exact mul_left_cancel₀ (ne_of_gt hwpos) hfactored
  -- Leakage bound, cast to the integers.
  have hleakNat := secondOrder_minLayer_leakage_add_le
    G hfree hd heven hmin hcard hp hboundary hall c₀ hc₀min
  rw [← hQM, ← hM, ← ha] at hleakNat
  -- Strictness: a strictly larger component carries coefficient mass.
  have hstrictNat : M.card * a < N := by
    set m : (secondOrderDefectGraph G).ConnectedComponent → ℕ :=
      fun f ↦ f.supp.ncard / p with hm
    have hsize : ∀ f : (secondOrderDefectGraph G).ConnectedComponent,
        f.supp.ncard = m f * p := by
      intro f
      rw [hm]
      rw [Nat.div_mul_cancel (hall f)]
    have hcoeffSum :
        (∑ f : (secondOrderDefectGraph G).ConnectedComponent, m f) =
          N := by
      have hsumSizes :
          (∑ f : (secondOrderDefectGraph G).ConnectedComponent,
            f.supp.ncard) = N * p := by
        rw [sum_connectedComponent_supp_ncard (secondOrderDefectGraph G),
          hcard]
        exact hboundary
      have hmul : (∑ f : (secondOrderDefectGraph G).ConnectedComponent,
          m f) * p = N * p := by
        calc
          (∑ f : (secondOrderDefectGraph G).ConnectedComponent, m f) *
              p = ∑ f : (secondOrderDefectGraph G).ConnectedComponent,
                m f * p := by rw [Finset.sum_mul]
          _ = ∑ f : (secondOrderDefectGraph G).ConnectedComponent,
                f.supp.ncard := by
              apply Finset.sum_congr rfl
              intro f _
              exact (hsize f).symm
          _ = N * p := hsumSizes
      exact Nat.eq_of_mul_eq_mul_right hpPos hmul
    have hf₀M : f₀ ∉ M := by
      intro h
      exact hf₀ne (hmemSize f₀ h)
    have hf₀m : 1 ≤ m f₀ := by
      have hpos : 0 < f₀.supp.ncard := f₀.nonempty_supp.ncard_pos
      have := Nat.le_of_dvd hpos (hall f₀)
      rw [hm]
      exact Nat.div_pos this hpPos
    have hMcoeff : (∑ e ∈ M, m e) = M.card * a := by
      have : ∀ e ∈ M, m e = a := by
        intro e he
        show e.supp.ncard / p = c₀.supp.ncard / p
        rw [hmemSize e he]
      rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
    have hsplitCoeff :
        (∑ f ∈ Finset.univ \ M, m f) + ∑ e ∈ M, m e =
          ∑ f : (secondOrderDefectGraph G).ConnectedComponent, m f :=
      Finset.sum_sdiff (Finset.subset_univ M)
    have hout : 1 ≤ ∑ f ∈ Finset.univ \ M, m f := by
      calc
        1 ≤ m f₀ := hf₀m
        _ ≤ ∑ f ∈ Finset.univ \ M, m f :=
          Finset.single_le_sum (fun f _ ↦ Nat.zero_le _)
            (Finset.mem_sdiff.mpr ⟨Finset.mem_univ f₀, hf₀M⟩)
    omega
  -- Assembly squeeze forces a solitary unit minimum.
  have hsq := minimum_sector_assembly_squeeze
    (s := M) (L := L) (T := 0) (d := (d : ℤ)) (p := (p : ℤ))
    (N := (N : ℤ)) (a := (a : ℤ))
    (by exact_mod_cast huPos)
    (by exact_mod_cast haPos)
    (by exact_mod_cast hd)
    (by exact_mod_cast hdp)
    (fun c _ ↦ hLnonneg c)
    (by
      have h1 : 1 ≤ d := by omega
      have hZ : ((d * (d - 1) + 3 : ℕ) : ℤ) = ((N * p : ℕ) : ℤ) := by
        exact_mod_cast hboundary
      push_cast [Nat.cast_sub h1] at hZ
      linear_combination hZ)
    (by
      rw [add_zero]
      have hw : (c₀.supp.ncard : ℤ) = (a : ℤ) * (p : ℤ) := by
        exact_mod_cast hc₀size
      rw [← hw]
      exact hidentityRaw)
    le_rfl
    (by
      have hcast : ((a * (∑ e ∈ M, ∑ f ∈ Finset.univ \ M, QM e f) +
          M.card * a : ℕ) : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast hleakNat
      have hLsum : (∑ c ∈ M, L c) =
          ((∑ e ∈ M, ∑ f ∈ Finset.univ \ M, QM e f : ℕ) : ℤ) := by
        simp only [hL]
        push_cast
        rfl
      rw [hLsum]
      push_cast at hcast ⊢
      linarith)
    (by exact_mod_cast hstrictNat)
  obtain ⟨huEq, haEq⟩ := hsq
  have huEqN : M.card = 1 := by exact_mod_cast huEq
  have haEqN : a = 1 := by exact_mod_cast haEq
  -- The solitary unit minimum dies on the diagonal collapse.
  have hd6 : 6 ≤ d := by
    rcases heven with ⟨k, hk⟩
    omega
  have hp7 : 7 ≤ p := by omega
  have hpOdd : Odd p := hp.odd_of_ne_two (by omega)
  have hc₀p : c₀.supp.ncard = p := by
    rw [hc₀size, haEqN, one_mul]
  exact false_of_secondOrder_lone_unit_minimum
    G hfree hd heven hmin hcard hp7 hpOdd c₀ hc₀min hc₀p
    (by rw [← hM]; omega)

end

end Erdos85
